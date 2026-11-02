import InitECandidate.Solver.Wave8GuestInv.R11Shards.EvmBase

/-! Proofs of `ek_refill_frame_state_gas`, `ek_frame_halt`, and `frame_exception_spec` on R11. -/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R11Shards

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

/-! ## 1. Exact R11 contract vocabulary (pre-`C00`) -/

def FunSpecR11 (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → Prop)
    (fname : MlS) : Prop :=
  ∃ (params : List (MlS × ShapeHOL)) (body : ProgHOL 64) (retShape : ShapeHOL),
    originalRuntimeCode.lookup fname = some (params, body, retShape) ∧
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode → P s →
      (∃ values, lookupCodeHOLFinite originalRuntimeCode.lookup fname values =
        some (body, s.locals, retShape)) →
      (evaluateHOLFiniteState s body).1 ≠ some .timeOut →
      Q s (evaluateHOLFiniteState s body).1 (evaluateHOLFiniteState s body).2

def OnReturnR11 (Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F → Prop) :
    ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → Prop :=
  fun s r post => ∀ v, r = some (.returned v) → Q s post

def ResumesR11 (r : Option (PanSemResultExact 64)) : Prop :=
  (∃ v, r = some (.returned v)) ∨ ∃ e v, r = some (.exception e v) ∧ e ≠ ofString "TrapErr"

def GlobalsKeptR11 (gw : List String) {F : Type} (s post : PanSemStateFiniteExact 64 F) : Prop :=
  ∀ k : MlS, k ∉ gw.map ofString → s.globals.lookup k = post.globals.lookup k

def EvmStepR11 (gw : List String) :
    ∀ {F : Type}, PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F → Prop :=
  fun s post => EvmInv post ∧ globN s "heap_ptr" ≤ globN post "heap_ptr" ∧ GlobalsKeptR11 gw s post ∧
    evmChain post = evmChain s

def EvmKeepsR11 (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop) (gw : List String)
    (fname : MlS) : Prop :=
  FunSpecR11 P (fun s r post => ResumesR11 r → EvmStepR11 gw s post) fname

def evmRR11 {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat :=
  ((evmChain s).map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)).sum

theorem not_resumes_err : ¬ ResumesR11 (some (.error : PanSemResultExact 64)) := by
  rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> cases h

/-! ## 2. Lookup & parameter-shape helpers -/

theorem lookup_refill_frame_state_gas :
    originalRuntimeCode.lookup (ofString "refill_frame_state_gas") =
      some ([], sourceFnBody Guest.Software.guestFn_refill_frame_state_gas, .one) :=
  lookup_of_guestAst_getElem 452 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_refill_frame_state_gas) rfl

theorem lookup_frame_halt :
    originalRuntimeCode.lookup (ofString "frame_halt") =
      some ([(ofString "err", .one)], sourceFnBody Guest.Software.guestFn_frame_halt, .one) :=
  lookup_of_guestAst_getElem 586 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_frame_halt) rfl

theorem lookup_frame_exception :
    originalRuntimeCode.lookup (ofString "frame_exception") =
      some ([(ofString "err", .one)], sourceFnBody Guest.Software.guestFn_frame_exception, .one) :=
  lookup_of_guestAst_getElem 579 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_frame_exception) rfl

theorem one_word_param_of_lookup {fname param : MlS} {body : ProgHOL 64}
    {locals : HolFiniteMapExact MlS (ValueHOL 64)}
    (hlook : originalRuntimeCode.lookup fname = some ([(param, .one)], body, .one))
    (hex : ∃ values, lookupCodeHOLFinite originalRuntimeCode.lookup fname values =
      some (body, locals, .one)) :
    ∃ w : BitVec 64, locals.lookup param = some (.val (.word w)) := by
  obtain ⟨values, hl⟩ := hex
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hl
  split at hl
  · cases hl
  · rename_i exactBody exactLocals exactShape raw
    have heq := Option.some.inj hl
    rcases Prod.mk.inj heq with ⟨rfl, hrest⟩
    rcases Prod.mk.inj hrest with ⟨rfl, _⟩
    unfold lookupCodeHOLExact at raw
    rw [hlook] at raw
    dsimp only at raw
    split at raw
    · rename_i hcond
      have rawEq := Option.some.inj raw
      rcases Prod.mk.inj rawEq with ⟨_, hrest2⟩
      rcases Prod.mk.inj hrest2 with ⟨hloc, _⟩
      subst hloc
      rcases values with _ | ⟨v0, _ | _⟩
      · simp at hcond
      · have hsh : shapeEqHOL .one (shapeOfHOLExact v0) = true := by
          simpa [List.map] using hcond
        rcases v0 with ⟨⟨w⟩⟩ | fs | ⟨nm, fs⟩
        · exact ⟨w, by simp⟩
        · simp [shapeOfHOLExact, shapeEqHOL] at hsh
        · simp [shapeOfHOLExact, shapeEqHOL] at hsh
      · simp at hcond
    · cases raw

theorem store_res_not_resumes {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {dst val : ExpHOL 64} {res : PanSemResultExact 64}
    (h : evaluateHOLFiniteState s (.store dst val) = (some res, post)) :
    ¬ ResumesR11 (some res) := by
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
  exact not_resumes_err

def updW (m : BitVec 64 → HolWordLab 64) (a w : BitVec 64) : BitVec 64 → HolWordLab 64 :=
  fun x => if x = a then .word w else m x

theorem store_global_off_word {F : Type} {t post : PanSemStateFiniteExact 64 F}
    {gname : String} {gbase off : Nat} {gw : BitVec 64} {valExp : ExpHOL 64}
    (hg_lk : t.globals.lookup (ofString gname) = some (.val (.word gw)))
    (hg_nat : gw.toNat = gbase)
    (hbnd : gbase + off < 2 ^ 64)
    (hval : ∀ v : ValueHOL 64,
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) valExp = some v →
      ∃ w : BitVec 64, v = .val (.word w))
    (hrun : evaluateHOLFiniteState t
      (.store (.op .add [.var .global (ofString gname), .const (BitVec.ofNat 64 off)]) valExp) =
      (none, post)) :
    ∃ w : BitVec 64,
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) valExp =
        some (.val (.word w)) ∧
      post = { t with memory := updW t.memory (BitVec.ofNat 64 (gbase + off)) w } := by
  have hdst : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
      (.op .add [.var .global (ofString gname), .const (BitVec.ofNat 64 off)]) =
      some (.val (.word (BitVec.ofNat 64 (gbase + off)))) := by
    simp only [evalHOLExact, evalListHOLExact, hg_lk, wordOpHOL, wordOp, valueIsWord, valueWord,
      List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr, BitVec.add_zero]
    congr 3
    apply BitVec.eq_of_toNat_eq
    have hz0 : (0 : BitVec 64).toNat = 0 := rfl
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hg_nat, hz0, Nat.add_zero,
      Nat.mod_eq_of_lt (show off < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt hbnd]
  rw [evaluateHOLFiniteState_store, hdst] at hrun
  revert hrun
  cases hv : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) valExp with
  | none => simp
  | some v =>
    obtain ⟨w, rfl⟩ := hval v hv
    dsimp only
    split
    · rename_i m' hst
      unfold flattenHOL panMemStoresHOL panMemStoreHOL at hst
      by_cases hdom : t.memaddrs (BitVec.ofNat 64 (gbase + off))
      · simp only [hdom, ↓reduceIte, panMemStoresHOL, Option.some.injEq] at hst
        subst hst
        intro hrun; injection hrun with _ hpost
        exact ⟨w, rfl, hpost.symm⟩
      · simp [hdom] at hst
    · simp

theorem memW_updW_same {F : Type} (t : PanSemStateFiniteExact 64 F) (a : Nat) (w : BitVec 64) :
    memW { t with memory := updW t.memory (BitVec.ofNat 64 a) w } a = w.toNat := by
  unfold memW updW; simp

theorem memW_updW_ne {F : Type} (t : PanSemStateFiniteExact 64 F) (a b : Nat) (w : BitVec 64)
    (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (hne : b ≠ a) :
    memW { t with memory := updW t.memory (BitVec.ofNat 64 a) w } b = memW t b := by
  unfold memW updW
  have hbv : BitVec.ofNat 64 b ≠ BitVec.ofNat 64 a := by
    intro heq
    have := congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt ha] at this
    exact hne this
  simp [hbv]

theorem evm_head_globals {F : Type} {s : PanSemStateFiniteExact 64 F} (hE : EvmInv s) :
    globN s "ev" + 280 < 2 ^ 64 ∧ globN s "cur_cont" + 104 < 2 ^ 64 ∧
    (∃ evw : BitVec 64, s.globals.lookup (ofString "ev") = some (.val (.word evw)) ∧ evw.toNat = globN s "ev") ∧
    (∃ ccw : BitVec 64, s.globals.lookup (ofString "cur_cont") = some (.val (.word ccw)) ∧ ccw.toNat = globN s "cur_cont") ∧
    memW s (globN s "ev" + 64) + memW s (globN s "ev" + 192) + 1 < 2 ^ 64 := by
  obtain ⟨hAR, S, _, hch_ne, _, _, hFWF, _, _, _, _, _, _, _, hGas⟩ := hE
  have hch_cons : ∃ tl, evmChain s = (globN s "ev", globN s "cur_cont") :: tl := by
    unfold evmChain; rw [show maxChain + 1 = 16384 + 1 from rfl, evmChainFrom]
    exact ⟨_, rfl⟩
  obtain ⟨tl, hch⟩ := hch_cons
  have hhead : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by rw [hch]; exact List.mem_cons_self
  have hF0 := hFWF _ hhead
  have he_in := (hF0.1 (globN s "ev", 280) (by simp)).1
  have hc_in := (hF0.1 (globN s "cur_cont", 104) (by simp)).1
  have h1 := hAR.2.2.2.1; have h2 := hAR.2.2.2.2.1
  rw [scratchStart_val] at h1
  have he_lt : globN s "ev" + 280 < 2 ^ 64 := by have := he_in.2; rw [scratchEnd_val] at this; omega
  have hc_lt : globN s "cur_cont" + 104 < 2 ^ 64 := by have := hc_in.2; rw [scratchEnd_val] at this; omega
  have he_pos : 0 < globN s "ev" := by have := he_in.1; dsimp only at this; omega
  have hc_pos : 0 < globN s "cur_cont" := by have := hc_in.1; dsimp only at this; omega
  have hevw : ∃ evw : BitVec 64, s.globals.lookup (ofString "ev") = some (.val (.word evw)) ∧ evw.toNat = globN s "ev" := by
    unfold globN at he_pos ⊢; split at he_pos <;> [exact ⟨_, ‹_›, rfl⟩; omega]
  have hccw : ∃ ccw : BitVec 64, s.globals.lookup (ofString "cur_cont") = some (.val (.word ccw)) ∧ ccw.toNat = globN s "cur_cont" := by
    unfold globN at hc_pos ⊢; split at hc_pos <;> [exact ⟨_, ‹_›, rfl⟩; omega]
  have hgas0 : memW s (globN s "ev" + 64) + memW s (globN s "ev" + 192) + 1 < 2 ^ 64 := by
    rw [hch, List.map_cons, List.sum_cons] at hGas; dsimp only at hGas; omega
  exact ⟨he_lt, hc_lt, hevw, hccw, hgas0⟩

/-! ## 3. Exact execution of `refill_frame_state_gas` on an `EvmInv` state -/

theorem refill_body_eq :
    sourceFnBody Guest.Software.guestFn_refill_frame_state_gas =
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

theorem refill_exec_step {F : Type} {s : PanSemStateFiniteExact 64 F} (hInv : EvmInv s)
    (hres : ResumesR11 (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_refill_frame_state_gas)).1) :
    let post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_refill_frame_state_gas)).2
    EvmInv post ∧ post.globals = s.globals ∧ evmChain post = evmChain s ∧ evmRR11 post ≤ evmRR11 s := by
  dsimp only
  obtain ⟨he_lt, _, ⟨evw, hevw_lk, hevw_nat⟩, _, hgas_sum⟩ := evm_head_globals hInv
  have hInv0 := hInv
  obtain ⟨hAR, S, _, _, _, _, hFWF, _⟩ := hInv0
  have hhead : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by simp [evmChain, evmChainFrom]
  have hrec_w := ((hFWF _ hhead).1 (globN s "ev", 280) (by simp)).2
  rw [refill_body_eq, evaluateHOLFiniteState_dec_total] at hres ⊢
  dsimp only at hres ⊢
  revert hres
  rcases hmsg_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.load .one (.op .add [.var .global (ofString "ev"), .const 112])) with _ | msgVal
  · dsimp only; intro hres; exact absurd hres not_resumes_err
  · dsimp only
    by_cases hsh_msg : shapeEqHOL .one (shapeOfHOLExact msgVal) = true
    · rw [if_pos hsh_msg]; dsimp only; intro hres
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
      change (let post := { (evaluateHOLFiniteState s0 body0).2 with
        locals := (evaluateHOLFiniteState s0 body0).2.locals.resVarEq
          (ofString "msg", s.locals.lookup (ofString "msg")) };
        EvmInv post ∧ post.globals = s.globals ∧ evmChain post = evmChain s ∧ evmRR11 post ≤ evmRR11 s)
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
        · obtain ⟨w1, hw1_ev, hs1_eq⟩ := store_global_off_word (t := s0) (post := s1)
            (gname := "ev") (gbase := globN s "ev") (off := 64) hevw_lk hevw_nat (by omega)
            (fun v hv => by
              simp only [evalHOLExact, wordOpHOL] at hv
              revert hv
              rcases @evalListHOLExact 64 F _ s0.toExact (fun a => Classical.propDecidable (s0.memaddrs a)) _ with _ | vs
              · simp
              · dsimp only; split
                · simp only [Option.map]
                  rcases wordOp .add (vs.map valueWord) with _ | w
                  · simp
                  · intro hv; injection hv with hv'; exact ⟨w, hv'.symm⟩
                · simp) h1
          have hw1_sum : w1.toNat = memW s (globN s "ev" + 64) + memW s (globN s "ev" + 192) := by
            obtain ⟨wg, hdom64, hmem64⟩ := hrec_w.2.2 8 (by omega)
            obtain ⟨wsp, hdom192, hmem192⟩ := hrec_w.2.2 24 (by omega)
            have h64_eq : globN s "ev" + 8 * 8 = globN s "ev" + 64 := by omega
            have h192_eq : globN s "ev" + 8 * 24 = globN s "ev" + 192 := by omega
            rw [h64_eq] at hdom64 hmem64; rw [h192_eq] at hdom192 hmem192
            have had64 : evw + (64 + 0) = BitVec.ofNat 64 (globN s "ev" + 64) := by
              apply BitVec.eq_of_toNat_eq
              have hz0 : (0 : BitVec 64).toNat = 0 := rfl
              have h64n : (64 : BitVec 64).toNat = 64 := rfl
              simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hevw_nat, hz0, h64n, Nat.add_zero,
                Nat.mod_eq_of_lt (show 64 < 2 ^ 64 by omega), Nat.mod_eq_of_lt (by omega)]
            have had192 : evw + (192 + 0) = BitVec.ofNat 64 (globN s "ev" + 192) := by
              apply BitVec.eq_of_toNat_eq
              have hz0 : (0 : BitVec 64).toNat = 0 := rfl
              have h192n : (192 : BitVec 64).toNat = 192 := rfl
              simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hevw_nat, hz0, h192n, Nat.add_zero,
                Nat.mod_eq_of_lt (show 192 < 2 ^ 64 by omega), Nat.mod_eq_of_lt (by omega)]
            have hsum_ev : @evalHOLExact 64 F _ s0.toExact (fun a => Classical.propDecidable (s0.memaddrs a))
                (.op .add
                  [.load .one (.op .add [.var .global (ofString "ev"), .const 64]),
                   .load .one (.op .add [.var .global (ofString "ev"), .const 192])]) =
                some (.val (.word (wg + (wsp + 0)))) := by
              have hml64 : @memLoadHOLExact 64 _ .one (BitVec.ofNat 64 (globN s "ev" + 64))
                  s0.memaddrs (fun a => Classical.propDecidable (s0.memaddrs a))
                  s0.memory s0.structs = some (.val (.word wg)) := by
                have hd0 : s0.memaddrs (BitVec.ofNat 64 (globN s "ev" + 64)) := hdom64
                have hm0 : s0.memory (BitVec.ofNat 64 (globN s "ev" + 64)) = .word wg := hmem64
                unfold memLoadHOLExact; rw [if_pos hd0, hm0]
              have hml192 : @memLoadHOLExact 64 _ .one (BitVec.ofNat 64 (globN s "ev" + 192))
                  s0.memaddrs (fun a => Classical.propDecidable (s0.memaddrs a))
                  s0.memory s0.structs = some (.val (.word wsp)) := by
                have hd0 : s0.memaddrs (BitVec.ofNat 64 (globN s "ev" + 192)) := hdom192
                have hm0 : s0.memory (BitVec.ofNat 64 (globN s "ev" + 192)) = .word wsp := hmem192
                unfold memLoadHOLExact; rw [if_pos hd0, hm0]
              have hwf0 : isWfShapeExactHOL s0.structs .one = true := rfl
              have hev_s0 : s0.globals.lookup (ofString "ev") = some (.val (.word evw)) := hevw_lk
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
            rw [Nat.mod_eq_of_lt wsp.isLt, Nat.mod_eq_of_lt (by rw [← hmw64, ← hmw192]; omega)]
          rw [evaluateHOLFiniteState_seq_line780] at hres ⊢
          cases h2 : evaluateHOLFiniteState s1
              (.store (.op .add [.var .global (ofString "ev"), .const 72])
                (.load .one (.op .add [.var .local (ofString "msg"), .const 48]))) with
          | mk r2 s2 =>
            rw [h2] at hres; dsimp only at hres ⊢
            rcases r2 with _ | res2
            · obtain ⟨w2, _, hs2_eq⟩ := store_global_off_word (t := s1) (post := s2)
                (gname := "ev") (gbase := globN s "ev") (off := 72)
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
                · obtain ⟨w3, hw3_ev, hs3_eq⟩ := store_global_off_word (t := s2) (post := s3)
                    (gname := "ev") (gbase := globN s "ev") (off := 192)
                    (by rw [hs2_eq, hs1_eq]; exact hevw_lk) hevw_nat (by omega)
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
                  let post := { (emptyLocalsHOLFinite s3) with
                    locals := (emptyLocalsHOLFinite s3).locals.resVarEq
                      (ofString "msg", s.locals.lookup (ofString "msg")) }
                  have hGp : GuestInv post := by
                    have hmeta : post.code = s.code ∧ post.memaddrs = s.memaddrs ∧
                        post.shMemaddrs = s.shMemaddrs ∧ post.baseAddr = s.baseAddr := by
                      simp [post, emptyLocalsHOLFinite, hs3_eq, hs2_eq, hs1_eq, s0, setVarHOLFinite]
                    exact guestInv_congr hmeta.1 hmeta.2.1 hmeta.2.2.1 hmeta.2.2.2 hInv.1.1
                  have hglob : post.globals = s.globals := by
                    simp [post, emptyLocalsHOLFinite, hs3_eq, hs2_eq, hs1_eq, s0, setVarHOLFinite]
                  have hbe : post.be = s.be := by
                    simp [post, emptyLocalsHOLFinite, hs3_eq, hs2_eq, hs1_eq, s0, setVarHOLFinite]
                  have hmem_out : ∀ x : BitVec 64,
                      (∀ addr ∈ headAllowedOffsets (globN s "ev") (globN s "cur_cont"), x ≠ BitVec.ofNat 64 addr) →
                      post.memory x = s.memory x := by
                    intro x hx
                    change s3.memory x = s.memory x
                    rw [hs3_eq, hs2_eq, hs1_eq]
                    have hn192 : x ≠ BitVec.ofNat 64 (globN s "ev" + 192) := hx _ (by simp [headAllowedOffsets])
                    have hn72 : x ≠ BitVec.ofNat 64 (globN s "ev" + 72) := hx _ (by simp [headAllowedOffsets])
                    have hn64 : x ≠ BitVec.ofNat 64 (globN s "ev" + 64) := hx _ (by simp [headAllowedOffsets])
                    simp [updW, hn192, hn72, hn64, s0, setVarHOLFinite]
                  have hgas_le : memW post (globN s "ev" + 64) + memW post (globN s "ev" + 192) ≤
                      memW s (globN s "ev" + 64) + memW s (globN s "ev" + 192) := by
                    have hm192 : memW post (globN s "ev" + 192) = w3.toNat := by
                      change memW s3 (globN s "ev" + 192) = w3.toNat
                      rw [hs3_eq]; exact memW_updW_same s2 _ w3
                    have hm64 : memW post (globN s "ev" + 64) = w1.toNat := by
                      change memW s3 (globN s "ev" + 64) = w1.toNat
                      rw [hs3_eq, memW_updW_ne s2 _ _ w3 (by omega) (by omega) (by omega),
                          hs2_eq, memW_updW_ne s1 _ _ w2 (by omega) (by omega) (by omega),
                          hs1_eq, memW_updW_same s0 _ w1]
                    rw [hm64, hm192, hw1_sum, hw3_zero]; omega
                  obtain ⟨hEp, hch_eq, hsum_le⟩ :=
                    evmInv_of_head_status_gas_update hInv hGp hglob hbe hmem_out hgas_le
                  exact ⟨hEp, hglob, hch_eq, hsum_le⟩
                · exact absurd hres (store_res_not_resumes h3)
            · exact absurd hres (store_res_not_resumes h2)
        · exact absurd hres (store_res_not_resumes h1)
    · rw [if_neg hsh_msg]; dsimp only; intro hres; exact absurd hres not_resumes_err

theorem ek_refill_frame_state_gas_r11 :
    EvmKeepsR11 EvmInv [] (ofString "refill_frame_state_gas") := by
  refine ⟨_, _, _, lookup_refill_frame_state_gas, ?_⟩
  intro F s _ hInv _ _ hres
  obtain ⟨hEp, hglob, hch_eq, _⟩ := refill_exec_step hInv hres
  exact ⟨hEp, by simp [globN, hglob], fun _ _ => by rw [hglob], hch_eq⟩

/-! ## 4. Exact execution of `frame_halt` on an `EvmInv` state with 1-word `err` -/

theorem frame_halt_body_eq :
    sourceFnBody Guest.Software.guestFn_frame_halt =
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

theorem frame_halt_exec_step {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hInv : EvmInv s) {w_err : BitVec 64}
    (hw_err : s.locals.lookup (ofString "err") = some (.val (.word w_err)))
    (hres : ResumesR11 (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_frame_halt)).1) :
    let post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_frame_halt)).2
    EvmInv post ∧ post.globals = s.globals ∧ evmChain post = evmChain s ∧ evmRR11 post ≤ evmRR11 s := by
  dsimp only
  obtain ⟨he_lt, _, ⟨evw, hevw_lk, hevw_nat⟩, _, _⟩ := evm_head_globals hInv
  rw [frame_halt_body_eq, evaluateHOLFiniteState_seq_line780] at hres ⊢
  cases h1 : evaluateHOLFiniteState s
      (.store (.op .add [.var .global (ofString "ev"), .const 184])
        (.op .add
          [.load .one (.op .add [.var .global (ofString "ev"), .const 184]),
           .load .one (.op .add [.var .global (ofString "ev"), .const 64])])) with
  | mk r1 s1 =>
    rw [h1] at hres; dsimp only at hres ⊢
    rcases r1 with _ | res1
    · obtain ⟨w1, _, hs1_eq⟩ := store_global_off_word (t := s) (post := s1)
        (gname := "ev") (gbase := globN s "ev") (off := 184) hevw_lk hevw_nat (by omega)
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
        · obtain ⟨w2, hw2_ev, hs2_eq⟩ := store_global_off_word (t := s1) (post := s2)
            (gname := "ev") (gbase := globN s "ev") (off := 64)
            (by rw [hs1_eq]; exact hevw_lk) hevw_nat (by omega)
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
            · obtain ⟨w3, _, hs3_eq⟩ := store_global_off_word (t := s2) (post := s3)
                (gname := "ev") (gbase := globN s "ev") (off := 160)
                (by rw [hs2_eq, hs1_eq]; exact hevw_lk) hevw_nat (by omega)
                (fun v hv => by
                  change s2.locals.lookup (ofString "err") = some v at hv
                  rw [hs2_eq, hs1_eq] at hv; dsimp only at hv; rw [hw_err] at hv
                  injection hv with hv'; exact ⟨w_err, hv'.symm⟩) h3
              rw [evaluateHOLFiniteState_return] at hres ⊢
              dsimp only [evalHOLExact] at hres ⊢
              have hle32 : sizeOfShapeWithContextHOL s3.structs
                  (shapeOfHOLExact (ValueHOL.val (HolWordLab.word (0 : BitVec 64)))) ≤ 32 := by
                simp [shapeOfHOLExact]
              rw [if_pos hle32]; dsimp only
              let post := emptyLocalsHOLFinite s3
              have hGp : GuestInv post := by
                have hmeta : post.code = s.code ∧ post.memaddrs = s.memaddrs ∧
                    post.shMemaddrs = s.shMemaddrs ∧ post.baseAddr = s.baseAddr := by
                  simp [post, emptyLocalsHOLFinite, hs3_eq, hs2_eq, hs1_eq]
                exact guestInv_congr hmeta.1 hmeta.2.1 hmeta.2.2.1 hmeta.2.2.2 hInv.1.1
              have hglob : post.globals = s.globals := by
                simp [post, emptyLocalsHOLFinite, hs3_eq, hs2_eq, hs1_eq]
              have hbe : post.be = s.be := by
                simp [post, emptyLocalsHOLFinite, hs3_eq, hs2_eq, hs1_eq]
              have hmem_out : ∀ x : BitVec 64,
                  (∀ addr ∈ headAllowedOffsets (globN s "ev") (globN s "cur_cont"), x ≠ BitVec.ofNat 64 addr) →
                  post.memory x = s.memory x := by
                intro x hx
                change s3.memory x = s.memory x
                rw [hs3_eq, hs2_eq, hs1_eq]
                have hn160 : x ≠ BitVec.ofNat 64 (globN s "ev" + 160) := hx _ (by simp [headAllowedOffsets])
                have hn64 : x ≠ BitVec.ofNat 64 (globN s "ev" + 64) := hx _ (by simp [headAllowedOffsets])
                have hn184 : x ≠ BitVec.ofNat 64 (globN s "ev" + 184) := hx _ (by simp [headAllowedOffsets])
                simp [updW, hn160, hn64, hn184]
              have hgas_le : memW post (globN s "ev" + 64) + memW post (globN s "ev" + 192) ≤
                  memW s (globN s "ev" + 64) + memW s (globN s "ev" + 192) := by
                have hm64 : memW post (globN s "ev" + 64) = w2.toNat := by
                  change memW s3 (globN s "ev" + 64) = w2.toNat
                  rw [hs3_eq, memW_updW_ne s2 _ _ w3 (by omega) (by omega) (by omega),
                      hs2_eq, memW_updW_same s1 _ w2]
                have hm192 : memW post (globN s "ev" + 192) = memW s (globN s "ev" + 192) := by
                  change memW s3 (globN s "ev" + 192) = memW s (globN s "ev" + 192)
                  rw [hs3_eq, memW_updW_ne s2 _ _ w3 (by omega) (by omega) (by omega),
                      hs2_eq, memW_updW_ne s1 _ _ w2 (by omega) (by omega) (by omega),
                      hs1_eq, memW_updW_ne s _ _ w1 (by omega) (by omega) (by omega)]
                rw [hm64, hw2_zero, hm192]; omega
              obtain ⟨hEp, hch_eq, hsum_le⟩ :=
                evmInv_of_head_status_gas_update hInv hGp hglob hbe hmem_out hgas_le
              exact ⟨hEp, hglob, hch_eq, hsum_le⟩
            · exact absurd hres (store_res_not_resumes h3)
        · exact absurd hres (store_res_not_resumes h2)
    · exact absurd hres (store_res_not_resumes h1)

theorem ek_frame_halt_r11 :
    EvmKeepsR11 EvmInv [] (ofString "frame_halt") := by
  refine ⟨_, _, _, lookup_frame_halt, ?_⟩
  intro F s _ hInv hex _ hres
  obtain ⟨w_err, hw_err⟩ := one_word_param_of_lookup lookup_frame_halt hex
  obtain ⟨hEp, hglob, hch_eq, _⟩ := frame_halt_exec_step hInv hw_err hres
  exact ⟨hEp, by simp [globN, hglob], fun _ _ => by rw [hglob], hch_eq⟩

/-! ## 5. Proof of `frame_exception_spec` on R11 -/

theorem frame_exception_body_eq :
    sourceFnBody Guest.Software.guestFn_frame_exception =
      .seq
        (.call (some (none, none)) (ofString "refill_frame_state_gas") [])
        (.seq
          (.ite (.cmp .notEqual (.var .local (ofString "err")) (.const 1))
            (.seq
              (.call (some (none, none)) (ofString "frame_halt") [.var .local (ofString "err")])
              (.seq
                (.store (.op .add [.var .global (ofString "ev"), .const 120]) (.var .global (ofString "evm_empty")))
                (.store (.op .add [.var .global (ofString "ev"), .const 128]) (.const 0))))
            (.store (.op .add [.var .global (ofString "ev"), .const 160]) (.var .local (ofString "err"))))
          (.seq
            (.store (.op .add [.var .global (ofString "cur_cont"), .const 32]) (.const 1))
            (.return (.const 0)))) := rfl

private theorem call0_returned_inv {F : Type} {s post_call : PanSemStateFiniteExact 64 F}
    {fname : MlS} {args : List (ExpHOL 64)}
    (hcall : evaluateHOLFiniteState s (.call (some (none, none)) fname args) = (none, post_call)) :
    ∃ values body callee ret v cpost,
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some values ∧
      lookupCodeHOLFinite s.code.lookup fname values = some (body, callee, ret) ∧
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), cpost) ∧
      post_call = { cpost with locals := s.locals } := by
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

private theorem evmChain_congr_lc {F : Type} (s : PanSemStateFiniteExact 64 F)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    evmChain { s with locals := L, clock := k } = evmChain s := by
  have hcf : ∀ (fuel e c : Nat),
      evmChainFrom { s with locals := L, clock := k } fuel e c = evmChainFrom s fuel e c := by
    intro fuel; induction fuel with
    | zero => intros; rfl
    | succ fuel ih => intros; simp only [evmChainFrom, ih]; rfl
  exact hcf _ _ _

private theorem evmRR11_congr_lc {F : Type} (s : PanSemStateFiniteExact 64 F)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    evmRR11 { s with locals := L, clock := k } = evmRR11 s := by
  unfold evmRR11; rw [evmChain_congr_lc s L k]; rfl

private theorem evmInv_congr_lc {F : Type} (s : PanSemStateFiniteExact 64 F)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) (h : EvmInv s) :
    EvmInv { s with locals := L, clock := k } := by
  have hf : ∀ (nodes : Nat) (Fr : List Nat) (head : Nat),
      FreeChain { s with locals := L, clock := k } nodes head Fr ↔ FreeChain s nodes head Fr := by
    intro nodes Fr; induction Fr with
    | nil => intro _; exact Iff.rfl
    | cons _ rest ih => intro _; exact and_congr Iff.rfl (ih _)
  have hw : ∀ t, HtabWF { s with locals := L, clock := k } t ↔ HtabWF s t := by
    intro t; simp only [HtabWF, hf]; exact Iff.rfl
  have ht : ∀ S, TablesTyped { s with locals := L, clock := k } S ↔ TablesTyped s S := by
    intro S; simp only [TablesTyped, hw]; exact Iff.rfl
  have hwt : ∀ S, WorldTyped { s with locals := L, clock := k } S ↔ WorldTyped s S := by
    intro S; simp only [WorldTyped, ht]; exact Iff.rfl
  have hch : evmChain { s with locals := L, clock := k } = evmChain s := evmChain_congr_lc s L k
  have har : ArenaReady { s with locals := L, clock := k } ↔ ArenaReady s :=
    ⟨fun h0 => ⟨guestInv_congr (s := { s with locals := L, clock := k }) rfl rfl rfl rfl h0.1, h0.2⟩,
     fun h0 => ⟨guestInv_with_locals_clock s L k h0.1, h0.2⟩⟩
  simp only [EvmInv, FrameWF, MsgOwned, hwt, har, hch] at h ⊢
  exact h

private theorem seq_returned_inv {F : Type} {s : PanSemStateFiniteExact 64 F} {p1 p2 : ProgHOL 64}
    {v : ValueHOL 64}
    (h : (evaluateHOLFiniteState s (.seq p1 p2)).1 = some (.returned v))
    (hn1 : ∀ u, (evaluateHOLFiniteState s p1).1 ≠ some (.returned u)) :
    ∃ m, evaluateHOLFiniteState s p1 = (none, m) ∧
      evaluateHOLFiniteState m p2 = evaluateHOLFiniteState s (.seq p1 p2) := by
  have hseq := evaluateHOLFiniteState_seq_line780 s p1 p2
  rcases hr1 : evaluateHOLFiniteState s p1 with ⟨r1, m⟩
  rw [hr1] at hseq
  cases r1 with
  | none => exact ⟨m, rfl, hseq.symm⟩
  | some r =>
    rw [hseq] at h
    dsimp only at h
    injection h with hr; subst hr
    exact absurd hr1 (fun h' => hn1 v (by rw [h']))

private theorem call0_ne_returned {F : Type} (s : PanSemStateFiniteExact 64 F) (fn : MlS)
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

private theorem store_ne_returned {F : Type} (s : PanSemStateFiniteExact 64 F) (d e : ExpHOL 64)
    (u : ValueHOL 64) :
    (evaluateHOLFiniteState s (.store d e)).1 ≠ some (.returned u) := by
  rw [evaluateHOLFiniteState_store]
  split
  · split
    · split <;> simp
    · simp
  · simp

private theorem ite_ne_returned {F : Type} {s : PanSemStateFiniteExact 64 F}
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

private theorem seq_ne_returned {p1 p2 : ProgHOL 64}
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

theorem frame_exception_exec {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) (hInv : EvmInv s)
    (w_emp w_err : BitVec 64) (hw_emp : GlobalWord s "evm_empty" w_emp)
    (hw_err : s.locals.lookup (ofString "err") = some (.val (.word w_err)))
    (v : ValueHOL 64)
    (hv : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_frame_exception)).1 =
      some (.returned v)) :
    let post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_frame_exception)).2
    EvmInv post ∧ EvmDone post ∧
      (evmChain post).length = (evmChain s).length ∧ evmRR11 post ≤ evmRR11 s := by
  dsimp only
  rw [frame_exception_body_eq] at hv ⊢
  -- Step 1: call `refill_frame_state_gas`
  obtain ⟨m1, hs1_call, hrest1⟩ := seq_returned_inv hv (call0_ne_returned s _ _)
  have hpost_eq1 := congrArg Prod.snd hrest1.symm
  rw [← hrest1] at hv; rw [hpost_eq1]; clear hrest1 hpost_eq1
  obtain ⟨vals1, body1, cal1, ret1, rv1, cpost1, _, hl1, hrun1, hm1_eq⟩ := call0_returned_inv hs1_call
  have hcode_lk1 : s.code.lookup (ofString "refill_frame_state_gas") =
      some ([], sourceFnBody Guest.Software.guestFn_refill_frame_state_gas, .one) := by
    rw [hcode]; exact lookup_refill_frame_state_gas
  have hbody1 : body1 = sourceFnBody Guest.Software.guestFn_refill_frame_state_gas :=
    lookupCodeHOLFinite_installed_body s.code.lookup _ _ _ _ _ _ _ _ hcode_lk1 hl1
  subst hbody1
  have hInv_ce1 : EvmInv (callEntryStateHOLFinite s cal1) := evmInv_congr_lc s cal1 (s.clock - 1) hInv
  have hres1 : ResumesR11 (evaluateHOLFiniteState (callEntryStateHOLFinite s cal1)
      (sourceFnBody Guest.Software.guestFn_refill_frame_state_gas)).1 := by
    rw [hrun1]; exact Or.inl ⟨rv1, rfl⟩
  obtain ⟨hInv_cp1, hglob_cp1, hch_cp1, hR_cp1⟩ := refill_exec_step hInv_ce1 hres1
  have hcpost1_eq : (evaluateHOLFiniteState (callEntryStateHOLFinite s cal1)
      (sourceFnBody Guest.Software.guestFn_refill_frame_state_gas)).2 = cpost1 := by
    rw [hrun1]
  rw [hcpost1_eq] at hInv_cp1 hglob_cp1 hch_cp1 hR_cp1
  subst hm1_eq
  let s1 := ({ cpost1 with locals := s.locals } : PanSemStateFiniteExact 64 F)
  have hInv1 : EvmInv s1 := evmInv_congr_lc cpost1 s.locals cpost1.clock hInv_cp1
  have hglob1 : s1.globals = s.globals := hglob_cp1
  have hch1 : evmChain s1 = evmChain s := by
    have h1 : evmChain s1 = evmChain cpost1 := evmChain_congr_lc cpost1 s.locals cpost1.clock
    have h2 : evmChain (callEntryStateHOLFinite s cal1) = evmChain s := evmChain_congr_lc s cal1 (s.clock - 1)
    exact h1.trans (hch_cp1.trans h2)
  have hR1 : evmRR11 s1 ≤ evmRR11 s := by
    have h1 : evmRR11 s1 = evmRR11 cpost1 := evmRR11_congr_lc cpost1 s.locals cpost1.clock
    have h2 : evmRR11 (callEntryStateHOLFinite s cal1) = evmRR11 s := evmRR11_congr_lc s cal1 (s.clock - 1)
    omega
  have hcode1 : s1.code = originalRuntimeCode := by
    have hm := (PanRunBounded.evaluateHOLFiniteState_metadata s
      (.call (some (none, none)) (ofString "refill_frame_state_gas") [])).1
    rw [hs1_call] at hm; exact hm.trans hcode
  -- Step 2: `ite (err != 1) ... ...`
  have hite_noret := ite_ne_returned (s := s1)
    (c := .cmp .notEqual (.var .local (ofString "err")) (.const 1))
    (seq_ne_returned (fun t u => call0_ne_returned t _ _ u)
      (seq_ne_returned (fun t u => store_ne_returned t _ _ u) (fun t u => store_ne_returned t _ _ u)))
    (fun t u => store_ne_returned t _ _ u)
  obtain ⟨s2, hs2_ite, hrest2⟩ := seq_returned_inv hv hite_noret
  have hpost_eq2 := congrArg Prod.snd hrest2.symm
  rw [← hrest2] at hv; rw [hpost_eq2]; clear hrest2 hpost_eq2
  -- Show `EvmInv s2 ∧ s2.globals = s1.globals ∧ evmChain s2 = evmChain s1 ∧ evmRR11 s2 ≤ evmRR11 s1`
  have hs2_props : EvmInv s2 ∧ s2.globals = s1.globals ∧ evmChain s2 = evmChain s1 ∧ evmRR11 s2 ≤ evmRR11 s1 := by
    obtain ⟨he_lt1, _, ⟨evw1, hevw1_lk, hevw1_nat⟩, _, _⟩ := evm_head_globals hInv1
    have herr_s1 : s1.locals.lookup (ofString "err") = some (.val (.word w_err)) := hw_err
    rw [evaluateHOLFiniteState_ite] at hs2_ite
    have hcmp : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
        (.cmp .notEqual (.var .local (ofString "err")) (.const 1)) =
        some (.val (.word (if w_err ≠ 1 then 1 else 0))) := by
      simp [evalHOLExact, herr_s1, Compiler.Encoders.Asm.wordCmpHOL]
    rw [hcmp] at hs2_ite; dsimp only at hs2_ite
    by_cases hw1 : w_err = 1
    · -- `err == 1`: runs `store (ev + 160) err`
      subst hw1; simp only [ne_eq, not_true_eq_false, ↓reduceIte] at hs2_ite
      obtain ⟨w160, _, rfl⟩ := store_global_off_word (t := s1) (post := s2)
        (gname := "ev") (gbase := globN s1 "ev") (off := 160) hevw1_lk hevw1_nat (by omega)
        (fun v0 hv0 => by
          change s1.locals.lookup (ofString "err") = some v0 at hv0
          rw [herr_s1] at hv0; injection hv0 with hv'; exact ⟨1, hv'.symm⟩) hs2_ite
      let post2 := { s1 with memory := updW s1.memory (BitVec.ofNat 64 (globN s1 "ev" + 160)) w160 }
      have hGp2 : GuestInv post2 := guestInv_congr (s := s1) rfl rfl rfl rfl hInv1.1.1
      have hmem2 : ∀ x : BitVec 64,
          (∀ addr ∈ headAllowedOffsets (globN s1 "ev") (globN s1 "cur_cont"), x ≠ BitVec.ofNat 64 addr) →
          post2.memory x = s1.memory x := by
        intro x hx
        have hn160 : x ≠ BitVec.ofNat 64 (globN s1 "ev" + 160) := hx _ (by simp [headAllowedOffsets])
        simp [post2, updW, hn160]
      have hgas2 : memW post2 (globN s1 "ev" + 64) + memW post2 (globN s1 "ev" + 192) ≤
          memW s1 (globN s1 "ev" + 64) + memW s1 (globN s1 "ev" + 192) := by
        rw [memW_updW_ne s1 _ _ w160 (by omega) (by omega) (by omega),
            memW_updW_ne s1 _ _ w160 (by omega) (by omega) (by omega)]
      obtain ⟨hEp2, hch2, hR2⟩ := evmInv_of_head_status_gas_update hInv1 hGp2 rfl rfl hmem2 hgas2
      exact ⟨hEp2, rfl, hch2, hR2⟩
    · -- `err != 1`: runs `call frame_halt [err]; store (ev+120) evm_empty; store (ev+128) 0`
      have h10 : ((1 : BitVec 64) = 0) = False := by decide
      simp only [ne_eq, hw1, not_false_eq_true, ↓reduceIte, h10] at hs2_ite
      rw [evaluateHOLFiniteState_seq_line780] at hs2_ite
      rcases hfh : evaluateHOLFiniteState s1
          (.call (some (none, none)) (ofString "frame_halt") [.var .local (ofString "err")]) with ⟨rfh, mfh⟩
      rw [hfh] at hs2_ite
      rcases rfh with _ | r_bad
      · dsimp only at hs2_ite
        obtain ⟨vals_fh, body_fh, cal_fh, ret_fh, rv_fh, cpost_fh, hargs_fh, hl_fh, hrun_fh, hmfh_eq⟩ :=
          call0_returned_inv hfh
        subst hmfh_eq
        have hcode1_fh : s1.code.lookup (ofString "frame_halt") =
            some ([(ofString "err", .one)], sourceFnBody Guest.Software.guestFn_frame_halt, .one) := by
          rw [hcode1]; exact lookup_frame_halt
        have hbody_fh : body_fh = sourceFnBody Guest.Software.guestFn_frame_halt :=
          lookupCodeHOLFinite_installed_body s1.code.lookup _ _ _ _ _ _ _ _ hcode1_fh hl_fh
        subst hbody_fh
        have hret_fh : ret_fh = .one := by
          have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
            s1.code.lookup (ofString "frame_halt") vals_fh (sourceFnBody Guest.Software.guestFn_frame_halt)
            cal_fh ret_fh hl_fh
          simp only [Flapjack.lookupCodeHOLExact, hcode1_fh] at hx
          split at hx
          · exact (congrArg (fun x => x.2.2) (Option.some.inj hx)).symm
          · cases hx
        subst hret_fh
        obtain ⟨w_ce_err, hw_ce_err⟩ := one_word_param_of_lookup lookup_frame_halt
          ⟨vals_fh, by rwa [hcode1] at hl_fh⟩
        have hInv_ce_fh : EvmInv (callEntryStateHOLFinite s1 cal_fh) :=
          evmInv_congr_lc s1 cal_fh (s1.clock - 1) hInv1
        have hres_fh : ResumesR11 (evaluateHOLFiniteState (callEntryStateHOLFinite s1 cal_fh)
            (sourceFnBody Guest.Software.guestFn_frame_halt)).1 := by
          rw [hrun_fh]; exact Or.inl ⟨rv_fh, rfl⟩
        obtain ⟨hInv_cp_fh, hglob_cp_fh, hch_cp_fh, hR_cp_fh⟩ :=
          frame_halt_exec_step hInv_ce_fh hw_ce_err hres_fh
        have hcpost_fh_eq : (evaluateHOLFiniteState (callEntryStateHOLFinite s1 cal_fh)
            (sourceFnBody Guest.Software.guestFn_frame_halt)).2 = cpost_fh := by
          rw [hrun_fh]
        rw [hcpost_fh_eq] at hInv_cp_fh hglob_cp_fh hch_cp_fh hR_cp_fh
        let sfh := ({ cpost_fh with locals := s1.locals } : PanSemStateFiniteExact 64 F)
        have hInv_fh : EvmInv sfh := evmInv_congr_lc cpost_fh s1.locals cpost_fh.clock hInv_cp_fh
        have hglob_fh : sfh.globals = s1.globals := hglob_cp_fh
        have hch_fh : evmChain sfh = evmChain s1 := by
          have h1 : evmChain sfh = evmChain cpost_fh := evmChain_congr_lc cpost_fh s1.locals cpost_fh.clock
          have h2 : evmChain (callEntryStateHOLFinite s1 cal_fh) = evmChain s1 := evmChain_congr_lc s1 cal_fh (s1.clock - 1)
          exact h1.trans (hch_cp_fh.trans h2)
        have hR_fh : evmRR11 sfh ≤ evmRR11 s1 := by
          have h1 : evmRR11 sfh = evmRR11 cpost_fh := evmRR11_congr_lc cpost_fh s1.locals cpost_fh.clock
          have h2 : evmRR11 (callEntryStateHOLFinite s1 cal_fh) = evmRR11 s1 := evmRR11_congr_lc s1 cal_fh (s1.clock - 1)
          omega
        -- Now two stores: `ev + 120 := evm_empty` and `ev + 128 := 0`
        rw [evaluateHOLFiniteState_seq_line780] at hs2_ite
        rcases hst120 : evaluateHOLFiniteState sfh
            (.store (.op .add [.var .global (ofString "ev"), .const 120])
              (.var .global (ofString "evm_empty"))) with ⟨r120, s120⟩
        rw [hst120] at hs2_ite
        rcases r120 with _ | _
        · dsimp only at hs2_ite
          have hev_sfh : globN sfh "ev" = globN s1 "ev" := by simp [globN, hglob_fh]
          have hcc_sfh : globN sfh "cur_cont" = globN s1 "cur_cont" := by simp [globN, hglob_fh]
          have hemp_sfh : sfh.globals.lookup (ofString "evm_empty") = some (.val (.word w_emp)) := by
            rw [hglob_fh, hglob1]; exact hw_emp
          obtain ⟨w120, _, hs120_eq⟩ := store_global_off_word (t := sfh) (post := s120)
            (gname := "ev") (gbase := globN s1 "ev") (off := 120)
            (by rw [hglob_fh]; exact hevw1_lk) hevw1_nat (by omega)
            (fun v0 hv0 => by
              change sfh.globals.lookup (ofString "evm_empty") = some v0 at hv0
              rw [hemp_sfh] at hv0; injection hv0 with hv'; exact ⟨w_emp, hv'.symm⟩) hst120
          obtain ⟨w128, _, hs2_eq⟩ := store_global_off_word (t := s120) (post := s2)
            (gname := "ev") (gbase := globN s1 "ev") (off := 128)
            (by rw [hs120_eq, hglob_fh]; exact hevw1_lk) hevw1_nat (by omega)
            (fun v0 hv0 => by
              simp [evalHOLExact] at hv0; exact ⟨0, hv0.symm⟩) hs2_ite
          have hGp_s2 : GuestInv s2 := by
            rw [hs2_eq, hs120_eq]
            exact guestInv_congr (s := sfh) rfl rfl rfl rfl hInv_fh.1.1
          have hglob_s2 : s2.globals = sfh.globals := by rw [hs2_eq, hs120_eq]
          have hbe_s2 : s2.be = sfh.be := by rw [hs2_eq, hs120_eq]
          have hmem_s2 : ∀ x : BitVec 64,
              (∀ addr ∈ headAllowedOffsets (globN sfh "ev") (globN sfh "cur_cont"), x ≠ BitVec.ofNat 64 addr) →
              s2.memory x = sfh.memory x := by
            intro x hx
            rw [hs2_eq, hs120_eq]
            have hn120 : x ≠ BitVec.ofNat 64 (globN s1 "ev" + 120) := by
              rw [← hev_sfh]; exact hx _ (by simp [headAllowedOffsets])
            have hn128 : x ≠ BitVec.ofNat 64 (globN s1 "ev" + 128) := by
              rw [← hev_sfh]; exact hx _ (by simp [headAllowedOffsets])
            simp [updW, hn120, hn128]
          have hgas_s2 : memW s2 (globN sfh "ev" + 64) + memW s2 (globN sfh "ev" + 192) ≤
              memW sfh (globN sfh "ev" + 64) + memW sfh (globN sfh "ev" + 192) := by
            rw [hev_sfh, hs2_eq,
                memW_updW_ne s120 _ _ w128 (by omega) (by omega) (by omega),
                memW_updW_ne s120 _ _ w128 (by omega) (by omega) (by omega),
                hs120_eq,
                memW_updW_ne sfh _ _ w120 (by omega) (by omega) (by omega),
                memW_updW_ne sfh _ _ w120 (by omega) (by omega) (by omega)]
          obtain ⟨hEp_s2, hch_s2, hR_s2⟩ :=
            evmInv_of_head_status_gas_update hInv_fh hGp_s2 hglob_s2 hbe_s2 hmem_s2 hgas_s2
          exact ⟨hEp_s2, hglob_s2.trans hglob_fh, hch_s2.trans hch_fh, le_trans hR_s2 hR_fh⟩
        · cases hs2_ite
      · cases hs2_ite
  -- Step 3: `store (cur_cont + 32) 1; return 0`
  obtain ⟨hInv2, hglob2, hch2, hR2⟩ := hs2_props
  obtain ⟨s3, hs3_st, hrest3⟩ := seq_returned_inv hv (store_ne_returned s2 _ _)
  have hpost_eq3 := congrArg Prod.snd hrest3.symm
  rw [← hrest3] at hv; rw [hpost_eq3]; clear hrest3 hpost_eq3
  obtain ⟨he_lt2, hc_lt2, _, ⟨ccw2, hccw2_lk, hccw2_nat⟩, _⟩ := evm_head_globals hInv2
  obtain ⟨w32, hw32_eval, hs3_eq⟩ := store_global_off_word (t := s2) (post := s3)
    (gname := "cur_cont") (gbase := globN s2 "cur_cont") (off := 32) hccw2_lk hccw2_nat (by omega)
    (fun v0 hv0 => by simp [evalHOLExact] at hv0; exact ⟨1, hv0.symm⟩) hs3_st
  have hw32_eq1 : w32 = 1 := by
    simp [evalHOLExact] at hw32_eval
    exact hw32_eval.symm
  rw [evaluateHOLFiniteState_return] at hv ⊢
  have hc0 : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
      (.const 0) = some (.val (.word 0)) := rfl
  rw [hc0] at hv ⊢; dsimp only at hv ⊢
  have hle32 : sizeOfShapeWithContextHOL s3.structs
      (shapeOfHOLExact (ValueHOL.val (HolWordLab.word (0 : BitVec 64)))) ≤ 32 := by
    simp [shapeOfHOLExact]
  rw [if_pos hle32]; dsimp only
  let post := emptyLocalsHOLFinite s3
  have hGp_post : GuestInv post := by
    simp only [post, emptyLocalsHOLFinite, hs3_eq]
    exact guestInv_congr (s := s2) rfl rfl rfl rfl hInv2.1.1
  have hglob_post : post.globals = s2.globals := by simp [post, emptyLocalsHOLFinite, hs3_eq]
  have hbe_post : post.be = s2.be := by simp [post, emptyLocalsHOLFinite, hs3_eq]
  have hmem_post : ∀ x : BitVec 64,
      (∀ addr ∈ headAllowedOffsets (globN s2 "ev") (globN s2 "cur_cont"), x ≠ BitVec.ofNat 64 addr) →
      post.memory x = s2.memory x := by
    intro x hx
    change s3.memory x = s2.memory x
    rw [hs3_eq]
    have hn32 : x ≠ BitVec.ofNat 64 (globN s2 "cur_cont" + 32) := hx _ (by simp [headAllowedOffsets])
    simp [updW, hn32]
  have hgas_post : memW post (globN s2 "ev" + 64) + memW post (globN s2 "ev" + 192) ≤
      memW s2 (globN s2 "ev" + 64) + memW s2 (globN s2 "ev" + 192) := by
    have hdisj_ec2 : Disj (globN s2 "ev", 280) (globN s2 "cur_cont", 104) := by
      obtain ⟨_, _, _, _, _, _, _, _, hP2, _⟩ := hInv2
      have hfl := List.pairwise_flatten.mp hP2
      have hmem0 : (globN s2 "ev", globN s2 "cur_cont") ∈ evmChain s2 := by simp [evmChain, evmChainFrom]
      have hp0 := hfl.1 _ (List.mem_map_of_mem hmem0)
      exact (List.pairwise_cons.mp (List.pairwise_append.mp hp0).1).1 _ (by simp)
    have hne64 : globN s2 "ev" + 64 ≠ globN s2 "cur_cont" + 32 := by
      unfold Disj at hdisj_ec2; dsimp only at hdisj_ec2
      rcases hdisj_ec2 with h | h | h | h <;> omega
    have hne192 : globN s2 "ev" + 192 ≠ globN s2 "cur_cont" + 32 := by
      unfold Disj at hdisj_ec2; dsimp only at hdisj_ec2
      rcases hdisj_ec2 with h | h | h | h <;> omega
    change memW s3 (globN s2 "ev" + 64) + memW s3 (globN s2 "ev" + 192) ≤ _
    rw [hs3_eq,
        memW_updW_ne s2 _ _ w32 (by omega) (by omega) hne64,
        memW_updW_ne s2 _ _ w32 (by omega) (by omega) hne192]
  obtain ⟨hEp_post, hch_post, hR_post⟩ :=
    evmInv_of_head_status_gas_update hInv2 hGp_post hglob_post hbe_post hmem_post hgas_post
  have hdone_post : EvmDone post := by
    left
    have hcc_post : globN post "cur_cont" = globN s2 "cur_cont" := by simp [globN, hglob_post]
    rw [hcc_post]
    change memW s3 (globN s2 "cur_cont" + 32) ≠ 0
    rw [hs3_eq, memW_updW_same, hw32_eq1]
    decide
  exact ⟨hEp_post, hdone_post, by rw [hch_post, hch2, hch1], le_trans hR_post (le_trans hR2 hR1)⟩

theorem frame_exception_spec_of_evm_empty_word :
    FunSpecR11 (fun s => EvmInv s ∧ ∃ w : BitVec 64, GlobalWord s "evm_empty" w)
      (OnReturnR11 fun s post => EvmInv post ∧ EvmDone post ∧
        (evmChain post).length = (evmChain s).length ∧ evmRR11 post ≤ evmRR11 s)
      (ofString "frame_exception") := by
  refine ⟨[(ofString "err", .one)], sourceFnBody Guest.Software.guestFn_frame_exception, .one,
    lookup_frame_exception, ?_⟩
  intro F s hcode ⟨hInv, w_emp, hw_emp⟩ hex _ v hv
  obtain ⟨w_err, hw_err⟩ := one_word_param_of_lookup lookup_frame_exception hex
  exact frame_exception_exec s hcode hInv w_emp w_err hw_emp hw_err v hv

end InitECandidate.Solver.Wave8GuestInv.R11Shards


