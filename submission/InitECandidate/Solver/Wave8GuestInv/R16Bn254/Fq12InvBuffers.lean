import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.GuestTrapAlign
import InitECandidate.Solver.HeapPotential
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.MemcpyAlignedBody
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqPolynomialFrame
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqPolynomialRank
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqStationaryValues
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqPolySubmulCalls
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.StateTraceReturned

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.Wave8GuestInv.R16Bn254
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Encoders.Asm
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith

theorem ordinaryDomain_iff_local (x : BitVec 64) :
    ordinaryDomain x ↔ x.toNat % 8 = 0 ∧ sourceBase ≤ x.toNat ∧ x.toNat < heapEnd := by
  unfold ordinaryDomain
  rw [StackRemove.mem_addresses]
  have hx := x.isLt
  have hconst : (stackStart - sourceBase) / 8 - globalsWords = 3888119741 ∧
      sourceBase = 2701131776 ∧ heapEnd = 33806089704 ∧
      StackRemove.bytesInWord 64 = BitVec.ofNat 64 8 := ⟨by decide, by decide, by decide, by decide⟩
  rcases hconst with ⟨hn, hsb, hhe, hbw⟩
  rw [hn, hbw]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [BitVec.ofNat_mul_ofNat, BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat]
    simp only [hsb, hhe]
    omega
  · rintro ⟨hal, hlo, hhi⟩
    refine ⟨(x.toNat - sourceBase) / 8, by simp only [hsb, hhe] at hlo hhi; omega, ?_⟩
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.ofNat_mul_ofNat, BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat]
    simp only [hsb, hhe] at hlo hhi ⊢
    omega

/-- Any two non-overlapping 416-byte intervals (`b1 + 416 ≤ b2` or `b2 + 416 ≤ b1`, nonwrapping)
give `PolynomialDisjoint b1 b2`. -/
theorem polynomialDisjoint_of_nonoverlap (b1 b2 : BitVec 64)
    (hw1 : b1.toNat + 416 ≤ 2 ^ 64) (hw2 : b2.toNat + 416 ≤ 2 ^ 64)
    (hdisj : b1.toNat + 416 ≤ b2.toNat ∨ b2.toNat + 416 ≤ b1.toNat) :
    PolynomialDisjoint b1 b2 := by
  intro j hj k hk x hxk hxj
  obtain ⟨uk, huk, rfl⟩ := coefficientWords_member b2 x k hxk
  obtain ⟨uj, huj, heq⟩ := coefficientWords_member b1 _ j hxj
  have hk_nat : (coefficientAddress b2 k + BitVec.ofNat 64 uk).toNat = b2.toNat + 32 * k + uk := by
    simp only [coefficientAddress, BitVec.add_assoc, ← BitVec.ofNat_add]
    rw [BitVec.toNat_add_of_lt]
    · simp only [BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt (by omega)]; omega
    · simp only [BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt (by omega)]; omega
  have hj_nat : (coefficientAddress b1 j + BitVec.ofNat 64 uj).toNat = b1.toNat + 32 * j + uj := by
    simp only [coefficientAddress, BitVec.add_assoc, ← BitVec.ofNat_add]
    rw [BitVec.toNat_add_of_lt]
    · simp only [BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt (by omega)]; omega
    · simp only [BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt (by omega)]; omega
  have hnat := congrArg BitVec.toNat heq
  rw [hk_nat, hj_nat] at hnat
  rcases hdisj with h | h <;> omega

/-- An 8-byte-aligned 416-byte block inside `[sourceBase, heapEnd)` satisfies `DomainPolynomial`
under `GuestInv` and constructs a represented `MemoryPolynomial`. -/
theorem domainPolynomial_of_interval {F : Type} (s : PanSemStateFiniteExact 64 F)
    (base : BitVec 64) (hG : GuestInv s)
    (halign : base.toNat % 8 = 0)
    (hlo : sourceBase ≤ base.toNat) (hhi : base.toNat + 416 ≤ heapEnd) :
    DomainPolynomial s.memaddrs base ∧ base.toNat + 416 ≤ 2 ^ 64 ∧
      MemoryPolynomial s.memory base (polynomialMemoryCoefficients s.memory base) := by
  have hhe64 : heapEnd < 2 ^ 64 := by decide
  have hw : base.toNat + 416 ≤ 2 ^ 64 := by omega
  refine ⟨?_, hw, ?_⟩
  · intro i hi
    have haddr_nat : ∀ off : Nat, off < 32 →
        (coefficientAddress base i + BitVec.ofNat 64 off).toNat = base.toNat + 32 * i + off := by
      intro off hoff
      simp only [coefficientAddress, BitVec.add_assoc, ← BitVec.ofNat_add]
      rw [BitVec.toNat_add_of_lt]
      · simp only [BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt (by omega)]; omega
      · simp only [BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt (by omega)]; omega
    have hcell : ∀ off : Nat, off < 32 → off % 8 = 0 →
        s.memaddrs (coefficientAddress base i + BitVec.ofNat 64 off) := by
      intro off hoff hm8
      rw [hG.memaddrs, ordinaryDomain_iff_local]
      have hn := haddr_nat off hoff
      exact ⟨by omega, by omega, by omega⟩
    refine ⟨by simpa using hcell 0 (by decide) (by decide),
      hcell 8 (by decide) (by decide),
      hcell 16 (by decide) (by decide),
      hcell 24 (by decide) (by decide)⟩
  · intro i hi
    unfold MemoryU256 polynomialMemoryCoefficients polynomialMemoryWord
    refine ⟨?_, ?_, ?_, ?_⟩
    · cases s.memory (coefficientAddress base i) <;> rfl
    · cases s.memory (coefficientAddress base i + 8) <;> rfl
    · cases s.memory (coefficientAddress base i + 16) <;> rfl
    · cases s.memory (coefficientAddress base i + 24) <;> rfl

/-! ### 1. `alloc(416)` exact step on `GuestInv` -/

private theorem lookup_alloc_416 :
    originalRuntimeCode.lookup (ofString "alloc") =
      some ([(ofString "n", .one)], sourceFnBody Guest.Software.guestFn_alloc, .one) :=
  lookup_of_guestAst_getElem 7 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_alloc) rfl

theorem alloc416_callee_returned {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (ret : ValueHOL 64) (hc : s.code = originalRuntimeCode)
    (hl : s.locals.lookup (ofString "n") = some (.val (.word 416)))
    (hr : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_alloc) =
      (some (.returned ret), post)) :
    ∃ p q : BitVec 64,
      ret = .val (.word p) ∧
      s.globals.lookup (ofString "heap_ptr") = some (.val (.word p)) ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word q)) ∧
      post.memory = s.memory ∧
      q = (p + (416 + 7)) &&& ((0 : BitVec 64) - 8) ∧
      q.toNat ≤ heapLimit ∧
      (p.toNat + 423 < 2 ^ 64 →
        p.toNat + 416 ≤ q.toNat ∧ q.toNat = (p.toNat + 423) / 8 * 8 ∧ q.toNat % 8 = 0) := by
  have hbody_eq : sourceFnBody Guest.Software.guestFn_alloc =
      .dec (ofString "p") .one (.var .global (ofString "heap_ptr"))
        (.seq
          (.ite (.cmp .lower (.op .sub [.const 2952790016, .var .local (ofString "p")])
              (.var .local (ofString "n")))
            (.call (some (none, none)) (ofString "trap_with") [.const 1])
            .skip)
          (.dec (ofString "q") .one
            (.op .and [.op .add [.var .local (ofString "p"), .var .local (ofString "n"), .const 7],
              .op .sub [.const 0, .const 8]])
            (.seq
              (.ite (.cmp .lower (.const 2952790016) (.var .local (ofString "q")))
                (.call (some (none, none)) (ofString "trap_with") [.const 1])
                .skip)
              (.seq
                (.assign .global (ofString "heap_ptr") (.var .local (ofString "q")))
                (.return (.var .local (ofString "p"))))))) := rfl
  have hret1 := congrArg Prod.fst hr
  dsimp only at hret1
  rw [hbody_eq, evaluateHOLFiniteState_dec_total] at hr hret1
  dsimp only at hr hret1
  have hp_word : ∃ p : BitVec 64, s.globals.lookup (ofString "heap_ptr") = some (.val (.word p)) := by
    rcases hg : s.globals.lookup (ofString "heap_ptr") with _ | gv
    · simp [evalHOLExact, hg] at hret1
    · rcases gv with ⟨⟨p⟩⟩ | fs | ⟨nm, fs⟩
      · exact ⟨p, rfl⟩
      · simp [evalHOLExact, hg, shapeEqHOL, shapeOfHOLExact] at hret1
      · simp [evalHOLExact, hg, shapeEqHOL, shapeOfHOLExact] at hret1
  obtain ⟨p, hp_lk⟩ := hp_word
  have hp_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.var .global (ofString "heap_ptr")) = some (.val (.word p)) := hp_lk
  rw [hp_ev] at hr hret1
  have hsh_p : shapeEqHOL .one (shapeOfHOLExact (.val (.word p))) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  dsimp only at hr hret1
  rw [if_pos hsh_p] at hr hret1
  dsimp only at hr hret1
  let pState := setVarHOLFinite (ofString "p") (.val (.word p)) s
  have hp_loc : pState.locals.lookup (ofString "p") = some (.val (.word p)) := by
    simp [pState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hn_loc : pState.locals.lookup (ofString "n") = some (.val (.word 416)) := by
    simp [pState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hl,
      show ofString "p" ≠ ofString "n" by decide]
  rw [evaluateHOLFiniteState_seq_line780] at hr hret1
  have hev1 : @evalHOLExact 64 F _ pState.toExact
      (fun a => Classical.propDecidable (pState.memaddrs a))
      (.cmp .lower (.op .sub [.const 2952790016, .var .local (ofString "p")])
        (.var .local (ofString "n"))) =
      some (.val (.word (if ((2952790016 : BitVec 64) - p).toNat < 416 then 1 else 0))) := by
    simp only [evalHOLExact, evalListHOLExact, hp_loc, hn_loc,
      wordCmpHOL, BitVec.lt_def, decide_eq_true_eq]
    rfl
  by_cases hcmp1 : ((2952790016 : BitVec 64) - p).toNat < 416
  · have hite1 : evaluateHOLFiniteState pState
        (.ite (.cmp .lower (.op .sub [.const 2952790016, .var .local (ofString "p")])
            (.var .local (ofString "n")))
          (.call (some (none, none)) (ofString "trap_with") [.const 1]) .skip) =
        evaluateHOLFiniteState pState (.call (some (none, none)) (ofString "trap_with") [.const 1]) := by
      rw [evaluateHOLFiniteState_ite, hev1, if_pos hcmp1]; simp
    rw [hite1] at hret1
    have hno_none := evaluate_call_trap_with_no_none pState 1 hc
    have hno_ret := fun w => evaluate_call_trap_with_no_return pState 1 w hc
    rcases htr : evaluateHOLFiniteState pState (.call (some (none, none)) (ofString "trap_with") [.const 1]) with ⟨r1, s1⟩
    rw [htr] at hno_none hno_ret hret1
    cases r1 with
    | none => exact absurd rfl hno_none
    | some _ => exact absurd hret1 (hno_ret ret)
  · have hite1 : evaluateHOLFiniteState pState
        (.ite (.cmp .lower (.op .sub [.const 2952790016, .var .local (ofString "p")])
            (.var .local (ofString "n")))
          (.call (some (none, none)) (ofString "trap_with") [.const 1]) .skip) = (none, pState) := by
      rw [evaluateHOLFiniteState_ite, hev1, if_neg hcmp1]; simp [evaluateHOLFiniteState_skip]
    rw [hite1] at hr hret1
    dsimp only at hr hret1
    rw [evaluateHOLFiniteState_dec_total] at hr hret1
    let q : BitVec 64 := (p + (416 + 7)) &&& ((0 : BitVec 64) - 8)
    have hq_ev : @evalHOLExact 64 F _ pState.toExact
        (fun a => Classical.propDecidable (pState.memaddrs a))
        (.op .and [.op .add [.var .local (ofString "p"), .var .local (ofString "n"), .const 7],
          .op .sub [.const 0, .const 8]]) = some (.val (.word q)) := by
      simp only [evalHOLExact, evalListHOLExact, hp_loc, hn_loc,
        wordOpHOL, wordOp, valueIsWord, valueWord, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr]
      exact congrArg (fun w => some (ValueHOL.val (HolWordLab.word w)))
        (InitECandidate.Solver.HeapPotential.alloc_q_word_eq p 416)
    dsimp only at hr hret1
    rw [hq_ev] at hr hret1
    have hsh_q : shapeEqHOL .one (shapeOfHOLExact (.val (.word q))) = true := by
      simp [shapeEqHOL, shapeOfHOLExact]
    dsimp only at hr hret1
    rw [if_pos hsh_q] at hr hret1
    dsimp only at hr hret1
    let qState := setVarHOLFinite (ofString "q") (.val (.word q)) pState
    have hq_loc : qState.locals.lookup (ofString "q") = some (.val (.word q)) := by
      simp [qState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hp_loc_q : qState.locals.lookup (ofString "p") = some (.val (.word p)) := by
      simp [qState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hp_loc,
        show ofString "q" ≠ ofString "p" by decide]
    rw [evaluateHOLFiniteState_seq_line780] at hr hret1
    have hev2 : @evalHOLExact 64 F _ qState.toExact
        (fun a => Classical.propDecidable (qState.memaddrs a))
        (.cmp .lower (.const 2952790016) (.var .local (ofString "q"))) =
        some (.val (.word (if 2952790016 < q.toNat then 1 else 0))) := by
      simp only [evalHOLExact, hq_loc, wordCmpHOL, BitVec.lt_def, decide_eq_true_eq]
      rfl
    by_cases hcmp2 : 2952790016 < q.toNat
    · have hite2 : evaluateHOLFiniteState qState
          (.ite (.cmp .lower (.const 2952790016) (.var .local (ofString "q")))
            (.call (some (none, none)) (ofString "trap_with") [.const 1]) .skip) =
          evaluateHOLFiniteState qState (.call (some (none, none)) (ofString "trap_with") [.const 1]) := by
        rw [evaluateHOLFiniteState_ite, hev2, if_pos hcmp2]; simp
      rw [hite2] at hret1
      have hno_none := evaluate_call_trap_with_no_none qState 1 hc
      have hno_ret := fun w => evaluate_call_trap_with_no_return qState 1 w hc
      rcases htr : evaluateHOLFiniteState qState (.call (some (none, none)) (ofString "trap_with") [.const 1]) with ⟨r2, s2⟩
      rw [htr] at hno_none hno_ret hret1
      cases r2 with
      | none => exact absurd rfl hno_none
      | some _ => exact absurd hret1 (hno_ret ret)
    · have hite2 : evaluateHOLFiniteState qState
          (.ite (.cmp .lower (.const 2952790016) (.var .local (ofString "q")))
            (.call (some (none, none)) (ofString "trap_with") [.const 1]) .skip) = (none, qState) := by
        rw [evaluateHOLFiniteState_ite, hev2, if_neg hcmp2]; simp [evaluateHOLFiniteState_skip]
      rw [hite2] at hr
      dsimp only at hr
      have hp_g : qState.globals.lookup (ofString "heap_ptr") = some (.val (.word p)) := hp_lk
      have heval_end : evaluateHOLFiniteState qState
          (.seq (.assign .global (ofString "heap_ptr") (.var .local (ofString "q")))
            (.return (.var .local (ofString "p")))) =
          (some (.returned (.val (.word p))),
            emptyLocalsHOLFinite (setGlobalHOLFinite (ofString "heap_ptr") (.val (.word q)) qState)) := by
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
        simp [evalHOLExact, hq_loc, hp_loc_q, isValidValueHOLExact, lookupKvarHOLExact, hp_g,
          shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite, setGlobalHOLFinite,
          evaluateHOLFiniteState_return, sizeOfShapeWithContextHOL]
      rw [heval_end] at hr
      dsimp only at hr
      have hret_eq : ValueHOL.val (.word p) = ret :=
        PanSemResultExact.returned.inj (Option.some.inj (Prod.mk.inj hr).1)
      have hpost_eq := (Prod.mk.inj hr).2.symm
      have hhl : heapLimit = 2952790016 := rfl
      have h423 : (416 + 7 : BitVec 64).toNat = 423 := rfl
      refine ⟨p, q, hret_eq.symm, hp_lk, ?_, ?_, rfl, by omega, ?_⟩
      · rw [hpost_eq]
        simp [emptyLocalsHOLFinite, setGlobalHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      · rw [hpost_eq]; rfl
      · intro hfit
        have hq_and := and_neg8_toNat (p + (416 + 7))
        change q.toNat = _ at hq_and
        have hsum : (p + (416 + 7)).toNat = p.toNat + 423 := by
          rw [BitVec.toNat_add, h423, Nat.mod_eq_of_lt hfit]
        rw [hsum] at hq_and
        exact ⟨by omega, hq_and, by omega⟩

/-- Scoped `.decCall name .one "alloc" [.const 416] cont` step on `GuestInv`. -/
theorem decCall_alloc416_none {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (name : MlS) (cont : ProgHOL 64) (hc : s.code = originalRuntimeCode)
    (hr : evaluateHOLFiniteState s (.decCall name .one (ofString "alloc") [.const 416] cont) =
      (none, post)) :
    ∃ (p q : BitVec 64) (resumed inner : PanSemStateFiniteExact 64 F),
      s.globals.lookup (ofString "heap_ptr") = some (.val (.word p)) ∧
      resumed.globals.lookup (ofString "heap_ptr") = some (.val (.word q)) ∧
      resumed.locals = s.locals.update (name, .val (.word p)) ∧
      resumed.memory = s.memory ∧
      resumed.memaddrs = s.memaddrs ∧
      resumed.shMemaddrs = s.shMemaddrs ∧
      resumed.baseAddr = s.baseAddr ∧
      resumed.code = s.code ∧
      q = (p + (416 + 7)) &&& ((0 : BitVec 64) - 8) ∧
      q.toNat ≤ heapLimit ∧
      (p.toNat + 423 < 2 ^ 64 →
        p.toNat + 416 ≤ q.toNat ∧ q.toNat = (p.toNat + 423) / 8 * 8 ∧ q.toNat % 8 = 0) ∧
      evaluateHOLFiniteState resumed cont = (none, inner) ∧
      post.memory = inner.memory ∧
      post.locals = HolFiniteMapExact.resVarEq inner.locals (name, s.locals.lookup name) := by
  obtain ⟨vals, body, callee, rs, value, bpost, resumed, inner,
    he, hlk, _, hrun, _, hlocals, hcode, hcont, hpost, hresumed, hfinal⟩ :=
    arith_decCall_none_state hr
  have hv : vals = [.val (.word 416)] := by
    simpa [evalListHOLFinite, evalListHOLExact, evalHOLExact] using he.symm
  subst vals
  have hraw : lookupCodeHOLExact originalRuntimeCode.lookup (ofString "alloc") [.val (.word 416)] =
      some (sourceFnBody Guest.Software.guestFn_alloc,
        (fun key => if key = ofString "n" then some (.val (.word 416)) else none), .one) := by
    simp [lookupCodeHOLExact, lookup_alloc_416, shapeEqHOL, shapeOfHOLExact]
  have hlk_eq : PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup
      (ofString "alloc") [.val (.word 416)] =
      some (sourceFnBody Guest.Software.guestFn_alloc,
        HolFiniteMapExact.empty.update (ofString "n", .val (.word 416)), .one) := by
    unfold PanSemStateFiniteExact.lookupCodeHOLFinite
    split
    · rename_i hmiss; rw [hraw] at hmiss; cases hmiss
    · rename_i eb el ers hfound
      have hinj := Option.some.inj (hfound.symm.trans hraw)
      obtain ⟨rfl, hinj2⟩ := Prod.mk.inj hinj
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hinj2
      apply congrArg (fun locals => some (sourceFnBody Guest.Software.guestFn_alloc, locals, ShapeHOL.one))
      apply HolFiniteMapExact.ext
      funext key
      by_cases hk : key = ofString "n"
      · subst key; simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty]
      · simp [hk, Ne.symm hk, HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY]
  have hlk' := hlk
  rw [hc] at hlk'
  change PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup _ _ = _ at hlk'
  rw [hlk_eq] at hlk'
  obtain ⟨rfl, hinj2⟩ := Prod.mk.inj (Option.some.inj hlk')
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hinj2
  let entry := callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "n", .val (.word 416)))
  have hn_lk : entry.locals.lookup (ofString "n") = some (.val (.word 416)) := by
    simp [entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty]
  have hmeta_b := evaluateHOLFiniteState_metadata entry (sourceFnBody Guest.Software.guestFn_alloc)
  have hbase_b := evaluate_baseAddr entry (sourceFnBody Guest.Software.guestFn_alloc)
  rw [hrun] at hmeta_b hbase_b
  obtain ⟨p, q, rfl, hp_g, hq_g, hmem_b, hq_def, hq_le, hq_props⟩ :=
    alloc416_callee_returned entry bpost value hc hn_lk hrun
  refine ⟨p, q, resumed, inner, hp_g, ?_, hlocals, ?_, ?_, ?_, ?_, hcode, hq_def, hq_le, hq_props, hcont, ?_, hpost⟩
  · rw [hresumed]; exact hq_g
  · rw [hresumed]; exact hmem_b
  · rw [hresumed]; exact hmeta_b.2.1
  · rw [hresumed]; exact hmeta_b.2.2.2.1
  · rw [hresumed]; exact hbase_b
  · rw [hfinal]

/-! ### 2. Self-contained write-frame + domain helper for `memzero` and `memcpy` -/

private def noBreakLocal : ProgHOL 64 → Bool
  | .break => false
  | .seq a b | .ite _ a b => noBreakLocal a && noBreakLocal b
  | .assign .local _ _ | .store _ _ | .storeByte _ _ | .skip => true
  | _ => false

private theorem evaluate_noBreakLocal {F : Type} (p : ProgHOL 64) (hp : noBreakLocal p = true)
    (s : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState s p).1 ≠ some .break := by
  cases shape : p with
  | «break» => simp [shape, noBreakLocal] at hp
  | skip => simp [evaluateHOLFiniteState_skip]
  | assign k _ _ =>
    cases k with
    | global => simp [shape, noBreakLocal] at hp
    | «local» => rw [evaluateHOLFiniteState_assign]; split; simp; split <;> simp
  | store _ _ => rw [evaluateHOLFiniteState_store]; split; (split; (split <;> simp); simp); simp
  | storeByte _ _ => rw [evaluateHOLFiniteState_storeByte]; split; (split; (split <;> simp); simp); simp
  | seq a b =>
    have hab : noBreakLocal a = true ∧ noBreakLocal b = true := by
      simpa [shape, noBreakLocal, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_seq_line780]
    have ha := evaluate_noBreakLocal a hab.1 s
    rcases hr : evaluateHOLFiniteState s a with ⟨r, m⟩
    rw [hr] at ha
    cases r with
    | none => exact evaluate_noBreakLocal b hab.2 m
    | some _ => exact ha
  | ite _ a b =>
    have hab : noBreakLocal a = true ∧ noBreakLocal b = true := by
      simpa [shape, noBreakLocal, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_noBreakLocal b hab.2 s
      · exact evaluate_noBreakLocal a hab.1 s
    · simp
  | _ => simp [shape, noBreakLocal] at hp

private def noReturnLocal : ProgHOL 64 → Bool
  | .seq a b | .ite _ a b => noReturnLocal a && noReturnLocal b
  | .while _ a => noReturnLocal a
  | .assign .local _ _ | .store _ _ | .storeByte _ _ | .skip => true
  | _ => false

private theorem evaluate_noReturnLocal {F : Type} (p : ProgHOL 64) (hp : noReturnLocal p = true)
    (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64) :
    (evaluateHOLFiniteState s p).1 ≠ some (.returned v) := by
  cases shape : p with
  | skip => simp [evaluateHOLFiniteState_skip]
  | assign k _ _ =>
    cases k with
    | global => simp [shape, noReturnLocal] at hp
    | «local» => rw [evaluateHOLFiniteState_assign]; split; simp; split <;> simp
  | store _ _ => rw [evaluateHOLFiniteState_store]; split; (split; (split <;> simp); simp); simp
  | storeByte _ _ => rw [evaluateHOLFiniteState_storeByte]; split; (split; (split <;> simp); simp); simp
  | seq a b =>
    have hab : noReturnLocal a = true ∧ noReturnLocal b = true := by
      simpa [shape, noReturnLocal, Bool.and_eq_true] using hp
    have rem := evaluateHOLFiniteState_clock_le s a
    rw [evaluateHOLFiniteState_seq_line780]
    have ha := evaluate_noReturnLocal a hab.1 s v
    rcases hr : evaluateHOLFiniteState s a with ⟨r, m⟩
    rw [hr] at ha rem
    cases r with
    | none => have mclk : m.clock ≤ s.clock := rem; exact evaluate_noReturnLocal b hab.2 m v
    | some _ => exact ha
  | ite _ a b =>
    have hab : noReturnLocal a = true ∧ noReturnLocal b = true := by
      simpa [shape, noReturnLocal, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_noReturnLocal b hab.2 s v
      · exact evaluate_noReturnLocal a hab.1 s v
    · simp
  | «while» cond body =>
    have hb : noReturnLocal body = true := by simpa [shape, noReturnLocal] using hp
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · simp
        · have dec_lt : (decClockHOLFinite s).clock < s.clock := by simp only [decClockHOLFinite]; omega
          dsimp only
          rw [fixClockHOLFinite_evaluateState]
          have ih1 := evaluate_noReturnLocal body hb (decClockHOLFinite s) v
          have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨r1, mid⟩
          rw [hbr] at ih1 rem
          have smaller : mid.clock < s.clock := by change mid.clock ≤ s.clock - 1 at rem; omega
          cases r1 with
          | none => exact evaluate_noReturnLocal (.while cond body) (by simpa [shape] using hp) mid v
          | some r1 =>
            cases r1 with
            | «continue» => exact evaluate_noReturnLocal (.while cond body) (by simpa [shape] using hp) mid v
            | «returned» _ => exact ih1
            | _ => simp
      · simp
    · simp
  | _ => simp [shape, noReturnLocal] at hp
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

/-- Simple write-footprint invariant for `memzero` and `memcpy` (arbitrary alignment):
tracks `globals = s0.globals`, `dst + i ≤ heapEnd`, and that every modified cell `x` satisfies
`panByteAlignHOL dst ≤ x ≤ dst + n - 1` (more precisely: `dst.toNat ≤ x.toNat + 7 ∧ x.toNat < dst0.toNat + n0.toNat`). -/
def ExtentFrame {F : Type} (s0 s : PanSemStateFiniteExact 64 F) (dst0 n0 : BitVec 64) : Prop :=
  s.globals = s0.globals ∧
  ∀ x : BitVec 64, s.memory x ≠ s0.memory x →
    ordinaryDomain x ∧ dst0.toNat ≤ x.toNat + 7 ∧ x.toNat < dst0.toNat + n0.toNat

private theorem extentFrame_refl {F : Type} (s0 : PanSemStateFiniteExact 64 F) (dst0 n0 : BitVec 64) :
    ExtentFrame s0 s0 dst0 n0 :=
  ⟨rfl, fun _ h => absurd rfl h⟩

private theorem extentFrame_locals_clock {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    {dst0 n0 : BitVec 64} (h : ExtentFrame s0 s dst0 n0)
    (loc : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    ExtentFrame s0 { s with locals := loc, clock := k } dst0 n0 :=
  ⟨h.1, h.2⟩

private def WalkInv {F : Type} (s0 : PanSemStateFiniteExact 64 F) (dst0 n0 : BitVec 64)
    (s : PanSemStateFiniteExact 64 F) : Prop :=
  GuestInv s ∧ ExtentFrame s0 s dst0 n0 ∧
  s.locals.lookup (ofString "dst") = some (.val (.word dst0)) ∧
  s.locals.lookup (ofString "n") = some (.val (.word n0)) ∧
  ∃ iw : BitVec 64,
    s.locals.lookup (ofString "i") = some (.val (.word iw)) ∧
    iw.toNat ≤ n0.toNat ∧
    (0 < iw.toNat → sourceBase ≤ dst0.toNat ∧ dst0.toNat + iw.toNat ≤ heapEnd)

private theorem store_one_extent {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    {dst0 n0 : BitVec 64} (hG : GuestInv s) (hef : ExtentFrame s0 s dst0 n0)
    (addrExp valExp : ExpHOL 64) (x : BitVec 64)
    (haddr : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) addrExp =
      some (.val (.word x)))
    (hval_one : ∀ v, @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) valExp =
      some v → ∃ w, v = .val w)
    (hnone : (evaluateHOLFiniteState s (.store addrExp valExp)).1 = none) :
    sourceBase ≤ x.toNat ∧ x.toNat + 8 ≤ heapEnd ∧
    (dst0.toNat ≤ x.toNat ∧ x.toNat + 8 ≤ dst0.toNat + n0.toNat →
      ExtentFrame s0 (evaluateHOLFiniteState s (.store addrExp valExp)).2 dst0 n0) := by
  rw [evaluateHOLFiniteState_store] at hnone ⊢
  rw [haddr] at hnone ⊢
  dsimp only at hnone ⊢
  split at hnone
  · rename_i val hval
    obtain ⟨vw, rfl⟩ := hval_one val hval
    simp only [hval, flattenHOL, panMemStoresHOL, panMemStoreHOL] at hnone ⊢
    by_cases hdom : s.memaddrs x
    · simp only [hdom, ↓reduceIte] at hnone ⊢
      have hord : ordinaryDomain x := by rw [← hG.memaddrs]; exact hdom
      have hdom_ord : x.toNat % 8 = 0 ∧ sourceBase ≤ x.toNat ∧ x.toNat < heapEnd :=
        (ordinaryDomain_iff_local x).mp hord
      have hhe_mod8 : heapEnd % 8 = 0 := by decide
      refine ⟨hdom_ord.2.1, by omega, fun hxin => ⟨hef.1, ?_⟩⟩
      intro a hne
      by_cases hax : a = x
      · subst hax
        exact ⟨hord, by omega, by omega⟩
      · simp only [hax, ↓reduceIte] at hne
        exact hef.2 a hne
    · simp [hdom] at hnone
  · simp at hnone

private theorem storeByte_extent {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    {dst0 n0 : BitVec 64} (hG : GuestInv s) (hef : ExtentFrame s0 s dst0 n0)
    (addrExp valExp : ExpHOL 64) (x : BitVec 64)
    (haddr : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) addrExp =
      some (.val (.word x)))
    (hnone : (evaluateHOLFiniteState s (.storeByte addrExp valExp)).1 = none) :
    sourceBase ≤ x.toNat ∧ x.toNat + 1 ≤ heapEnd ∧
    (dst0.toNat ≤ x.toNat ∧ x.toNat < dst0.toNat + n0.toNat →
      ExtentFrame s0 (evaluateHOLFiniteState s (.storeByte addrExp valExp)).2 dst0 n0) := by
  rw [evaluateHOLFiniteState_storeByte] at hnone ⊢
  rw [haddr] at hnone ⊢
  dsimp only at hnone ⊢
  split at hnone
  · rename_i vw hvw
    split at hnone
    · rename_i mem' hmem
      have hdom : s.memaddrs (panByteAlignHOL x) := by
        by_contra hc
        unfold panMemStoreByteWord8HOL at hmem
        cases s.memory (panByteAlignHOL x) with
        | word _ => simp [hc] at hmem
      have hord : ordinaryDomain (panByteAlignHOL x) := by rw [← hG.memaddrs]; exact hdom
      have hdom_ord : (panByteAlignHOL x).toNat % 8 = 0 ∧
          sourceBase ≤ (panByteAlignHOL x).toNat ∧ (panByteAlignHOL x).toNat < heapEnd :=
        (ordinaryDomain_iff_local _).mp hord
      have hhe_mod8 : heapEnd % 8 = 0 := by decide
      have hal_nat : (panByteAlignHOL x).toNat = x.toNat / 8 * 8 := byteAlign_toNat x
      have hmem_cell : ∀ a : BitVec 64, a ≠ panByteAlignHOL x → mem' a = s.memory a := by
        intro a hne
        have hm' := hmem
        unfold panMemStoreByteWord8HOL at hm'
        cases s.memory (panByteAlignHOL x) with
        | word cell =>
          dsimp only at hm'
          rw [if_pos hdom] at hm'
          injection hm' with hm_eq
          subst hm_eq
          simp [hne]
      refine ⟨by omega, by omega, fun hxin => ⟨hef.1, ?_⟩⟩
      intro a hne
      by_cases hax : a = panByteAlignHOL x
      · subst hax
        exact ⟨hord, by omega, by omega⟩
      · change mem' a ≠ s0.memory a at hne
        rw [hmem_cell a hax] at hne
        exact hef.2 a hne
    · simp at hnone
  · simp at hnone

private theorem eval_add2_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (d i : MlS) (x y : BitVec 64)
    (hx : s.locals.lookup d = some (.val (.word x)))
    (hy : s.locals.lookup i = some (.val (.word y))) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .local d, .var .local i]) = some (.val (.word (x + y))) := by
  simp [evalHOLExact, evalListHOLExact, hx, hy, valueIsWord, valueWord, wordOpHOL, wordOp]

private theorem eval_add3_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (d i : MlS) (x y c : BitVec 64)
    (hx : s.locals.lookup d = some (.val (.word x)))
    (hy : s.locals.lookup i = some (.val (.word y))) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .local d, .var .local i, .const c]) = some (.val (.word (x + y + c))) := by
  simp [evalHOLExact, evalListHOLExact, hx, hy, valueIsWord, valueWord, wordOpHOL, wordOp,
    BitVec.add_assoc]

private theorem eval_load_one_val {F : Type} (s : PanSemStateFiniteExact 64 F)
    (e : ExpHOL 64) (val : ValueHOL 64)
    (he : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.load .one e) = some val) :
    ∃ w, val = .val w := by
  simp only [evalHOLExact] at he
  split at he
  · split at he
    · simp only [memLoadHOLExact] at he
      split at he
      · injection he with hv
        exact ⟨_, hv.symm⟩
      · simp at he
    · simp at he
  · simp at he

private theorem seq_none_split {F : Type} (s : PanSemStateFiniteExact 64 F) (a b : ProgHOL 64)
    (hG : GuestInv s) (dst0 n0 iw : BitVec 64)
    (hd : s.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n0)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iw)))
    (had : avoidsLocal (ofString "dst") a = true)
    (han : avoidsLocal (ofString "n") a = true)
    (hai : avoidsLocal (ofString "i") a = true)
    (h : (evaluateHOLFiniteState s (.seq a b)).1 = none) :
    (evaluateHOLFiniteState s a).1 = none ∧
    ∃ m : PanSemStateFiniteExact 64 F,
      m = (evaluateHOLFiniteState s a).2 ∧
      GuestInv m ∧
      m.locals.lookup (ofString "dst") = some (.val (.word dst0)) ∧
      m.locals.lookup (ofString "n") = some (.val (.word n0)) ∧
      m.locals.lookup (ofString "i") = some (.val (.word iw)) ∧
      (evaluateHOLFiniteState m b).1 = none ∧
      (evaluateHOLFiniteState s (.seq a b)).2 = (evaluateHOLFiniteState m b).2 := by
  have h1 := h
  rw [evaluateHOLFiniteState_seq_line780] at h1
  rcases hr : evaluateHOLFiniteState s a with ⟨r, m⟩
  cases r with
  | none =>
    have h1' : (evaluateHOLFiniteState m b).1 = none := by simpa [hr] using h1
    refine ⟨by simp [hr], m, by simp [hr], ?_, ?_, ?_, ?_, h1', ?_⟩
    · have hm := guestInv_evaluate s a hG; rw [hr] at hm; exact hm
    · have := evaluate_avoidsLocal_flowing (ofString "dst") a had s (by rw [hr]; exact Or.inl rfl)
      rw [hr] at this; exact this.trans hd
    · have := evaluate_avoidsLocal_flowing (ofString "n") a han s (by rw [hr]; exact Or.inl rfl)
      rw [hr] at this; exact this.trans hn
    · have := evaluate_avoidsLocal_flowing (ofString "i") a hai s (by rw [hr]; exact Or.inl rfl)
      rw [hr] at this; exact this.trans hi
    · rw [evaluateHOLFiniteState_seq_line780, hr]
  | some _ => simp [hr] at h1

private theorem step_domain_nowrap (dst0 iw n0 k : BitVec 64)
    (hle : iw.toNat ≤ n0.toNat)
    (hprev : 0 < iw.toNat → sourceBase ≤ dst0.toNat ∧ dst0.toNat + iw.toNat ≤ heapEnd)
    (hcur : sourceBase ≤ (dst0 + iw).toNat ∧ (dst0 + iw).toNat + k.toNat ≤ heapEnd)
    (hk : 0 < k.toNat) (hk32 : k.toNat ≤ 32)
    (hcond : ¬ (n0 < iw + k)) :
    (dst0 + iw).toNat = dst0.toNat + iw.toNat ∧
    (iw + k).toNat = iw.toNat + k.toNat ∧
      (iw + k).toNat ≤ n0.toNat ∧
      sourceBase ≤ dst0.toNat ∧ dst0.toNat + (iw + k).toNat ≤ heapEnd := by
  have hS : sourceBase = 2701131776 := by decide
  have hH : heapEnd = 33806089704 := by decide
  have hdlt := dst0.isLt
  have hilt := iw.isLt
  have hnlt := n0.isLt
  rw [BitVec.lt_def] at hcond
  by_cases hiz : iw.toNat = 0
  · have hi0 : iw = 0 := BitVec.eq_of_toNat_eq hiz
    subst hi0
    have hd0 : dst0 + 0 = dst0 := BitVec.add_zero _
    have hk0 : (0 : BitVec 64) + k = k := BitVec.zero_add _
    rw [hd0] at hcur ⊢
    rw [hk0] at hcond ⊢
    have hz0 : (0 : BitVec 64).toNat = 0 := rfl
    rw [hz0]
    exact ⟨by omega, by omega, by omega, hcur.1, hcur.2⟩
  · obtain ⟨hdlo, hdhi⟩ := hprev (by omega)
    have hadd_di : (dst0 + iw).toNat = dst0.toNat + iw.toNat :=
      BitVec.toNat_add_of_lt (by omega)
    rw [hadd_di] at hcur ⊢
    have hik_lt : iw.toNat + k.toNat < 2 ^ 64 := by omega
    have hadd_ik : (iw + k).toNat = iw.toNat + k.toNat :=
      BitVec.toNat_add_of_lt hik_lt
    rw [hadd_ik] at hcond ⊢
    exact ⟨rfl, rfl, by omega, hdlo, by omega⟩

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
    wordCmpHOL] at he
  intro hlt
  have hnotle : ¬ (iw + k ≤ n0) := by
    rw [BitVec.lt_def] at hlt
    rw [BitVec.le_def]
    omega
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
  simp [evalHOLExact, hn, hi, wordCmpHOL] at he
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
    ¬ (iw < n0) := by
  simp [evalHOLExact, hn, hi, wordCmpHOL] at he
  rw [BitVec.le_def] at he
  rw [BitVec.lt_def]
  omega

private theorem assign_i_walk {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    {dst0 n0 iw k : BitVec 64}
    (hG : GuestInv s) (hef : ExtentFrame s0 s dst0 n0)
    (hd : s.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n0)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iw)))
    (hle : (iw + k).toNat ≤ n0.toNat)
    (hdlo : sourceBase ≤ dst0.toNat) (hdhi : dst0.toNat + (iw + k).toNat ≤ heapEnd) :
    WalkInv s0 dst0 n0
      (evaluateHOLFiniteState s (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const k]))).2 := by
  have hrun : evaluateHOLFiniteState s
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const k])) =
      (none, setVarHOLFinite (ofString "i") (.val (.word (iw + k))) s) := by
    simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hi, wordOpHOL, wordOp,
      valueIsWord, valueWord, lookupKvarHOLExact, isValidValueHOLExact, setKvarHOLFinite,
      shapeOfHOLExact, shapeEqHOL]
  rw [hrun]
  dsimp only
  refine ⟨guestInv_congr (s := s) rfl rfl rfl rfl hG, extentFrame_locals_clock hef _ s.clock,
    ?_, ?_, iw + k, ?_, hle, fun _ => ⟨hdlo, hdhi⟩⟩
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hd, show ofString "i" ≠ ofString "dst" by decide]
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn, show ofString "i" ≠ ofString "n" by decide]
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]

private theorem while_preserve_walk {F : Type} {s0 : PanSemStateFiniteExact 64 F} {dst0 n0 : BitVec 64}
    (cond : ExpHOL 64) (body : ProgHOL 64)
    (hnb : noBreakLocal body = true) (hnc : noTopContinue body = true)
    (hbody : ∀ (s : PanSemStateFiniteExact 64 F) (w : BitVec 64),
      WalkInv s0 dst0 n0 s →
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) cond =
        some (.val (.word w)) → w ≠ 0 →
      (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none →
      WalkInv s0 dst0 n0 (evaluateHOLFiniteState (decClockHOLFinite s) body).2)
    (k : Nat) (s post : PanSemStateFiniteExact 64 F) (hk : s.clock ≤ k)
    (hinv : WalkInv s0 dst0 n0 s)
    (hrun : evaluateHOLFiniteState s (.while cond body) = (none, post)) :
    WalkInv s0 dst0 n0 post ∧
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
      · rename_i hcw0
        have hw0 : cw = 0 := Classical.not_not.mp hcw0
        subst hw0
        injection hrun with _ hp
        subst hp
        exact ⟨hinv, hcond⟩
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
          have nb := evaluate_noBreakLocal body hnb (decClockHOLFinite s)
          have nc := evaluate_noTopContinue body hnc (decClockHOLFinite s)
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨r1, mid⟩
          rw [hbr] at hrun rem nb nc
          cases r1 with
          | none =>
            have hmid : WalkInv s0 dst0 n0 mid := by
              have hb := hbody s cw hinv hcond hnz (by rw [hbr])
              rw [hbr] at hb; exact hb
            exact ih mid (by change mid.clock ≤ s.clock - 1 at rem; omega) hmid hrun
          | some r1 =>
            cases r1 with
            | «continue» => exact absurd rfl nc
            | «break» => exact absurd rfl nb
            | _ => simp at hrun
      · rename_i hcw0
        have hw0 : cw = 0 := Classical.not_not.mp hcw0
        subst hw0
        injection hrun with _ hp
        subst hp
        exact ⟨hinv, hcond⟩
    · simp at hrun

private theorem step_walk_memzero1 {F : Type} {s0 : PanSemStateFiniteExact 64 F} {dst0 n0 : BitVec 64}
    (s : PanSemStateFiniteExact 64 F) (w : BitVec 64)
    (hinv : WalkInv s0 dst0 n0 s)
    (hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .notLower (.var .local (ofString "n"))
        (.op .add [.var .local (ofString "i"), .const 32])) = some (.val (.word w)))
    (hw : w ≠ 0) :
    let body := (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) (.const 0))
        (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 8]) (.const 0))
          (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 16]) (.const 0))
            (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 24]) (.const 0))
              (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 32]))))))
    (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none →
      WalkInv s0 dst0 n0 (evaluateHOLFiniteState (decClockHOLFinite s) body).2 := by
  intro body hnone
  obtain ⟨hG, hef, hdst, hn, iw, hi, hle, hdom⟩ := hinv
  let sd := decClockHOLFinite s
  have hGd : GuestInv sd := guestInv_congr (s := s) rfl rfl rfl rfl hG
  have hefd : ExtentFrame s0 sd dst0 n0 := extentFrame_locals_clock hef s.locals (s.clock - 1)
  have hnl := eval_notLower_true s n0 iw 32 w hn hi hcond hw
  have hH : heapEnd = 33806089704 := by decide
  have hv0 : ∀ (st : PanSemStateFiniteExact 64 F) v,
      @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a)) (.const 0) = some v →
      ∃ u, v = .val u := fun _ _ h => ⟨.word 0, (Option.some.inj h).symm⟩
  obtain ⟨hs0, s1, hs1_eq, hG1, hd1, hn1, hi1, hr1, heq1⟩ :=
    seq_none_split sd _ _ hGd dst0 n0 iw hdst hn hi rfl rfl rfl hnone
  obtain ⟨hs8, s2, hs2_eq, hG2, hd2, hn2, hi2, hr2, heq2⟩ :=
    seq_none_split s1 _ _ hG1 dst0 n0 iw hd1 hn1 hi1 rfl rfl rfl hr1
  obtain ⟨hs16, s3, hs3_eq, hG3, hd3, hn3, hi3, hr3, heq3⟩ :=
    seq_none_split s2 _ _ hG2 dst0 n0 iw hd2 hn2 hi2 rfl rfl rfl hr2
  obtain ⟨hs24, s4, hs4_eq, hG4, hd4, hn4, hi4, _, heq4⟩ :=
    seq_none_split s3 _ _ hG3 dst0 n0 iw hd3 hn3 hi3 rfl rfl rfl hr3
  have st0 := store_one_extent hGd hefd _ _ (dst0 + iw) (eval_add2_locals sd _ _ dst0 iw hdst hi) (hv0 sd) hs0
  have hd8_raw := store_one_extent hG1 (extentFrame_refl s1 0 0) _ _ (dst0 + iw + 8)
    (eval_add3_locals s1 _ _ dst0 iw 8 hd1 hi1) (hv0 s1) hs8
  have hd16_raw := store_one_extent hG2 (extentFrame_refl s2 0 0) _ _ (dst0 + iw + 16)
    (eval_add3_locals s2 _ _ dst0 iw 16 hd2 hi2) (hv0 s2) hs16
  have hd24_raw := store_one_extent hG3 (extentFrame_refl s3 0 0) _ _ (dst0 + iw + 24)
    (eval_add3_locals s3 _ _ dst0 iw 24 hd3 hi3) (hv0 s3) hs24
  have a8 : (dst0 + iw + 8).toNat = (dst0 + iw).toNat + 8 :=
    BitVec.toNat_add_of_lt (by have := st0.2.1; change (dst0 + iw).toNat + 8 < 2 ^ 64; omega)
  have a16 : (dst0 + iw + 16).toNat = (dst0 + iw).toNat + 16 := by
    have : (dst0 + iw).toNat + 8 + 8 ≤ heapEnd := by rw [← a8]; exact hd8_raw.2.1
    exact BitVec.toNat_add_of_lt (by change (dst0 + iw).toNat + 16 < 2 ^ 64; omega)
  have a24 : (dst0 + iw + 24).toNat = (dst0 + iw).toNat + 24 := by
    have : (dst0 + iw).toNat + 16 + 8 ≤ heapEnd := by rw [← a16]; exact hd16_raw.2.1
    exact BitVec.toNat_add_of_lt (by change (dst0 + iw).toNat + 24 < 2 ^ 64; omega)
  have hcur32 : sourceBase ≤ (dst0 + iw).toNat ∧ (dst0 + iw).toNat + (32 : BitVec 64).toNat ≤ heapEnd := by
    refine ⟨st0.1, ?_⟩
    have := hd24_raw.2.1; rw [a24] at this; change (dst0 + iw).toNat + 32 ≤ heapEnd; omega
  obtain ⟨hdi_eq, hik_eq, hle_ik, hdlo, hdhi⟩ :=
    step_domain_nowrap dst0 iw n0 32 hle hdom hcur32 (by decide) (by decide) hnl
  have hk32_val : (32 : BitVec 64).toNat = 32 := rfl
  have hef1 : ExtentFrame s0 s1 dst0 n0 := by rw [hs1_eq]; exact st0.2.2 ⟨by omega, by omega⟩
  have hef2 : ExtentFrame s0 s2 dst0 n0 := by
    rw [hs2_eq]
    exact (store_one_extent hG1 hef1 _ _ (dst0 + iw + 8)
      (eval_add3_locals s1 _ _ dst0 iw 8 hd1 hi1) (hv0 s1) hs8).2.2 ⟨by omega, by omega⟩
  have hef3 : ExtentFrame s0 s3 dst0 n0 := by
    rw [hs3_eq]
    exact (store_one_extent hG2 hef2 _ _ (dst0 + iw + 16)
      (eval_add3_locals s2 _ _ dst0 iw 16 hd2 hi2) (hv0 s2) hs16).2.2 ⟨by omega, by omega⟩
  have hef4 : ExtentFrame s0 s4 dst0 n0 := by
    rw [hs4_eq]
    exact (store_one_extent hG3 hef3 _ _ (dst0 + iw + 24)
      (eval_add3_locals s3 _ _ dst0 iw 24 hd3 hi3) (hv0 s3) hs24).2.2 ⟨by omega, by omega⟩
  change WalkInv s0 dst0 n0 (evaluateHOLFiniteState sd body).2
  rw [heq1, heq2, heq3, heq4]
  exact assign_i_walk hG4 hef4 hd4 hn4 hi4 hle_ik hdlo hdhi

private theorem step_walk_memzero2 {F : Type} {s0 : PanSemStateFiniteExact 64 F} {dst0 n0 : BitVec 64}
    (s : PanSemStateFiniteExact 64 F) (w : BitVec 64)
    (hinv : WalkInv s0 dst0 n0 s)
    (hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .notLower (.var .local (ofString "n"))
        (.op .add [.var .local (ofString "i"), .const 8])) = some (.val (.word w)))
    (hw : w ≠ 0) :
    let body := (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) (.const 0))
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 8])))
    (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none →
      WalkInv s0 dst0 n0 (evaluateHOLFiniteState (decClockHOLFinite s) body).2 := by
  intro body hnone
  obtain ⟨hG, hef, hdst, hn, iw, hi, hle, hdom⟩ := hinv
  let sd := decClockHOLFinite s
  have hGd : GuestInv sd := guestInv_congr (s := s) rfl rfl rfl rfl hG
  have hefd : ExtentFrame s0 sd dst0 n0 := extentFrame_locals_clock hef s.locals (s.clock - 1)
  have hnl := eval_notLower_true s n0 iw 8 w hn hi hcond hw
  have hv0 : ∀ (st : PanSemStateFiniteExact 64 F) v,
      @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a)) (.const 0) = some v →
      ∃ u, v = .val u := fun _ _ h => ⟨.word 0, (Option.some.inj h).symm⟩
  obtain ⟨hs0, s1, hs1_eq, hG1, hd1, hn1, hi1, _, heq1⟩ :=
    seq_none_split sd _ _ hGd dst0 n0 iw hdst hn hi rfl rfl rfl hnone
  have st0 := store_one_extent hGd hefd _ _ (dst0 + iw) (eval_add2_locals sd _ _ dst0 iw hdst hi) (hv0 sd) hs0
  obtain ⟨hdi_eq, hik_eq, hle_ik, hdlo, hdhi⟩ :=
    step_domain_nowrap dst0 iw n0 8 hle hdom ⟨st0.1, st0.2.1⟩ (by decide) (by decide) hnl
  have hk8_val : (8 : BitVec 64).toNat = 8 := rfl
  have hef1 : ExtentFrame s0 s1 dst0 n0 := by rw [hs1_eq]; exact st0.2.2 ⟨by omega, by omega⟩
  change WalkInv s0 dst0 n0 (evaluateHOLFiniteState sd body).2
  rw [heq1]
  exact assign_i_walk hG1 hef1 hd1 hn1 hi1 hle_ik hdlo hdhi

private theorem step_walk_memzero3 {F : Type} {s0 : PanSemStateFiniteExact 64 F} {dst0 n0 : BitVec 64}
    (s : PanSemStateFiniteExact 64 F) (w : BitVec 64)
    (hinv : WalkInv s0 dst0 n0 s)
    (hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .notLower (.var .local (ofString "n"))
        (.op .add [.var .local (ofString "i"), .const 8])) = some (.val (.word w)))
    (hw : w ≠ 0) :
    let body := (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) (.const 0))
        (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 1]) (.const 0))
          (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 2]) (.const 0))
            (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 3]) (.const 0))
              (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 4]) (.const 0))
                 (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 5]) (.const 0))
                   (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 6]) (.const 0))
                     (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 7]) (.const 0))
                       (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 8]))))))))))
    (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none →
      WalkInv s0 dst0 n0 (evaluateHOLFiniteState (decClockHOLFinite s) body).2 := by
  intro body hnone
  obtain ⟨hG, hef, hdst, hn, iw, hi, hle, hdom⟩ := hinv
  let sd := decClockHOLFinite s
  have hGd : GuestInv sd := guestInv_congr (s := s) rfl rfl rfl rfl hG
  have hefd : ExtentFrame s0 sd dst0 n0 := extentFrame_locals_clock hef s.locals (s.clock - 1)
  have hnl := eval_notLower_true s n0 iw 8 w hn hi hcond hw
  have hH : heapEnd = 33806089704 := by decide
  obtain ⟨hs0, s1, hs1_eq, hG1, hd1, hn1, hi1, hr1, heq1⟩ :=
    seq_none_split sd _ _ hGd dst0 n0 iw hdst hn hi rfl rfl rfl hnone
  obtain ⟨hs1, s2, hs2_eq, hG2, hd2, hn2, hi2, hr2, heq2⟩ :=
    seq_none_split s1 _ _ hG1 dst0 n0 iw hd1 hn1 hi1 rfl rfl rfl hr1
  obtain ⟨hs2, s3, hs3_eq, hG3, hd3, hn3, hi3, hr3, heq3⟩ :=
    seq_none_split s2 _ _ hG2 dst0 n0 iw hd2 hn2 hi2 rfl rfl rfl hr2
  obtain ⟨hs3, s4, hs4_eq, hG4, hd4, hn4, hi4, hr4, heq4⟩ :=
    seq_none_split s3 _ _ hG3 dst0 n0 iw hd3 hn3 hi3 rfl rfl rfl hr3
  obtain ⟨hs4, s5, hs5_eq, hG5, hd5, hn5, hi5, hr5, heq5⟩ :=
    seq_none_split s4 _ _ hG4 dst0 n0 iw hd4 hn4 hi4 rfl rfl rfl hr4
  obtain ⟨hs5, s6, hs6_eq, hG6, hd6, hn6, hi5_6, hr6, heq6⟩ :=
    seq_none_split s5 _ _ hG5 dst0 n0 iw hd5 hn5 hi5 rfl rfl rfl hr5
  obtain ⟨hs6, s7, hs7_eq, hG7, hd7, hn7, hi7, hr7, heq7⟩ :=
    seq_none_split s6 _ _ hG6 dst0 n0 iw hd6 hn6 hi5_6 rfl rfl rfl hr6
  obtain ⟨hs7, s8, hs8_eq, hG8, hd8, hn8, hi8, _, heq8⟩ :=
    seq_none_split s7 _ _ hG7 dst0 n0 iw hd7 hn7 hi7 rfl rfl rfl hr7
  have b0 := storeByte_extent hGd hefd _ _ (dst0 + iw) (eval_add2_locals sd _ _ dst0 iw hdst hi) hs0
  have b7_raw := storeByte_extent hG7 (extentFrame_refl s7 0 0) _ _ (dst0 + iw + 7)
    (eval_add3_locals s7 _ _ dst0 iw 7 hd7 hi7) hs7
  have a1 : (dst0 + iw + 1).toNat = (dst0 + iw).toNat + 1 :=
    BitVec.toNat_add_of_lt (by have := b0.2.1; change (dst0 + iw).toNat + 1 < 2 ^ 64; omega)
  have a2 : (dst0 + iw + 2).toNat = (dst0 + iw).toNat + 2 :=
    BitVec.toNat_add_of_lt (by have := b0.2.1; change (dst0 + iw).toNat + 2 < 2 ^ 64; omega)
  have a3 : (dst0 + iw + 3).toNat = (dst0 + iw).toNat + 3 :=
    BitVec.toNat_add_of_lt (by have := b0.2.1; change (dst0 + iw).toNat + 3 < 2 ^ 64; omega)
  have a4 : (dst0 + iw + 4).toNat = (dst0 + iw).toNat + 4 :=
    BitVec.toNat_add_of_lt (by have := b0.2.1; change (dst0 + iw).toNat + 4 < 2 ^ 64; omega)
  have a5 : (dst0 + iw + 5).toNat = (dst0 + iw).toNat + 5 :=
    BitVec.toNat_add_of_lt (by have := b0.2.1; change (dst0 + iw).toNat + 5 < 2 ^ 64; omega)
  have a6 : (dst0 + iw + 6).toNat = (dst0 + iw).toNat + 6 :=
    BitVec.toNat_add_of_lt (by have := b0.2.1; change (dst0 + iw).toNat + 6 < 2 ^ 64; omega)
  have a7 : (dst0 + iw + 7).toNat = (dst0 + iw).toNat + 7 :=
    BitVec.toNat_add_of_lt (by have := b0.2.1; change (dst0 + iw).toNat + 7 < 2 ^ 64; omega)
  have hcur8 : sourceBase ≤ (dst0 + iw).toNat ∧ (dst0 + iw).toNat + (8 : BitVec 64).toNat ≤ heapEnd := by
    refine ⟨b0.1, ?_⟩
    have := b7_raw.2.1; rw [a7] at this; change (dst0 + iw).toNat + 8 ≤ heapEnd; omega
  obtain ⟨hdi_eq, hik_eq, hle_ik, hdlo, hdhi⟩ :=
    step_domain_nowrap dst0 iw n0 8 hle hdom hcur8 (by decide) (by decide) hnl
  have hk8_val : (8 : BitVec 64).toNat = 8 := rfl
  have hef1 : ExtentFrame s0 s1 dst0 n0 := by rw [hs1_eq]; exact b0.2.2 ⟨by omega, by omega⟩
  have hef2 : ExtentFrame s0 s2 dst0 n0 := by
    rw [hs2_eq]; exact (storeByte_extent hG1 hef1 _ _ (dst0 + iw + 1) (eval_add3_locals s1 _ _ dst0 iw 1 hd1 hi1) hs1).2.2 ⟨by omega, by omega⟩
  have hef3 : ExtentFrame s0 s3 dst0 n0 := by
    rw [hs3_eq]; exact (storeByte_extent hG2 hef2 _ _ (dst0 + iw + 2) (eval_add3_locals s2 _ _ dst0 iw 2 hd2 hi2) hs2).2.2 ⟨by omega, by omega⟩
  have hef4 : ExtentFrame s0 s4 dst0 n0 := by
    rw [hs4_eq]; exact (storeByte_extent hG3 hef3 _ _ (dst0 + iw + 3) (eval_add3_locals s3 _ _ dst0 iw 3 hd3 hi3) hs3).2.2 ⟨by omega, by omega⟩
  have hef5 : ExtentFrame s0 s5 dst0 n0 := by
    rw [hs5_eq]; exact (storeByte_extent hG4 hef4 _ _ (dst0 + iw + 4) (eval_add3_locals s4 _ _ dst0 iw 4 hd4 hi4) hs4).2.2 ⟨by omega, by omega⟩
  have hef6 : ExtentFrame s0 s6 dst0 n0 := by
    rw [hs6_eq]; exact (storeByte_extent hG5 hef5 _ _ (dst0 + iw + 5) (eval_add3_locals s5 _ _ dst0 iw 5 hd5 hi5) hs5).2.2 ⟨by omega, by omega⟩
  have hef7 : ExtentFrame s0 s7 dst0 n0 := by
    rw [hs7_eq]; exact (storeByte_extent hG6 hef6 _ _ (dst0 + iw + 6) (eval_add3_locals s6 _ _ dst0 iw 6 hd6 hi5_6) hs6).2.2 ⟨by omega, by omega⟩
  have hef8 : ExtentFrame s0 s8 dst0 n0 := by
    rw [hs8_eq]; exact (storeByte_extent hG7 hef7 _ _ (dst0 + iw + 7) (eval_add3_locals s7 _ _ dst0 iw 7 hd7 hi7) hs7).2.2 ⟨by omega, by omega⟩
  change WalkInv s0 dst0 n0 (evaluateHOLFiniteState sd body).2
  rw [heq1, heq2, heq3, heq4, heq5, heq6, heq7, heq8]
  exact assign_i_walk hG8 hef8 hd8 hn8 hi8 hle_ik hdlo hdhi

private theorem step_walk_memzero4 {F : Type} {s0 : PanSemStateFiniteExact 64 F} {dst0 n0 : BitVec 64}
    (s : PanSemStateFiniteExact 64 F) (w : BitVec 64)
    (hinv : WalkInv s0 dst0 n0 s)
    (hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) =
        some (.val (.word w)))
    (hw : w ≠ 0) :
    let body := (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) (.const 0))
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])))
    (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none →
      WalkInv s0 dst0 n0 (evaluateHOLFiniteState (decClockHOLFinite s) body).2 := by
  intro body hnone
  obtain ⟨hG, hef, hdst, hn, iw, hi, hle, hdom⟩ := hinv
  let sd := decClockHOLFinite s
  have hGd : GuestInv sd := guestInv_congr (s := s) rfl rfl rfl rfl hG
  have hefd : ExtentFrame s0 sd dst0 n0 := extentFrame_locals_clock hef s.locals (s.clock - 1)
  have hlt := eval_lower_true s n0 iw w hn hi hcond hw
  rw [BitVec.lt_def] at hlt
  obtain ⟨hs0, s1, hs1_eq, hG1, hd1, hn1, hi1, _, heq1⟩ :=
    seq_none_split sd _ _ hGd dst0 n0 iw hdst hn hi rfl rfl rfl hnone
  have b0 := storeByte_extent hGd hefd _ _ (dst0 + iw) (eval_add2_locals sd _ _ dst0 iw hdst hi) hs0
  have hnlt := n0.isLt
  have ha1 : (iw + 1).toNat = iw.toNat + 1 :=
    BitVec.toNat_add_of_lt (by change iw.toNat + 1 < 2 ^ 64; omega)
  have hnl : ¬ (n0 < iw + 1) := by rw [BitVec.lt_def, ha1]; omega
  obtain ⟨hdi_eq, hik_eq, hle_ik, hdlo, hdhi⟩ :=
    step_domain_nowrap dst0 iw n0 1 hle hdom ⟨b0.1, b0.2.1⟩ (by decide) (by decide) hnl
  have hk1_val : (1 : BitVec 64).toNat = 1 := rfl
  have hef1 : ExtentFrame s0 s1 dst0 n0 := by rw [hs1_eq]; exact b0.2.2 ⟨by omega, by omega⟩
  change WalkInv s0 dst0 n0 (evaluateHOLFiniteState sd body).2
  rw [heq1]
  exact assign_i_walk hG1 hef1 hd1 hn1 hi1 hle_ik hdlo hdhi

private theorem step_walk_memcpy1 {F : Type} {s0 : PanSemStateFiniteExact 64 F} {dst0 n0 : BitVec 64}
    (s : PanSemStateFiniteExact 64 F) (w : BitVec 64)
    (hinv : WalkInv s0 dst0 n0 s)
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
      WalkInv s0 dst0 n0 (evaluateHOLFiniteState (decClockHOLFinite s) body).2 := by
  intro body hnone
  obtain ⟨hG, hef, hdst, hn, iw, hi, hle, hdom⟩ := hinv
  let sd := decClockHOLFinite s
  have hGd : GuestInv sd := guestInv_congr (s := s) rfl rfl rfl rfl hG
  have hefd : ExtentFrame s0 sd dst0 n0 := extentFrame_locals_clock hef s.locals (s.clock - 1)
  have hnl := eval_notLower_true s n0 iw 32 w hn hi hcond hw
  have hH : heapEnd = 33806089704 := by decide
  obtain ⟨hs0, s1, hs1_eq, hG1, hd1, hn1, hi1, hr1, heq1⟩ :=
    seq_none_split sd _ _ hGd dst0 n0 iw hdst hn hi rfl rfl rfl hnone
  obtain ⟨hs8, s2, hs2_eq, hG2, hd2, hn2, hi2, hr2, heq2⟩ :=
    seq_none_split s1 _ _ hG1 dst0 n0 iw hd1 hn1 hi1 rfl rfl rfl hr1
  obtain ⟨hs16, s3, hs3_eq, hG3, hd3, hn3, hi3, hr3, heq3⟩ :=
    seq_none_split s2 _ _ hG2 dst0 n0 iw hd2 hn2 hi2 rfl rfl rfl hr2
  obtain ⟨hs24, s4, hs4_eq, hG4, hd4, hn4, hi4, _, heq4⟩ :=
    seq_none_split s3 _ _ hG3 dst0 n0 iw hd3 hn3 hi3 rfl rfl rfl hr3
  have st0 := store_one_extent hGd hefd _ _ (dst0 + iw) (eval_add2_locals sd _ _ dst0 iw hdst hi) (eval_load_one_val sd _) hs0
  have hd8_raw := store_one_extent hG1 (extentFrame_refl s1 0 0) _ _ (dst0 + iw + 8)
    (eval_add3_locals s1 _ _ dst0 iw 8 hd1 hi1) (eval_load_one_val s1 _) hs8
  have hd16_raw := store_one_extent hG2 (extentFrame_refl s2 0 0) _ _ (dst0 + iw + 16)
    (eval_add3_locals s2 _ _ dst0 iw 16 hd2 hi2) (eval_load_one_val s2 _) hs16
  have hd24_raw := store_one_extent hG3 (extentFrame_refl s3 0 0) _ _ (dst0 + iw + 24)
    (eval_add3_locals s3 _ _ dst0 iw 24 hd3 hi3) (eval_load_one_val s3 _) hs24
  have a8 : (dst0 + iw + 8).toNat = (dst0 + iw).toNat + 8 :=
    BitVec.toNat_add_of_lt (by have := st0.2.1; change (dst0 + iw).toNat + 8 < 2 ^ 64; omega)
  have a16 : (dst0 + iw + 16).toNat = (dst0 + iw).toNat + 16 := by
    have : (dst0 + iw).toNat + 8 + 8 ≤ heapEnd := by rw [← a8]; exact hd8_raw.2.1
    exact BitVec.toNat_add_of_lt (by change (dst0 + iw).toNat + 16 < 2 ^ 64; omega)
  have a24 : (dst0 + iw + 24).toNat = (dst0 + iw).toNat + 24 := by
    have : (dst0 + iw).toNat + 16 + 8 ≤ heapEnd := by rw [← a16]; exact hd16_raw.2.1
    exact BitVec.toNat_add_of_lt (by change (dst0 + iw).toNat + 24 < 2 ^ 64; omega)
  have hcur32 : sourceBase ≤ (dst0 + iw).toNat ∧ (dst0 + iw).toNat + (32 : BitVec 64).toNat ≤ heapEnd := by
    refine ⟨st0.1, ?_⟩
    have := hd24_raw.2.1; rw [a24] at this; change (dst0 + iw).toNat + 32 ≤ heapEnd; omega
  obtain ⟨hdi_eq, hik_eq, hle_ik, hdlo, hdhi⟩ :=
    step_domain_nowrap dst0 iw n0 32 hle hdom hcur32 (by decide) (by decide) hnl
  have hk32_val : (32 : BitVec 64).toNat = 32 := rfl
  have hef1 : ExtentFrame s0 s1 dst0 n0 := by rw [hs1_eq]; exact st0.2.2 ⟨by omega, by omega⟩
  have hef2 : ExtentFrame s0 s2 dst0 n0 := by
    rw [hs2_eq]
    exact (store_one_extent hG1 hef1 _ _ (dst0 + iw + 8)
      (eval_add3_locals s1 _ _ dst0 iw 8 hd1 hi1) (eval_load_one_val s1 _) hs8).2.2 ⟨by omega, by omega⟩
  have hef3 : ExtentFrame s0 s3 dst0 n0 := by
    rw [hs3_eq]
    exact (store_one_extent hG2 hef2 _ _ (dst0 + iw + 16)
      (eval_add3_locals s2 _ _ dst0 iw 16 hd2 hi2) (eval_load_one_val s2 _) hs16).2.2 ⟨by omega, by omega⟩
  have hef4 : ExtentFrame s0 s4 dst0 n0 := by
    rw [hs4_eq]
    exact (store_one_extent hG3 hef3 _ _ (dst0 + iw + 24)
      (eval_add3_locals s3 _ _ dst0 iw 24 hd3 hi3) (eval_load_one_val s3 _) hs24).2.2 ⟨by omega, by omega⟩
  change WalkInv s0 dst0 n0 (evaluateHOLFiniteState sd body).2
  rw [heq1, heq2, heq3, heq4]
  exact assign_i_walk hG4 hef4 hd4 hn4 hi4 hle_ik hdlo hdhi

private theorem step_walk_memcpy2 {F : Type} {s0 : PanSemStateFiniteExact 64 F} {dst0 n0 : BitVec 64}
    (s : PanSemStateFiniteExact 64 F) (w : BitVec 64)
    (hinv : WalkInv s0 dst0 n0 s)
    (hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .notLower (.var .local (ofString "n"))
        (.op .add [.var .local (ofString "i"), .const 8])) = some (.val (.word w)))
    (hw : w ≠ 0) :
    let body := (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
          (.load .one (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])))
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 8])))
    (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none →
      WalkInv s0 dst0 n0 (evaluateHOLFiniteState (decClockHOLFinite s) body).2 := by
  intro body hnone
  obtain ⟨hG, hef, hdst, hn, iw, hi, hle, hdom⟩ := hinv
  let sd := decClockHOLFinite s
  have hGd : GuestInv sd := guestInv_congr (s := s) rfl rfl rfl rfl hG
  have hefd : ExtentFrame s0 sd dst0 n0 := extentFrame_locals_clock hef s.locals (s.clock - 1)
  have hnl := eval_notLower_true s n0 iw 8 w hn hi hcond hw
  obtain ⟨hs0, s1, hs1_eq, hG1, hd1, hn1, hi1, _, heq1⟩ :=
    seq_none_split sd _ _ hGd dst0 n0 iw hdst hn hi rfl rfl rfl hnone
  have st0 := store_one_extent hGd hefd _ _ (dst0 + iw) (eval_add2_locals sd _ _ dst0 iw hdst hi) (eval_load_one_val sd _) hs0
  obtain ⟨hdi_eq, hik_eq, hle_ik, hdlo, hdhi⟩ :=
    step_domain_nowrap dst0 iw n0 8 hle hdom ⟨st0.1, st0.2.1⟩ (by decide) (by decide) hnl
  have hk8_val : (8 : BitVec 64).toNat = 8 := rfl
  have hef1 : ExtentFrame s0 s1 dst0 n0 := by rw [hs1_eq]; exact st0.2.2 ⟨by omega, by omega⟩
  change WalkInv s0 dst0 n0 (evaluateHOLFiniteState sd body).2
  rw [heq1]
  exact assign_i_walk hG1 hef1 hd1 hn1 hi1 hle_ik hdlo hdhi

private theorem step_walk_memcpy3 {F : Type} {s0 : PanSemStateFiniteExact 64 F} {dst0 n0 : BitVec 64}
    (s : PanSemStateFiniteExact 64 F) (w : BitVec 64)
    (hinv : WalkInv s0 dst0 n0 s)
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
      WalkInv s0 dst0 n0 (evaluateHOLFiniteState (decClockHOLFinite s) body).2 := by
  intro body hnone
  obtain ⟨hG, hef, hdst, hn, iw, hi, hle, hdom⟩ := hinv
  let sd := decClockHOLFinite s
  have hGd : GuestInv sd := guestInv_congr (s := s) rfl rfl rfl rfl hG
  have hefd : ExtentFrame s0 sd dst0 n0 := extentFrame_locals_clock hef s.locals (s.clock - 1)
  have hnl := eval_notLower_true s n0 iw 8 w hn hi hcond hw
  have hH : heapEnd = 33806089704 := by decide
  obtain ⟨hs0, s1, hs1_eq, hG1, hd1, hn1, hi1, hr1, heq1⟩ :=
    seq_none_split sd _ _ hGd dst0 n0 iw hdst hn hi rfl rfl rfl hnone
  obtain ⟨hs1, s2, hs2_eq, hG2, hd2, hn2, hi2, hr2, heq2⟩ :=
    seq_none_split s1 _ _ hG1 dst0 n0 iw hd1 hn1 hi1 rfl rfl rfl hr1
  obtain ⟨hs2, s3, hs3_eq, hG3, hd3, hn3, hi3, hr3, heq3⟩ :=
    seq_none_split s2 _ _ hG2 dst0 n0 iw hd2 hn2 hi2 rfl rfl rfl hr2
  obtain ⟨hs3, s4, hs4_eq, hG4, hd4, hn4, hi4, hr4, heq4⟩ :=
    seq_none_split s3 _ _ hG3 dst0 n0 iw hd3 hn3 hi3 rfl rfl rfl hr3
  obtain ⟨hs4, s5, hs5_eq, hG5, hd5, hn5, hi5, hr5, heq5⟩ :=
    seq_none_split s4 _ _ hG4 dst0 n0 iw hd4 hn4 hi4 rfl rfl rfl hr4
  obtain ⟨hs5, s6, hs6_eq, hG6, hd6, hn6, hi5_6, hr6, heq6⟩ :=
    seq_none_split s5 _ _ hG5 dst0 n0 iw hd5 hn5 hi5 rfl rfl rfl hr5
  obtain ⟨hs6, s7, hs7_eq, hG7, hd7, hn7, hi7, hr7, heq7⟩ :=
    seq_none_split s6 _ _ hG6 dst0 n0 iw hd6 hn6 hi5_6 rfl rfl rfl hr6
  obtain ⟨hs7, s8, hs8_eq, hG8, hd8, hn8, hi8, _, heq8⟩ :=
    seq_none_split s7 _ _ hG7 dst0 n0 iw hd7 hn7 hi7 rfl rfl rfl hr7
  have b0 := storeByte_extent hGd hefd _ _ (dst0 + iw) (eval_add2_locals sd _ _ dst0 iw hdst hi) hs0
  have b7_raw := storeByte_extent hG7 (extentFrame_refl s7 0 0) _ _ (dst0 + iw + 7)
    (eval_add3_locals s7 _ _ dst0 iw 7 hd7 hi7) hs7
  have a1 : (dst0 + iw + 1).toNat = (dst0 + iw).toNat + 1 :=
    BitVec.toNat_add_of_lt (by have := b0.2.1; change (dst0 + iw).toNat + 1 < 2 ^ 64; omega)
  have a2 : (dst0 + iw + 2).toNat = (dst0 + iw).toNat + 2 :=
    BitVec.toNat_add_of_lt (by have := b0.2.1; change (dst0 + iw).toNat + 2 < 2 ^ 64; omega)
  have a3 : (dst0 + iw + 3).toNat = (dst0 + iw).toNat + 3 :=
    BitVec.toNat_add_of_lt (by have := b0.2.1; change (dst0 + iw).toNat + 3 < 2 ^ 64; omega)
  have a4 : (dst0 + iw + 4).toNat = (dst0 + iw).toNat + 4 :=
    BitVec.toNat_add_of_lt (by have := b0.2.1; change (dst0 + iw).toNat + 4 < 2 ^ 64; omega)
  have a5 : (dst0 + iw + 5).toNat = (dst0 + iw).toNat + 5 :=
    BitVec.toNat_add_of_lt (by have := b0.2.1; change (dst0 + iw).toNat + 5 < 2 ^ 64; omega)
  have a6 : (dst0 + iw + 6).toNat = (dst0 + iw).toNat + 6 :=
    BitVec.toNat_add_of_lt (by have := b0.2.1; change (dst0 + iw).toNat + 6 < 2 ^ 64; omega)
  have a7 : (dst0 + iw + 7).toNat = (dst0 + iw).toNat + 7 :=
    BitVec.toNat_add_of_lt (by have := b0.2.1; change (dst0 + iw).toNat + 7 < 2 ^ 64; omega)
  have hcur8 : sourceBase ≤ (dst0 + iw).toNat ∧ (dst0 + iw).toNat + (8 : BitVec 64).toNat ≤ heapEnd := by
    refine ⟨b0.1, ?_⟩
    have := b7_raw.2.1; rw [a7] at this; change (dst0 + iw).toNat + 8 ≤ heapEnd; omega
  obtain ⟨hdi_eq, hik_eq, hle_ik, hdlo, hdhi⟩ :=
    step_domain_nowrap dst0 iw n0 8 hle hdom hcur8 (by decide) (by decide) hnl
  have hk8_val : (8 : BitVec 64).toNat = 8 := rfl
  have hef1 : ExtentFrame s0 s1 dst0 n0 := by rw [hs1_eq]; exact b0.2.2 ⟨by omega, by omega⟩
  have hef2 : ExtentFrame s0 s2 dst0 n0 := by
    rw [hs2_eq]; exact (storeByte_extent hG1 hef1 _ _ (dst0 + iw + 1) (eval_add3_locals s1 _ _ dst0 iw 1 hd1 hi1) hs1).2.2 ⟨by omega, by omega⟩
  have hef3 : ExtentFrame s0 s3 dst0 n0 := by
    rw [hs3_eq]; exact (storeByte_extent hG2 hef2 _ _ (dst0 + iw + 2) (eval_add3_locals s2 _ _ dst0 iw 2 hd2 hi2) hs2).2.2 ⟨by omega, by omega⟩
  have hef4 : ExtentFrame s0 s4 dst0 n0 := by
    rw [hs4_eq]; exact (storeByte_extent hG3 hef3 _ _ (dst0 + iw + 3) (eval_add3_locals s3 _ _ dst0 iw 3 hd3 hi3) hs3).2.2 ⟨by omega, by omega⟩
  have hef5 : ExtentFrame s0 s5 dst0 n0 := by
    rw [hs5_eq]; exact (storeByte_extent hG4 hef4 _ _ (dst0 + iw + 4) (eval_add3_locals s4 _ _ dst0 iw 4 hd4 hi4) hs4).2.2 ⟨by omega, by omega⟩
  have hef6 : ExtentFrame s0 s6 dst0 n0 := by
    rw [hs6_eq]; exact (storeByte_extent hG5 hef5 _ _ (dst0 + iw + 5) (eval_add3_locals s5 _ _ dst0 iw 5 hd5 hi5) hs5).2.2 ⟨by omega, by omega⟩
  have hef7 : ExtentFrame s0 s7 dst0 n0 := by
    rw [hs7_eq]; exact (storeByte_extent hG6 hef6 _ _ (dst0 + iw + 6) (eval_add3_locals s6 _ _ dst0 iw 6 hd6 hi5_6) hs6).2.2 ⟨by omega, by omega⟩
  have hef8 : ExtentFrame s0 s8 dst0 n0 := by
    rw [hs8_eq]; exact (storeByte_extent hG7 hef7 _ _ (dst0 + iw + 7) (eval_add3_locals s7 _ _ dst0 iw 7 hd7 hi7) hs7).2.2 ⟨by omega, by omega⟩
  change WalkInv s0 dst0 n0 (evaluateHOLFiniteState sd body).2
  rw [heq1, heq2, heq3, heq4, heq5, heq6, heq7, heq8]
  exact assign_i_walk hG8 hef8 hd8 hn8 hi8 hle_ik hdlo hdhi

private theorem step_walk_memcpy4 {F : Type} {s0 : PanSemStateFiniteExact 64 F} {dst0 n0 : BitVec 64}
    (s : PanSemStateFiniteExact 64 F) (w : BitVec 64)
    (hinv : WalkInv s0 dst0 n0 s)
    (hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) =
        some (.val (.word w)))
    (hw : w ≠ 0) :
    let body := (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")])
          (.loadByte (.op .add [.var .local (ofString "src"), .var .local (ofString "i")])))
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])))
    (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none →
      WalkInv s0 dst0 n0 (evaluateHOLFiniteState (decClockHOLFinite s) body).2 := by
  intro body hnone
  obtain ⟨hG, hef, hdst, hn, iw, hi, hle, hdom⟩ := hinv
  let sd := decClockHOLFinite s
  have hGd : GuestInv sd := guestInv_congr (s := s) rfl rfl rfl rfl hG
  have hefd : ExtentFrame s0 sd dst0 n0 := extentFrame_locals_clock hef s.locals (s.clock - 1)
  have hlt := eval_lower_true s n0 iw w hn hi hcond hw
  rw [BitVec.lt_def] at hlt
  obtain ⟨hs0, s1, hs1_eq, hG1, hd1, hn1, hi1, _, heq1⟩ :=
    seq_none_split sd _ _ hGd dst0 n0 iw hdst hn hi rfl rfl rfl hnone
  have b0 := storeByte_extent hGd hefd _ _ (dst0 + iw) (eval_add2_locals sd _ _ dst0 iw hdst hi) hs0
  have hnlt := n0.isLt
  have ha1 : (iw + 1).toNat = iw.toNat + 1 :=
    BitVec.toNat_add_of_lt (by change iw.toNat + 1 < 2 ^ 64; omega)
  have hnl : ¬ (n0 < iw + 1) := by rw [BitVec.lt_def, ha1]; omega
  obtain ⟨hdi_eq, hik_eq, hle_ik, hdlo, hdhi⟩ :=
    step_domain_nowrap dst0 iw n0 1 hle hdom ⟨b0.1, b0.2.1⟩ (by decide) (by decide) hnl
  have hk1_val : (1 : BitVec 64).toNat = 1 := rfl
  have hef1 : ExtentFrame s0 s1 dst0 n0 := by rw [hs1_eq]; exact b0.2.2 ⟨by omega, by omega⟩
  change WalkInv s0 dst0 n0 (evaluateHOLFiniteState sd body).2
  rw [heq1]
  exact assign_i_walk hG1 hef1 hd1 hn1 hi1 hle_ik hdlo hdhi

private theorem setVar_lookup_ne_local {F : Type} (s : PanSemStateFiniteExact 64 F) (a b : MlS)
    (v : ValueHOL 64) (h : b ≠ a) :
    (setVarHOLFinite a v s).locals.lookup b = s.locals.lookup b := by
  simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm h]

private theorem lookup_memzero_local :
    originalRuntimeCode.lookup (ofString "memzero") =
      some ([(ofString "dst", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_memzero, .one) :=
  lookup_of_guestAst_getElem 17 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_memzero) rfl

private theorem lookup_memcpy_local :
    originalRuntimeCode.lookup (ofString "memcpy") =
      some ([(ofString "dst", .one), (ofString "src", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_memcpy, .one) :=
  lookup_of_guestAst_getElem 16 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_memcpy) rfl

private theorem lookup_heap_mark_local :
    originalRuntimeCode.lookup (ofString "heap_mark") =
      some ([], sourceFnBody Guest.Software.guestFn_heap_mark, .one) :=
  lookup_of_guestAst_getElem 8 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_heap_mark) rfl

/-- `heap_mark()` scoped `.decCall`: read-only on `memory` and `globals`! -/
theorem decCall_heap_mark_none {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (name : MlS) (cont : ProgHOL 64) (hc : s.code = originalRuntimeCode)
    (hr : evaluateHOLFiniteState s (.decCall name .one (ofString "heap_mark") [] cont) =
      (none, post)) :
    ∃ (markVal : ValueHOL 64) (resumed inner : PanSemStateFiniteExact 64 F),
      resumed.globals = s.globals ∧
      resumed.memory = s.memory ∧
      resumed.memaddrs = s.memaddrs ∧
      resumed.shMemaddrs = s.shMemaddrs ∧
      resumed.baseAddr = s.baseAddr ∧
      resumed.code = s.code ∧
      resumed.locals = s.locals.update (name, markVal) ∧
      evaluateHOLFiniteState resumed cont = (none, inner) ∧
      post.memory = inner.memory := by
  obtain ⟨vals, body, callee, rs, value, bpost, resumed, inner,
    he, hlk, _, hrun, _, hlocals, hcode, hcont, _, hresumed, hfinal⟩ :=
    arith_decCall_none_state hr
  have hv : vals = [] := by
    simpa [evalListHOLFinite, evalListHOLExact] using he.symm
  subst vals
  have hraw : lookupCodeHOLExact originalRuntimeCode.lookup (ofString "heap_mark") [] =
      some (sourceFnBody Guest.Software.guestFn_heap_mark, (fun _ => none), .one) := by
    simp [lookupCodeHOLExact, lookup_heap_mark_local]
  have hlk_eq : PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup
      (ofString "heap_mark") [] =
      some (sourceFnBody Guest.Software.guestFn_heap_mark, HolFiniteMapExact.empty, .one) := by
    unfold PanSemStateFiniteExact.lookupCodeHOLFinite
    split
    · rename_i hmiss; rw [hraw] at hmiss; cases hmiss
    · rename_i eb el ers hfound
      have hinj := Option.some.inj (hfound.symm.trans hraw)
      obtain ⟨rfl, hinj2⟩ := Prod.mk.inj hinj
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hinj2
      apply congrArg (fun locals => some (sourceFnBody Guest.Software.guestFn_heap_mark, locals, ShapeHOL.one))
      apply HolFiniteMapExact.ext
      funext key
      simp [HolFiniteMapExact.empty, FEMPTY]
  have hlk' := hlk
  rw [hc] at hlk'
  change PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup _ _ = _ at hlk'
  rw [hlk_eq] at hlk'
  obtain ⟨rfl, hinj2⟩ := Prod.mk.inj (Option.some.inj hlk')
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hinj2
  have hbody_eq : sourceFnBody Guest.Software.guestFn_heap_mark =
      .return (.var .global (ofString "heap_ptr")) := rfl
  rw [hbody_eq, evaluateHOLFiniteState_return] at hrun
  split at hrun
  · cases hrun
  · rename_i mv hmv
    split at hrun
    · rename_i hsz
      have hinj_run := Prod.mk.inj hrun
      have hret_mv := PanSemResultExact.returned.inj (Option.some.inj hinj_run.1)
      subst hret_mv
      have hbpost := hinj_run.2
      refine ⟨mv, resumed, inner, ?_, ?_, ?_, ?_, ?_, hcode, hlocals, hcont, ?_⟩
      · rw [hresumed, ← hbpost]; rfl
      · rw [hresumed, ← hbpost]; rfl
      · rw [hresumed, ← hbpost]; rfl
      · rw [hresumed, ← hbpost]; rfl
      · rw [hresumed, ← hbpost]; rfl
      · rw [hfinal]
    · cases hrun

/-- Callee-level `memzero(dst0, n0)` returning `some (.returned ret)` from `GuestInv`:
establishes `ExtentFrame` and (when `0 < n0`) `sourceBase ≤ dst0 ∧ dst0 + n0 ≤ heapEnd`,
plus exact `0` words when `dst0 % 8 = 0 ∧ n0 = 416`! -/
theorem memzero_callee_returned {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (dst0 n0 : BitVec 64) (ret : ValueHOL 64)
    (hG : GuestInv s)
    (hdst0 : s.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (hn0 : s.locals.lookup (ofString "n") = some (.val (.word n0)))
    (hr : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_memzero) =
      (some (.returned ret), post)) :
    ExtentFrame s post dst0 n0 ∧
    (0 < n0.toNat → sourceBase ≤ dst0.toNat ∧ dst0.toNat + n0.toNat ≤ heapEnd) ∧
    (dst0.toNat % 8 = 0 → n0 = 416 →
      MemoryPolynomial post.memory dst0 (fun _ => fqZeroLimbs)) := by
  have hret := hr
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_memzero,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hret
  obtain ⟨iv, inner, hiv, _, hbody, hpost⟩ := arith_dec_returned_state hret
  have hiv0 : iv = .val (.word 0) := by simpa [evalHOLFinite, evalHOLExact] using hiv.symm
  subst iv
  set s1 := setVarHOLFinite (ofString "i") (.val (.word 0)) s with hs1
  have hinv1 : WalkInv s dst0 n0 s1 := by
    refine ⟨guestInv_congr (s := s) rfl rfl rfl rfl hG,
      extentFrame_locals_clock (extentFrame_refl s dst0 n0) _ s.clock, ?_, ?_, 0, ?_,
      Nat.zero_le _, fun h => by simp at h⟩
    · rw [hs1, setVar_lookup_ne_local s (ofString "i") (ofString "dst") _ (by decide), hdst0]
    · rw [hs1, setVar_lookup_ne_local s (ofString "i") (ofString "n") _ (by decide), hn0]
    · simp [hs1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  rcases arith_seq_returned hbody with hite_ret | ⟨s2, hite_run, hrest2⟩
  · exfalso
    exact evaluate_noReturnLocal _ rfl s1 ret (congrArg Prod.fst hite_ret)
  have hinv2_and_align : WalkInv s dst0 n0 s2 ∧
      (dst0.toNat % 8 = 0 → n0 = 416 →
        MemoryPolynomial s2.memory dst0 (fun _ => fqZeroLimbs) ∧
        s2.locals.lookup (ofString "i") = some (.val (.word 416))) := by
    rw [evaluateHOLFiniteState_ite] at hite_run
    have hcond_ev : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
        (.cmp .equal (.op .and [.var .local (ofString "dst"), .const 7#64]) (.const 0#64)) =
        some (.val (.word (if dst0 &&& 7#64 = 0#64 then 1#64 else 0#64))) := by
      have hd1 : s1.locals.lookup (ofString "dst") = some (.val (.word dst0)) := hinv1.2.2.1
      simp only [evalHOLExact, evalListHOLExact, hd1, wordOpHOL, wordOp, valueIsWord, valueWord,
        List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr, wordCmpHOL]
      have hand_eq : AndOp.and dst0 (AndOp.and 7#64 18446744073709551615#64) = dst0 &&& 7#64 := by
        change dst0 &&& (7#64 &&& 18446744073709551615#64) = dst0 &&& 7#64
        rw [show (7#64 &&& 18446744073709551615#64) = 7#64 by decide]
      by_cases h : dst0 &&& 7#64 = 0#64 <;> simp [hand_eq, h]
    rw [hcond_ev] at hite_run
    dsimp only at hite_run
    by_cases hal7 : dst0 &&& 7#64 = 0#64
    · rw [if_pos hal7] at hite_run
      simp only [show ¬ ((1#64 : BitVec 64) = 0) by decide, ↓reduceIte] at hite_run
      obtain ⟨m1, hw1, hw2⟩ := arith_seq_none hite_run
      obtain ⟨hm1, hcond_m1⟩ := while_preserve_walk _ _ rfl rfl step_walk_memzero1 s1.clock s1 m1 le_rfl hinv1 hw1
      obtain ⟨hs2, hcond_s2⟩ := while_preserve_walk _ _ rfl rfl step_walk_memzero2 m1.clock m1 s2 le_rfl hm1 hw2
      refine ⟨hs2, fun hal8 hn416 => ?_⟩
      subst hn416
      have hl1_exact : ∀ (rem : Nat) (st : PanSemStateFiniteExact 64 F),
          rem ≤ 13 →
          st.locals.lookup (ofString "dst") = some (.val (.word dst0)) →
          st.locals.lookup (ofString "n") = some (.val (.word 416#64)) →
          st.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 (32 * (13 - rem))))) →
          (∀ j, j < 13 - rem → MemoryU256 st.memory (coefficientAddress dst0 j) fqZeroLimbs) →
          evaluateHOLFiniteState st
            (.while (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 32#64]))
              (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) (.const 0#64))
                (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 8#64]) (.const 0#64))
                  (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 16#64]) (.const 0#64))
                    (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 24#64]) (.const 0#64))
                      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 32#64]))))))) =
            (none, m1) →
          MemoryPolynomial m1.memory dst0 (fun _ => fqZeroLimbs) ∧
          m1.locals.lookup (ofString "i") = some (.val (.word 416#64)) := by
        intro rem
        induction rem with
        | zero =>
          intro st _ hdst_st hn_st hi_st hprev hrun_st
          rw [evaluateHOLFiniteState_while_fixClockRewrite] at hrun_st
          have h13 : BitVec.ofNat 64 (32 * (13 - 0)) = 416#64 := rfl
          rw [h13] at hi_st
          have hc0 : evalHOLFinite st (h := fun a => Classical.propDecidable (st.memaddrs a))
              (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 32#64])) =
              some (.val (.word 0#64)) := by
            simp [evalHOLFinite, evalHOLExact, evalListHOLExact, hn_st, hi_st, wordOpHOL, wordOp, valueIsWord, valueWord, wordCmpHOL]
          rw [hc0] at hrun_st
          dsimp only at hrun_st
          rw [if_neg (show ¬ (0#64 : BitVec 64) ≠ 0 by simp)] at hrun_st
          have hst_eq : st = m1 := (Prod.mk.inj hrun_st).2
          subst hst_eq
          exact ⟨fun j hj => hprev j hj, hi_st⟩
        | succ rem ih =>
          intro st hrem hdst_st hn_st hi_st hprev hrun_st
          set idx := 13 - (rem + 1)
          have hidx_lt : idx < 13 := by omega
          have hrem_sub : 13 - rem = idx + 1 := by omega
          rw [evaluateHOLFiniteState_while_fixClockRewrite] at hrun_st
          have hi_lt64 : 32 * idx + 32 < 2 ^ 64 := by omega
          have hc1 : evalHOLFinite st (h := fun a => Classical.propDecidable (st.memaddrs a))
              (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 32#64])) =
              some (.val (.word 1#64)) := by
            have hle416 : BitVec.ofNat 64 (32 * idx) + 32#64 ≤ 416#64 := by
              rw [BitVec.le_def, BitVec.toNat_add, BitVec.toNat_ofNat]
              have h1 : 32 * idx % 2 ^ 64 = 32 * idx := Nat.mod_eq_of_lt (by omega)
              have h2 : (32#64 : BitVec 64).toNat = 32 := rfl
              have h3 : (416#64 : BitVec 64).toNat = 416 := rfl
              rw [h1, h2, h3, Nat.mod_eq_of_lt hi_lt64]; omega
            have hnotlt' : ¬ (416#64 < BitVec.ofNat 64 (32 * idx) + 32#64) := by
              rw [BitVec.lt_def]; rw [BitVec.le_def] at hle416; omega
            simp [evalHOLFinite, evalHOLExact, evalListHOLExact, hn_st, hi_st,
              wordOpHOL, wordOp, valueIsWord, valueWord, wordCmpHOL, hnotlt']
          rw [hc1] at hrun_st
          dsimp only at hrun_st
          rw [if_pos (show (1#64 : BitVec 64) ≠ 0 by decide)] at hrun_st
          by_cases hclk : st.clock = 0
          · simp [hclk] at hrun_st
          · rw [if_neg hclk] at hrun_st
            let loopBody : ProgHOL 64 :=
              ProgHOL.seq (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "i")]) (ExpHOL.const 0#64))
                (ProgHOL.seq (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const 8#64]) (ExpHOL.const 0#64))
                  (ProgHOL.seq (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const 16#64]) (ExpHOL.const 0#64))
                    (ProgHOL.seq (ProgHOL.store (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "dst"), ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const 24#64]) (ExpHOL.const 0#64))
                      (ProgHOL.assign VarKind.local (ofString "i") (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const 32#64])))))
            rcases hbody_st : evaluateHOLFiniteState (decClockHOLFinite st) loopBody with ⟨rb, mid⟩
            rw [hbody_st] at hrun_st
            cases rb with
            | some r =>
              cases r with
              | «continue» =>
                have hnc := evaluate_noTopContinue loopBody (by decide) (decClockHOLFinite st)
                rw [hbody_st] at hnc; exact absurd rfl hnc
              | «break» =>
                have hnb := evaluate_noBreakLocal loopBody rfl (decClockHOLFinite st)
                rw [hbody_st] at hnb; exact absurd rfl hnb
              | _ => simp at hrun_st
            | none =>
              let sd := decClockHOLFinite st
              have hstore_zero : ∀ (q : PanSemStateFiniteExact 64 F) (ae : ExpHOL 64) (addr : BitVec 64),
                  @evalHOLExact 64 F _ q.toExact (fun a => Classical.propDecidable (q.memaddrs a)) ae =
                    some (.val (.word addr)) →
                  (evaluateHOLFiniteState q (.store ae (.const 0#64))).1 = none →
                  evaluateHOLFiniteState q (.store ae (.const 0#64)) =
                    (none, { q with memory := writeMemoryWord q.memory addr 0 }) := by
                intro q ae addr hae hnone_q
                rw [evaluateHOLFiniteState_store] at hnone_q ⊢
                rw [hae] at hnone_q ⊢
                have hconst0 : @evalHOLExact 64 F _ q.toExact (fun a => Classical.propDecidable (q.memaddrs a)) (.const 0#64) =
                    some (.val (.word 0#64)) := rfl
                rw [hconst0] at hnone_q ⊢
                dsimp only at hnone_q ⊢
                simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL] at hnone_q ⊢
                by_cases hdom : q.memaddrs addr
                · simp only [hdom, ↓reduceIte]
                  rfl
                · simp [hdom] at hnone_q
              obtain ⟨m_a, hs0, hr1⟩ := arith_seq_none hbody_st
              obtain ⟨m_b, hs8, hr2⟩ := arith_seq_none hr1
              obtain ⟨m_c, hs16, hr3⟩ := arith_seq_none hr2
              obtain ⟨m_d, hs24, hass⟩ := arith_seq_none hr3
              let mem1 := writeMemoryWord sd.memory (dst0 + BitVec.ofNat 64 (32 * idx)) 0
              let mem2 := writeMemoryWord mem1 (dst0 + BitVec.ofNat 64 (32 * idx) + 8#64) 0
              let mem3 := writeMemoryWord mem2 (dst0 + BitVec.ofNat 64 (32 * idx) + 16#64) 0
              have he0 := hstore_zero sd _ (dst0 + BitVec.ofNat 64 (32 * idx))
                (eval_add2_locals sd _ _ dst0 _ hdst_st hi_st) (congrArg Prod.fst hs0)
              have hs0_eq : m_a = { sd with memory := mem1 } :=
                (Prod.mk.inj (hs0.symm.trans he0)).2
              subst hs0_eq
              let s_a : PanSemStateFiniteExact 64 F := { sd with memory := mem1 }
              have he8 := hstore_zero s_a _ (dst0 + BitVec.ofNat 64 (32 * idx) + 8#64)
                (eval_add3_locals s_a _ _ dst0 _ 8#64 hdst_st hi_st) (congrArg Prod.fst hs8)
              have hs8_eq : m_b = { sd with memory := mem2 } :=
                (Prod.mk.inj (hs8.symm.trans he8)).2
              subst hs8_eq
              let s_b : PanSemStateFiniteExact 64 F := { sd with memory := mem2 }
              have he16 := hstore_zero s_b _ (dst0 + BitVec.ofNat 64 (32 * idx) + 16#64)
                (eval_add3_locals s_b _ _ dst0 _ 16#64 hdst_st hi_st) (congrArg Prod.fst hs16)
              have hs16_eq : m_c = { sd with memory := mem3 } :=
                (Prod.mk.inj (hs16.symm.trans he16)).2
              subst hs16_eq
              let s_c : PanSemStateFiniteExact 64 F := { sd with memory := mem3 }
              have he24 := hstore_zero s_c _ (dst0 + BitVec.ofNat 64 (32 * idx) + 24#64)
                (eval_add3_locals s_c _ _ dst0 _ 24#64 hdst_st hi_st) (congrArg Prod.fst hs24)
              have hs24_eq : m_d = { sd with memory := writeU256 sd.memory (coefficientAddress dst0 idx) fqZeroLimbs } := by
                have := (Prod.mk.inj (hs24.symm.trans he24)).2
                exact this
              subst hs24_eq
              let st_w : PanSemStateFiniteExact 64 F :=
                { sd with memory := writeU256 sd.memory (coefficientAddress dst0 idx) fqZeroLimbs }
              have hi_stw : st_w.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 (32 * (13 - (rem + 1)))))) := hi_st
              have hdst_stw : st_w.locals.lookup (ofString "dst") = some (.val (.word dst0)) := hdst_st
              have hn_stw : st_w.locals.lookup (ofString "n") = some (.val (.word 416#64)) := hn_st
              have hass_eq : mid = setVarHOLFinite (ofString "i") (.val (.word (BitVec.ofNat 64 (32 * idx) + 32#64))) st_w := by
                have ha_ev : evaluateHOLFiniteState st_w
                    (ProgHOL.assign VarKind.local (ofString "i") (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const 32#64])) =
                    (none, setVarHOLFinite (ofString "i") (.val (.word (BitVec.ofNat 64 (32 * idx) + 32#64))) st_w) := by
                  simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hi_stw, idx,
                    wordOpHOL, wordOp, valueIsWord, valueWord, lookupKvarHOLExact, isValidValueHOLExact,
                    setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL]
                exact (Prod.mk.inj (hass.symm.trans ha_ev)).2
              subst hass_eq
              have hi_mid : BitVec.ofNat 64 (32 * idx) + 32#64 = BitVec.ofNat 64 (32 * (13 - rem)) := by
                rw [hrem_sub, Nat.mul_add, Nat.mul_one, BitVec.ofNat_add]
              refine ih _ (by omega)
                (by rw [setVar_lookup_ne_local st_w (ofString "i") (ofString "dst") _ (by decide), hdst_stw])
                (by rw [setVar_lookup_ne_local st_w (ofString "i") (ofString "n") _ (by decide), hn_stw])
                (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hi_mid])
                (fun j hj => ?_) hrun_st
              rw [hrem_sub] at hj
              by_cases hji : j = idx
              · rw [hji]; exact writeU256_value st.memory (coefficientAddress dst0 idx) fqZeroLimbs
              · exact writeU256_preserves st.memory _ _ fqZeroLimbs fqZeroLimbs
                  (coefficientWords_disjoint dst0 idx j hidx_lt (by omega) (Ne.symm hji))
                  (hprev j (by omega))
      obtain ⟨hm_m1, hi_m1⟩ := hl1_exact 13 s1 (by decide) hinv1.2.2.1 hinv1.2.2.2.1
        (by simp [hs1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
        (fun _ hj => by omega) hw1
      have hs2_eq : m1 = s2 := by
        rw [evaluateHOLFiniteState_while_fixClockRewrite] at hw2
        have hc2 : evalHOLFinite m1 (h := fun a => Classical.propDecidable (m1.memaddrs a))
            (ExpHOL.cmp Cmp.notLower (ExpHOL.var VarKind.local (ofString "n"))
              (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const 8#64])) =
            some (.val (.word 0#64)) := by
          simp [evalHOLFinite, evalHOLExact, evalListHOLExact, hm1.2.2.2.1, hi_m1, wordOpHOL, wordOp, valueIsWord, valueWord, wordCmpHOL]
        rw [hc2] at hw2
        dsimp only at hw2
        rw [if_neg (show ¬ (0#64 : BitVec 64) ≠ 0 by simp)] at hw2
        exact (Prod.mk.inj hw2).2
      subst hs2_eq
      exact ⟨hm_m1, hi_m1⟩
    · rw [if_neg hal7] at hite_run
      simp only [↓reduceIte, evaluateHOLFiniteState_skip] at hite_run
      have hs2_eq : s1 = s2 := (Prod.mk.inj hite_run).2
      subst hs2_eq
      refine ⟨hinv1, fun hal8 _ => False.elim (hal7 ?_)⟩
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_and]
      have : dst0.toNat &&& (7#64 : BitVec 64).toNat = dst0.toNat % 8 :=
        Nat.and_two_pow_sub_one_eq_mod dst0.toNat 3
      simpa using this.trans hal8
  rcases arith_seq_returned hrest2 with hl3_ret | ⟨s3, hw3, hrest3⟩
  · exfalso
    exact evaluate_noReturnLocal _ rfl s2 ret (congrArg Prod.fst hl3_ret)
  obtain ⟨hinv3, _⟩ := while_preserve_walk _ _ rfl rfl step_walk_memzero3 s2.clock s2 s3 le_rfl hinv2_and_align.1 hw3
  rcases arith_seq_returned hrest3 with hl4_ret | ⟨s4, hw4, hret4⟩
  · exfalso
    exact evaluate_noReturnLocal _ rfl s3 ret (congrArg Prod.fst hl4_ret)
  obtain ⟨hinv4, hcond4⟩ := while_preserve_walk _ _ rfl rfl step_walk_memzero4 s3.clock s3 s4 le_rfl hinv3 hw4
  have hret_eval : evaluateHOLFiniteState s4 (.return (.const 0#64)) =
      (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite s4) := by
    simp [evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL]
  rw [hret_eval] at hret4
  have hs4_post : post.memory = s4.memory ∧ post.globals = s4.globals := by
    rw [hpost, ← (Prod.mk.inj hret4).2]; exact ⟨rfl, rfl⟩
  obtain ⟨_, hef4, _, hn4, iw4, hi4, hle4, hdom4⟩ := hinv4
  have hge4 := eval_lower_false s4 n0 iw4 hn4 hi4 hcond4
  have hiw_eq : iw4.toNat = n0.toNat := by rw [BitVec.lt_def] at hge4; omega
  refine ⟨⟨hs4_post.2.trans hef4.1, fun x hne => hef4.2 x (hs4_post.1 ▸ hne)⟩,
    fun hpos => by have := hdom4 (by omega); rw [hiw_eq] at this; exact this,
    fun hal8 hn416 => ?_⟩
  obtain ⟨hm_s2, hi_s2⟩ := hinv2_and_align.2 hal8 hn416
  subst hn416
  have hs3_eq : s2 = s3 := by
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at hw3
    have hc3 : evalHOLFinite s2 (h := fun a => Classical.propDecidable (s2.memaddrs a))
        (ExpHOL.cmp Cmp.notLower (ExpHOL.var VarKind.local (ofString "n"))
          (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const 8#64])) =
        some (.val (.word 0#64)) := by
      have hn2 := hinv2_and_align.1.2.2.2.1
      simp [evalHOLFinite, evalHOLExact, evalListHOLExact, hn2, hi_s2, wordOpHOL, wordOp, valueIsWord, valueWord, wordCmpHOL]
    rw [hc3] at hw3
    dsimp only at hw3
    rw [if_neg (show ¬ (0#64 : BitVec 64) ≠ 0 by simp)] at hw3
    exact (Prod.mk.inj hw3).2
  have hs4_eq : s3 = s4 := by
    subst hs3_eq
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at hw4
    have hc4 : evalHOLFinite s2 (h := fun a => Classical.propDecidable (s2.memaddrs a))
        (ExpHOL.cmp Cmp.lower (ExpHOL.var VarKind.local (ofString "i")) (ExpHOL.var VarKind.local (ofString "n"))) =
        some (.val (.word 0#64)) := by
      have hn2 := hinv2_and_align.1.2.2.2.1
      simp [evalHOLFinite, evalHOLExact, hn2, hi_s2, wordCmpHOL]
    rw [hc4] at hw4
    dsimp only at hw4
    rw [if_neg (show ¬ (0#64 : BitVec 64) ≠ 0 by simp)] at hw4
    exact (Prod.mk.inj hw4).2
  rw [hs4_post.1, ← hs4_eq, ← hs3_eq]
  exact hm_s2

/-- Discard-result `memzero(dstExp, nExp)` call under `GuestInv`. -/
theorem call_memzero_none {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (dstExp nExp : ExpHOL 64) (dst0 n0 : BitVec 64)
    (hc : s.code = originalRuntimeCode) (hG : GuestInv s)
    (hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [dstExp, nExp] =
      some [.val (.word dst0), .val (.word n0)])
    (hr : evaluateHOLFiniteState s (.call (some (none, none)) (ofString "memzero") [dstExp, nExp]) =
      (none, post)) :
    ExtentFrame s post dst0 n0 ∧
    post.locals = s.locals ∧
    (0 < n0.toNat → sourceBase ≤ dst0.toNat ∧ dst0.toNat + n0.toNat ≤ heapEnd) ∧
    (dst0.toNat % 8 = 0 → n0 = 416 →
      MemoryPolynomial post.memory dst0 (fun _ => fqZeroLimbs)) := by
  obtain ⟨vals, body, callee, rs, ret, bpost, heargs, hlk, _, hrun, _, hpost⟩ :=
    arith_call_discard_none_state hr
  have hv : vals = [.val (.word dst0), .val (.word n0)] := Option.some.inj (heargs.symm.trans hargs)
  subst vals
  rw [hc] at hlk
  obtain ⟨_, _, rfl, rfl, rfl⟩ := arith_two_arg_lookup_inv_shape originalRuntimeCode.lookup
    (ofString "memzero") (ofString "dst") (ofString "n") .one .one .one
    (sourceFnBody Guest.Software.guestFn_memzero) (.val (.word dst0)) (.val (.word n0))
    (by decide) lookup_memzero_local hlk
  let entry := callEntryStateHOLFinite s
    ((HolFiniteMapExact.empty.update (ofString "dst", .val (.word dst0))).update
      (ofString "n", .val (.word n0)))
  have hGe : GuestInv entry := guestInv_congr (s := s) rfl rfl rfl rfl hG
  have hd_lk : entry.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
    simp [entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "n" ≠ ofString "dst" by decide]
  have hn_lk : entry.locals.lookup (ofString "n") = some (.val (.word n0)) := by
    simp [entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  obtain ⟨hef, hdom, hpoly⟩ := memzero_callee_returned entry bpost dst0 n0 ret hGe hd_lk hn_lk hrun
  refine ⟨?_, by rw [hpost], hdom, ?_⟩
  · rw [hpost]; exact ⟨hef.1, hef.2⟩
  · intro hal hn416; rw [hpost]; exact hpoly hal hn416

/-- Callee-level `memcpy(dst0, src0, n0)` returning `some (.returned ret)` from `GuestInv`:
establishes `ExtentFrame` for arbitrary alignment/length, AND exact `MemoryPolynomial` copy
when `dst0 % 8 = 0 ∧ src0 % 8 = 0 ∧ n0 = 416 ∧ PolynomialDisjoint dst0 src0`! -/
theorem memcpy_callee_returned {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (dst0 src0 n0 : BitVec 64) (ret : ValueHOL 64)
    (hG : GuestInv s)
    (hdst0 : s.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (hsrc0 : s.locals.lookup (ofString "src") = some (.val (.word src0)))
    (hn0 : s.locals.lookup (ofString "n") = some (.val (.word n0)))
    (hr : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_memcpy) =
      (some (.returned ret), post)) :
    ExtentFrame s post dst0 n0 ∧
    (0 < n0.toNat → sourceBase ≤ dst0.toNat ∧ dst0.toNat + n0.toNat ≤ heapEnd) ∧
    (∀ Src : Nat → Limbs256,
      dst0.toNat % 8 = 0 → src0.toNat % 8 = 0 → n0 = 416 →
      DomainPolynomial s.memaddrs dst0 → DomainPolynomial s.memaddrs src0 →
      MemoryPolynomial s.memory src0 Src →
      PolynomialDisjoint dst0 src0 →
      MemoryPolynomial post.memory dst0 Src) := by
  have hret := hr
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_memcpy,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hret
  obtain ⟨iv, inner, hiv, _, hbody, hpost⟩ := arith_dec_returned_state hret
  have hiv0 : iv = .val (.word 0) := by simpa [evalHOLFinite, evalHOLExact] using hiv.symm
  subst iv
  set s1 := setVarHOLFinite (ofString "i") (.val (.word 0)) s with hs1
  have hsrc_s1 : s1.locals.lookup (ofString "src") = some (.val (.word src0)) := by
    rw [hs1, setVar_lookup_ne_local s (ofString "i") (ofString "src") _ (by decide), hsrc0]
  have hinv1 : WalkInv s dst0 n0 s1 := by
    refine ⟨guestInv_congr (s := s) rfl rfl rfl rfl hG,
      extentFrame_locals_clock (extentFrame_refl s dst0 n0) _ s.clock, ?_, ?_, 0, ?_,
      Nat.zero_le _, fun h => by simp at h⟩
    · rw [hs1, setVar_lookup_ne_local s (ofString "i") (ofString "dst") _ (by decide), hdst0]
    · rw [hs1, setVar_lookup_ne_local s (ofString "i") (ofString "n") _ (by decide), hn0]
    · simp [hs1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  rcases arith_seq_returned hbody with hite_ret | ⟨s2, hite_run, hrest2⟩
  · exfalso
    exact evaluate_noReturnLocal _ rfl s1 ret (congrArg Prod.fst hite_ret)
  have hinv2_and_align : WalkInv s dst0 n0 s2 ∧
      (∀ Src : Nat → Limbs256,
        dst0.toNat % 8 = 0 → src0.toNat % 8 = 0 → n0 = 416 →
        DomainPolynomial s.memaddrs dst0 → DomainPolynomial s.memaddrs src0 →
        MemoryPolynomial s.memory src0 Src →
        PolynomialDisjoint dst0 src0 →
        MemoryPolynomial s2.memory dst0 Src ∧
        s2.locals.lookup (ofString "i") = some (.val (.word 416))) := by
    rw [evaluateHOLFiniteState_ite] at hite_run
    have hcond_ev : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
        (.cmp .equal (.op .and [.op .or [.var .local (ofString "dst"), .var .local (ofString "src")], .const 7#64]) (.const 0#64)) =
        some (.val (.word (if (dst0 ||| src0) &&& 7#64 = 0#64 then 1#64 else 0#64))) := by
      have hd1 : s1.locals.lookup (ofString "dst") = some (.val (.word dst0)) := hinv1.2.2.1
      simp only [evalHOLExact, evalListHOLExact, hd1, hsrc_s1, wordOpHOL, wordOp, valueIsWord, valueWord,
        List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr, wordCmpHOL]
      have hor_eq : OrOp.or dst0 (OrOp.or src0 0#64) = dst0 ||| src0 := by
        change dst0 ||| (src0 ||| 0#64) = dst0 ||| src0
        rw [BitVec.or_zero]
      have hand_eq : AndOp.and (dst0 ||| src0) (AndOp.and 7#64 18446744073709551615#64) = (dst0 ||| src0) &&& 7#64 := by
        change (dst0 ||| src0) &&& (7#64 &&& 18446744073709551615#64) = (dst0 ||| src0) &&& 7#64
        rw [show (7#64 &&& 18446744073709551615#64) = 7#64 by decide]
      by_cases h : (dst0 ||| src0) &&& 7#64 = 0#64 <;> simp [hor_eq, hand_eq, h]
    rw [hcond_ev] at hite_run
    dsimp only at hite_run
    by_cases hal7 : (dst0 ||| src0) &&& 7#64 = 0#64
    · rw [if_pos hal7] at hite_run
      simp only [show ¬ ((1#64 : BitVec 64) = 0) by decide, ↓reduceIte] at hite_run
      obtain ⟨m1, hw1, hw2⟩ := arith_seq_none hite_run
      obtain ⟨hm1, _⟩ := while_preserve_walk _ _ rfl rfl step_walk_memcpy1 s1.clock s1 m1 le_rfl hinv1 hw1
      obtain ⟨hs2, _⟩ := while_preserve_walk _ _ rfl rfl step_walk_memcpy2 m1.clock m1 s2 le_rfl hm1 hw2
      refine ⟨hs2, fun Src hald hals hn416 hdd hds hmsrc hdisj => ?_⟩
      subst hn416
      have hl1_exact : ∀ (rem : Nat) (st : PanSemStateFiniteExact 64 F),
          rem ≤ 13 →
          st.memaddrs = s.memaddrs →
          st.locals.lookup (ofString "dst") = some (.val (.word dst0)) →
          st.locals.lookup (ofString "src") = some (.val (.word src0)) →
          st.locals.lookup (ofString "n") = some (.val (.word 416#64)) →
          st.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 (32 * (13 - rem))))) →
          MemoryPolynomial st.memory src0 Src →
          (∀ j, j < 13 - rem → MemoryU256 st.memory (coefficientAddress dst0 j) (Src j)) →
          evaluateHOLFiniteState st
            (.while (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 32#64]))
              memcpyAlignedBody) = (none, m1) →
          MemoryPolynomial m1.memory dst0 Src ∧
          m1.locals.lookup (ofString "i") = some (.val (.word 416#64)) := by
        intro rem
        induction rem with
        | zero =>
          intro st _ _ _ _ hn_st hi_st _ hprev hrun_st
          rw [evaluateHOLFiniteState_while_fixClockRewrite] at hrun_st
          have h13 : BitVec.ofNat 64 (32 * (13 - 0)) = 416#64 := rfl
          rw [h13] at hi_st
          have hc0 : evalHOLFinite st (h := fun a => Classical.propDecidable (st.memaddrs a))
              (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 32#64])) =
              some (.val (.word 0#64)) := by
            simp [evalHOLFinite, evalHOLExact, evalListHOLExact, hn_st, hi_st, wordOpHOL, wordOp, valueIsWord, valueWord, wordCmpHOL]
          rw [hc0] at hrun_st
          dsimp only at hrun_st
          rw [if_neg (show ¬ (0#64 : BitVec 64) ≠ 0 by simp)] at hrun_st
          have hst_eq : st = m1 := (Prod.mk.inj hrun_st).2
          subst hst_eq
          exact ⟨fun j hj => hprev j hj, hi_st⟩
        | succ rem ih =>
          intro st hrem hdom_st hdst_st hsrc_st hn_st hi_st hmsrc_st hprev hrun_st
          set idx := 13 - (rem + 1)
          have hidx_lt : idx < 13 := by omega
          have hrem_sub : 13 - rem = idx + 1 := by omega
          rw [evaluateHOLFiniteState_while_fixClockRewrite] at hrun_st
          have hi_lt64 : 32 * idx + 32 < 2 ^ 64 := by omega
          have hc1 : evalHOLFinite st (h := fun a => Classical.propDecidable (st.memaddrs a))
              (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 32#64])) =
              some (.val (.word 1#64)) := by
            have hle416 : BitVec.ofNat 64 (32 * idx) + 32#64 ≤ 416#64 := by
              rw [BitVec.le_def, BitVec.toNat_add, BitVec.toNat_ofNat]
              have h1 : 32 * idx % 2 ^ 64 = 32 * idx := Nat.mod_eq_of_lt (by omega)
              have h2 : (32#64 : BitVec 64).toNat = 32 := rfl
              have h3 : (416#64 : BitVec 64).toNat = 416 := rfl
              rw [h1, h2, h3, Nat.mod_eq_of_lt hi_lt64]; omega
            have hnotlt' : ¬ (416#64 < BitVec.ofNat 64 (32 * idx) + 32#64) := by
              rw [BitVec.lt_def]; rw [BitVec.le_def] at hle416; omega
            simp [evalHOLFinite, evalHOLExact, evalListHOLExact, hn_st, hi_st,
              wordOpHOL, wordOp, valueIsWord, valueWord, wordCmpHOL, hnotlt']
          rw [hc1] at hrun_st
          dsimp only at hrun_st
          rw [if_pos (show (1#64 : BitVec 64) ≠ 0 by decide)] at hrun_st
          by_cases hclk : st.clock = 0
          · simp [hclk] at hrun_st
          · rw [if_neg hclk] at hrun_st
            let sd := decClockHOLFinite st
            have hsep : ∀ a ∈ u256Addresses (dst0 + BitVec.ofNat 64 (32 * idx)),
                a ∉ u256Addresses (src0 + BitVec.ofNat 64 (32 * idx)) :=
              fun a ha hsa => hdisj idx hidx_lt idx hidx_lt a hsa ha
            have hb_ev := memcpyAlignedBody_eval (decClockHOLFinite st) dst0 src0 (BitVec.ofNat 64 (32 * idx)) (Src idx)
              hdst_st hsrc_st hi_st
              (hdom_st ▸ hdd idx hidx_lt) (hdom_st ▸ hds idx hidx_lt)
              (hmsrc_st idx hidx_lt) hsep
            rw [hb_ev] at hrun_st
            dsimp only at hrun_st
            let st_w : PanSemStateFiniteExact 64 F :=
              { sd with memory := writeU256 sd.memory (dst0 + BitVec.ofNat 64 (32 * idx)) (Src idx) }
            have hdst_stw : st_w.locals.lookup (ofString "dst") = some (.val (.word dst0)) := hdst_st
            have hsrc_stw : st_w.locals.lookup (ofString "src") = some (.val (.word src0)) := hsrc_st
            have hn_stw : st_w.locals.lookup (ofString "n") = some (.val (.word 416#64)) := hn_st
            have hi_mid : BitVec.ofNat 64 (32 * idx) + 32#64 = BitVec.ofNat 64 (32 * (13 - rem)) := by
              rw [hrem_sub, Nat.mul_add, Nat.mul_one, BitVec.ofNat_add]
            let st_next := setVarHOLFinite (ofString "i") (ValueHOL.val (HolWordLab.word (BitVec.ofNat 64 (32 * idx) + 32))) st_w
            have hdom_next : st_next.memaddrs = s.memaddrs := hdom_st
            have hca_eq : dst0 + BitVec.ofNat 64 (32 * idx) = coefficientAddress dst0 idx := rfl
            refine ih st_next (by omega) hdom_next
              (by rw [setVar_lookup_ne_local st_w (ofString "i") (ofString "dst") _ (by decide), hdst_stw])
              (by rw [setVar_lookup_ne_local st_w (ofString "i") (ofString "src") _ (by decide), hsrc_stw])
              (by rw [setVar_lookup_ne_local st_w (ofString "i") (ofString "n") _ (by decide), hn_stw])
              (by simp [st_next, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hi_mid])
              (fun k hk => by
                change MemoryU256 (writeU256 st.memory (dst0 + BitVec.ofNat 64 (32 * idx)) (Src idx)) _ _
                rw [hca_eq]
                exact writeU256_preserves st.memory _ _ (Src idx) (Src k)
                  (fun x hx hxd => hdisj idx hidx_lt k hk x hx hxd) (hmsrc_st k hk))
              (fun j hj => ?_) hrun_st
            change MemoryU256 (writeU256 st.memory (dst0 + BitVec.ofNat 64 (32 * idx)) (Src idx)) _ _
            rw [hrem_sub] at hj
            rw [hca_eq]
            by_cases hji : j = idx
            · rw [hji]; exact writeU256_value st.memory (coefficientAddress dst0 idx) (Src idx)
            · exact writeU256_preserves st.memory _ _ (Src idx) (Src j)
                (coefficientWords_disjoint dst0 idx j hidx_lt (by omega) (Ne.symm hji))
                (hprev j (by omega))
      obtain ⟨hm_m1, hi_m1⟩ := hl1_exact 13 s1 (by decide) rfl hinv1.2.2.1 hsrc_s1 hinv1.2.2.2.1
        (by simp [hs1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
        hmsrc (fun _ hj => by omega) hw1
      have hs2_eq : m1 = s2 := by
        rw [evaluateHOLFiniteState_while_fixClockRewrite] at hw2
        have hc2 : evalHOLFinite m1 (h := fun a => Classical.propDecidable (m1.memaddrs a))
            (ExpHOL.cmp Cmp.notLower (ExpHOL.var VarKind.local (ofString "n"))
              (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const 8#64])) =
            some (.val (.word 0#64)) := by
          simp [evalHOLFinite, evalHOLExact, evalListHOLExact, hm1.2.2.2.1, hi_m1, wordOpHOL, wordOp, valueIsWord, valueWord, wordCmpHOL]
        rw [hc2] at hw2
        dsimp only at hw2
        rw [if_neg (show ¬ (0#64 : BitVec 64) ≠ 0 by simp)] at hw2
        exact (Prod.mk.inj hw2).2
      subst hs2_eq
      exact ⟨hm_m1, hi_m1⟩
    · rw [if_neg hal7] at hite_run
      simp only [↓reduceIte, evaluateHOLFiniteState_skip] at hite_run
      have hs2_eq : s1 = s2 := (Prod.mk.inj hite_run).2
      subst hs2_eq
      refine ⟨hinv1, fun _ hald hals _ _ _ _ _ => False.elim (hal7 ?_)⟩
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_and, BitVec.toNat_or]
      have hd7 : dst0.toNat &&& 7 = 0 := by
        simpa using (Nat.and_two_pow_sub_one_eq_mod dst0.toNat 3).trans hald
      have hs7 : src0.toNat &&& 7 = 0 := by
        simpa using (Nat.and_two_pow_sub_one_eq_mod src0.toNat 3).trans hals
      have : (dst0.toNat ||| src0.toNat) &&& (7#64 : BitVec 64).toNat =
          (dst0.toNat &&& 7) ||| (src0.toNat &&& 7) := Nat.and_or_distrib_right _ _ 7
      simpa [hd7, hs7] using this
  rcases arith_seq_returned hrest2 with hl3_ret | ⟨s3, hw3, hrest3⟩
  · exfalso
    exact evaluate_noReturnLocal _ rfl s2 ret (congrArg Prod.fst hl3_ret)
  obtain ⟨hinv3, _⟩ := while_preserve_walk _ _ rfl rfl step_walk_memcpy3 s2.clock s2 s3 le_rfl hinv2_and_align.1 hw3
  rcases arith_seq_returned hrest3 with hl4_ret | ⟨s4, hw4, hret4⟩
  · exfalso
    exact evaluate_noReturnLocal _ rfl s3 ret (congrArg Prod.fst hl4_ret)
  obtain ⟨hinv4, hcond4⟩ := while_preserve_walk _ _ rfl rfl step_walk_memcpy4 s3.clock s3 s4 le_rfl hinv3 hw4
  have hret_eval : evaluateHOLFiniteState s4 (.return (.const 0#64)) =
      (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite s4) := by
    simp [evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL]
  rw [hret_eval] at hret4
  have hs4_post : post.memory = s4.memory ∧ post.globals = s4.globals := by
    rw [hpost, ← (Prod.mk.inj hret4).2]; exact ⟨rfl, rfl⟩
  obtain ⟨_, hef4, _, hn4, iw4, hi4, _, hdom4⟩ := hinv4
  have hge4 := eval_lower_false s4 n0 iw4 hn4 hi4 hcond4
  have hiw_eq : iw4.toNat = n0.toNat := by rw [BitVec.lt_def] at hge4; omega
  refine ⟨⟨hs4_post.2.trans hef4.1, fun x hne => hef4.2 x (hs4_post.1 ▸ hne)⟩,
    fun hpos => by have := hdom4 (by omega); rw [hiw_eq] at this; exact this,
    fun Src hald hals hn416 hdd hds hmsrc hdisj => ?_⟩
  obtain ⟨hm_s2, hi_s2⟩ := hinv2_and_align.2 Src hald hals hn416 hdd hds hmsrc hdisj
  subst hn416
  have hs3_eq : s2 = s3 := by
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at hw3
    have hc3 : evalHOLFinite s2 (h := fun a => Classical.propDecidable (s2.memaddrs a))
        (ExpHOL.cmp Cmp.notLower (ExpHOL.var VarKind.local (ofString "n"))
          (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "i"), ExpHOL.const 8#64])) =
        some (.val (.word 0#64)) := by
      have hn2 := hinv2_and_align.1.2.2.2.1
      simp [evalHOLFinite, evalHOLExact, evalListHOLExact, hn2, hi_s2, wordOpHOL, wordOp, valueIsWord, valueWord, wordCmpHOL]
    rw [hc3] at hw3
    dsimp only at hw3
    rw [if_neg (show ¬ (0#64 : BitVec 64) ≠ 0 by simp)] at hw3
    exact (Prod.mk.inj hw3).2
  have hs4_eq : s3 = s4 := by
    subst hs3_eq
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at hw4
    have hc4 : evalHOLFinite s2 (h := fun a => Classical.propDecidable (s2.memaddrs a))
        (ExpHOL.cmp Cmp.lower (ExpHOL.var VarKind.local (ofString "i")) (ExpHOL.var VarKind.local (ofString "n"))) =
        some (.val (.word 0#64)) := by
      have hn2 := hinv2_and_align.1.2.2.2.1
      simp [evalHOLFinite, evalHOLExact, hn2, hi_s2, wordCmpHOL]
    rw [hc4] at hw4
    dsimp only at hw4
    rw [if_neg (show ¬ (0#64 : BitVec 64) ≠ 0 by simp)] at hw4
    exact (Prod.mk.inj hw4).2
  rw [hs4_post.1, ← hs4_eq, ← hs3_eq]
  exact hm_s2

/-- Discard-result `memcpy(dstExp, srcExp, nExp)` call under `GuestInv`. -/
theorem call_memcpy_none {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (dstExp srcExp nExp : ExpHOL 64) (dst0 src0 n0 : BitVec 64)
    (hc : s.code = originalRuntimeCode) (hG : GuestInv s)
    (hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [dstExp, srcExp, nExp] =
      some [.val (.word dst0), .val (.word src0), .val (.word n0)])
    (hr : evaluateHOLFiniteState s (.call (some (none, none)) (ofString "memcpy") [dstExp, srcExp, nExp]) =
      (none, post)) :
    ExtentFrame s post dst0 n0 ∧
    post.locals = s.locals ∧
    (0 < n0.toNat → sourceBase ≤ dst0.toNat ∧ dst0.toNat + n0.toNat ≤ heapEnd) ∧
    (∀ Src : Nat → Limbs256,
      dst0.toNat % 8 = 0 → src0.toNat % 8 = 0 → n0 = 416 →
      DomainPolynomial s.memaddrs dst0 → DomainPolynomial s.memaddrs src0 →
      MemoryPolynomial s.memory src0 Src →
      PolynomialDisjoint dst0 src0 →
      MemoryPolynomial post.memory dst0 Src) := by
  obtain ⟨vals, body, callee, rs, ret, bpost, heargs, hlk, _, hrun, _, hpost⟩ :=
    arith_call_discard_none_state hr
  have hv : vals = [.val (.word dst0), .val (.word src0), .val (.word n0)] :=
    Option.some.inj (heargs.symm.trans hargs)
  subst vals
  have hraw : lookupCodeHOLExact originalRuntimeCode.lookup (ofString "memcpy")
      [.val (.word dst0), .val (.word src0), .val (.word n0)] =
      some (sourceFnBody Guest.Software.guestFn_memcpy,
        (fun key => if key = ofString "n" then some (.val (.word n0))
          else if key = ofString "src" then some (.val (.word src0))
          else if key = ofString "dst" then some (.val (.word dst0)) else none), .one) := by
    simp [lookupCodeHOLExact, lookup_memcpy_local, shapeEqHOL, shapeOfHOLExact]
    decide
  have hlk_eq : PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup
      (ofString "memcpy") [.val (.word dst0), .val (.word src0), .val (.word n0)] =
      some (sourceFnBody Guest.Software.guestFn_memcpy,
        (((HolFiniteMapExact.empty.update (ofString "dst", .val (.word dst0))).update
          (ofString "src", .val (.word src0))).update (ofString "n", .val (.word n0))), .one) := by
    unfold PanSemStateFiniteExact.lookupCodeHOLFinite
    split
    · rename_i hmiss; rw [hraw] at hmiss; cases hmiss
    · rename_i eb el ers hfound
      have hinj := Option.some.inj (hfound.symm.trans hraw)
      obtain ⟨rfl, hinj2⟩ := Prod.mk.inj hinj
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hinj2
      apply congrArg (fun locals => some (sourceFnBody Guest.Software.guestFn_memcpy, locals, ShapeHOL.one))
      apply HolFiniteMapExact.ext
      funext key
      by_cases hkn : key = ofString "n"
      · subst key; simp [HolFiniteMapExact.lookup_update, FUPDATE]
      · by_cases hks : key = ofString "src"
        · subst key; simp [hkn, Ne.symm hkn, HolFiniteMapExact.lookup_update, FUPDATE]
        · by_cases hkd : key = ofString "dst"
          · subst key; simp [hkn, Ne.symm hkn, hks, Ne.symm hks, HolFiniteMapExact.lookup_update, FUPDATE]
          · simp [hkn, Ne.symm hkn, hks, Ne.symm hks, hkd, Ne.symm hkd,
              HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY]
  rw [hc] at hlk
  change PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup _ _ = _ at hlk
  rw [hlk_eq] at hlk
  obtain ⟨rfl, hinj2⟩ := Prod.mk.inj (Option.some.inj hlk)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hinj2
  let entry := callEntryStateHOLFinite s
    (((HolFiniteMapExact.empty.update (ofString "dst", .val (.word dst0))).update
      (ofString "src", .val (.word src0))).update (ofString "n", .val (.word n0)))
  have hGe : GuestInv entry := guestInv_congr (s := s) rfl rfl rfl rfl hG
  have hd_lk : entry.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
    simp [entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "n" ≠ ofString "dst" by decide, show ofString "src" ≠ ofString "dst" by decide]
  have hs_lk : entry.locals.lookup (ofString "src") = some (.val (.word src0)) := by
    simp [entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "n" ≠ ofString "src" by decide]
  have hn_lk : entry.locals.lookup (ofString "n") = some (.val (.word n0)) := by
    simp [entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  obtain ⟨hef, hdom, hpoly⟩ := memcpy_callee_returned entry bpost dst0 src0 n0 ret hGe hd_lk hs_lk hn_lk hrun
  refine ⟨?_, by rw [hpost], hdom, ?_⟩
  · rw [hpost]; exact ⟨hef.1, hef.2⟩
  · intro Src hald hals hn416 hdd hds hmsrc hdisj
    rw [hpost]; exact hpoly Src hald hals hn416 hdd hds hmsrc hdisj

end InitECandidate.Solver.Wave8GuestInv.R16Bn254
