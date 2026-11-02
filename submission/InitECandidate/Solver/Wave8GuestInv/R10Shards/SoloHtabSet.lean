import InitECandidate.Solver.Wave8GuestInv.R10Shards.SoloHtabSetBase

/-! Callee and loop-step lemmas for `htab_set_spec` (`htab_grow`, `htab_new_node`, `htab_new_leaf`,
`htab_new_internal`, `htab_find_leaf`, and `htab_set`'s descent loop). -/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

namespace InitECandidate.Solver.Wave8GuestInv.SoloHtabSet

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

/-! ## 1. Store, Address, and `alloc` Helpers -/

def updW (m : BitVec 64 → HolWordLab 64) (a w : BitVec 64) : BitVec 64 → HolWordLab 64 :=
  fun c => if c = a then .word w else m c

theorem stores_word {dom : BitVec 64 → Prop} (inst : DecidablePred dom)
    {m m' : BitVec 64 → HolWordLab 64}
    {a w : BitVec 64} (h : @panMemStoresHOL 64 _ a (flattenHOL (.val (.word w))) dom inst m = some m') :
    dom a ∧ m' = updW m a w := by
  unfold flattenHOL panMemStoresHOL panMemStoreHOL at h
  by_cases hd : dom a
  · simp only [hd, ↓reduceIte, panMemStoresHOL, Option.some.injEq] at h
    exact ⟨hd, h.symm⟩
  · simp [hd] at h

theorem ofNat64_eq_of_lt {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (h : BitVec.ofNat 64 a = BitVec.ofNat 64 b) : a = b := by
  have h' := congrArg BitVec.toNat h
  simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using h'

theorem ofNat64_ne_of_ne_of_lt {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (h : a ≠ b) : BitVec.ofNat 64 a ≠ BitVec.ofNat 64 b :=
  fun hab => h (ofNat64_eq_of_lt ha hb hab)

theorem ofNat_add_toNat (t : BitVec 64) (n : Nat) :
    BitVec.ofNat 64 (t.toNat + n) = t + BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, BitVec.toNat_ofNat]

theorem ofNat_node_addr (nd w : BitVec 64) (off : Nat) :
    BitVec.ofNat 64 (nd.toNat + 32 * w.toNat + off) = nd + w * 32 + BitVec.ofNat 64 off := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  have : (32 : BitVec 64).toNat = 32 := rfl
  rw [this]
  omega

theorem memW_updW_same {F : Type} (s : PanSemStateFiniteExact 64 F) (a w : BitVec 64) :
    memW { s with memory := updW s.memory a w } a.toNat = w.toNat := by
  simp [memW, updW]

theorem memW_updW_other {F : Type} (s : PanSemStateFiniteExact 64 F)
    (a w : BitVec 64) (b : Nat) (h : BitVec.ofNat 64 b ≠ a) :
    memW { s with memory := updW s.memory a w } b = memW s b := by
  simp [memW, updW, h]

theorem hdr_word {F : Type} (s : PanSemStateFiniteExact 64 F) (tw w : BitVec 64)
    (i : Nat) (h : s.memory (tw + BitVec.ofNat 64 (8 * i)) = .word w) :
    hdr s tw.toNat i = w.toNat := by
  unfold hdr memW
  rw [ofNat_add_toNat tw (8 * i), h]

theorem word_of_hdr {F : Type} (s : PanSemStateFiniteExact 64 F) (tw : BitVec 64)
    (i : Nat) (hi : i < 11) (hB : HtabBlocks s tw.toNat) :
    s.memaddrs (tw + BitVec.ofNat 64 (8 * i)) ∧
    s.memory (tw + BitVec.ofNat 64 (8 * i)) = .word (BitVec.ofNat 64 (hdr s tw.toNat i)) := by
  have hhdr := (hB.1 (tw.toNat, 88) (by simp [htabFootprint])).2
  obtain ⟨w, hdom, hm⟩ := hhdr.2.2 i (by omega)
  rw [ofNat_add_toNat] at hdom hm
  refine ⟨hdom, ?_⟩
  rw [hdr_word s tw w i hm, BitVec.ofNat_toNat, BitVec.setWidth_eq, hm]

theorem word_of_node {F : Type} (s : PanSemStateFiniteExact 64 F) (tw nd w : BitVec 64)
    (off : Nat) (h5 : hdr s tw.toNat 5 = nd.toNat)
    (hw : w.toNat < hdr s tw.toNat 10 + 1)
    (hoff : off = 0 ∨ off = 8 ∨ off = 16 ∨ off = 24)
    (hB : HtabBlocks s tw.toNat) :
    s.memaddrs (nd + w * 32 + BitVec.ofNat 64 off) ∧
    s.memory (nd + w * 32 + BitVec.ofNat 64 off) =
      .word (BitVec.ofNat 64 (nodeF s nd.toNat w.toNat off)) := by
  have hndB := (hB.1 (hdr s tw.toNat 5, (hdr s tw.toNat 10 + 1) * 32) (by simp [htabFootprint])).2
  rw [h5] at hndB
  let k := 4 * w.toNat + off / 8
  have hk : k < ((hdr s tw.toNat 10 + 1) * 32) / 8 := by rcases hoff with rfl | rfl | rfl | rfl <;> dsimp [k] <;> omega
  obtain ⟨u, hdom, hm⟩ := hndB.2.2 k hk
  have hk_eq : nd.toNat + 8 * k = nd.toNat + 32 * w.toNat + off := by
    rcases hoff with rfl | rfl | rfl | rfl <;> dsimp [k] <;> omega
  rw [hk_eq, ofNat_node_addr] at hdom hm
  refine ⟨hdom, ?_⟩
  unfold nodeF memW
  rw [ofNat_node_addr, hm, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem word_of_order {F : Type} (s : PanSemStateFiniteExact 64 F) (tw ow iw : BitVec 64)
    (h6 : hdr s tw.toNat 6 = ow.toNat)
    (hi : iw.toNat < hdr s tw.toNat 10 + 1)
    (hB : HtabBlocks s tw.toNat) :
    s.memaddrs (ow + iw * 8) ∧
    s.memory (ow + iw * 8) = .word (BitVec.ofNat 64 (memW s (ow.toNat + 8 * iw.toNat))) := by
  have hordB := (hB.1 (hdr s tw.toNat 6, (hdr s tw.toNat 10 + 1) * 8) (by simp [htabFootprint])).2
  rw [h6] at hordB
  obtain ⟨u, hdom, hm⟩ := hordB.2.2 iw.toNat (by omega)
  have haddr : BitVec.ofNat 64 (ow.toNat + 8 * iw.toNat) = ow + iw * 8 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
    have : (8 : BitVec 64).toNat = 8 := rfl
    rw [this]; omega
  rw [haddr] at hdom hm
  refine ⟨hdom, ?_⟩
  unfold memW
  rw [haddr, hm, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem frameOutside_updW {F : Type} (s : PanSemStateFiniteExact 64 F)
    (a w : BitVec 64) (keep : List Ivl) (fresh : Ivl)
    (ha : (∃ i ∈ keep, CellHits a.toNat i) ∨ CellHits a.toNat fresh) :
    FrameOutside s { s with memory := updW s.memory a w } keep fresh := by
  intro x hx hfresh
  by_cases hxa : x = a
  · subst x
    exfalso
    rcases ha with ⟨i, hi, hhit⟩ | hhit
    · exact hx i hi hhit
    · exact hfresh hhit
  · simp [updW, hxa]

theorem frameOutside_trans_same {F : Type} {a b c : PanSemStateFiniteExact 64 F}
    {keep : List Ivl} {fresh : Ivl}
    (h1 : FrameOutside a b keep fresh) (h2 : FrameOutside b c keep fresh) :
    FrameOutside a c keep fresh :=
  fun x hx hf => (h2 x hx hf).trans (h1 x hx hf)

theorem cellHits_of_inside {a : Nat} {i j : Ivl}
    (hhit : CellHits a i) (hin : Inside i j.1 (j.1 + j.2)) : CellHits a j := by
  have h1 : i.1 < a + 8 := hhit.1
  have h2 : a < i.1 + i.2 := hhit.2
  have h3 : j.1 ≤ i.1 := hin.1
  have h4 : i.1 + i.2 ≤ j.1 + j.2 := hin.2
  exact ⟨by omega, by omega⟩

theorem frameOutside_mono {F : Type} {a b : PanSemStateFiniteExact 64 F}
    {keep1 keep2 : List Ivl} {fresh1 fresh2 : Ivl}
    (h : FrameOutside a b keep1 fresh1)
    (hk : ∀ i ∈ keep1, (∃ j ∈ keep2, Inside i j.1 (j.1 + j.2)) ∨ Inside i fresh2.1 (fresh2.1 + fresh2.2))
    (hf : Inside fresh1 fresh2.1 (fresh2.1 + fresh2.2)) :
    FrameOutside a b keep2 fresh2 := by
  intro x hx hxf
  apply h x
  · intro i hi hhit
    rcases hk i hi with ⟨j, hj, hij⟩ | hif'
    · exact hx j hj (cellHits_of_inside hhit hij)
    · exact hxf (cellHits_of_inside hhit hif')
  · intro hhit
    exact hxf (cellHits_of_inside hhit hf)

/-! ### `alloc` body semantics -/

theorem alloc_body_run {F : Type}
    (state : PanSemStateFiniteExact 64 F) (p n : BitVec 64)
    (hcode : state.code = originalRuntimeCode)
    (hp_le : p.toNat ≤ cMax.toNat)
    (hp_lookup : state.globals.lookup (ofString "heap_ptr") = some (.val (.word p)))
    (hn : state.locals.lookup (ofString "n") = some (.val (.word n))) :
    let out := evaluateHOLFiniteState state (sourceFnBody Guest.Software.guestFn_alloc)
    let q := (p + (n + 7)) &&& ((0 : BitVec 64) - 8)
    ∀ retVal : ValueHOL 64, out.1 = some (.returned retVal) →
      retVal = .val (.word p) ∧
      p.toNat + n.toNat ≤ q.toNat ∧ q.toNat ≤ cMax.toNat ∧ q.toNat % 8 = 0 ∧
      out.2 = { state with
        globals := (state.globals.update (ofString "heap_ptr", .val (.word q)))
        locals := out.2.locals } := by
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
  rw [hbody_eq, evaluateHOLFiniteState_dec_total]
  have hp_eval : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a))
      (.var .global (ofString "heap_ptr")) = some (.val (.word p)) := hp_lookup
  dsimp only
  rw [hp_eval]
  have hsh_p : shapeEqHOL .one (shapeOfHOLExact (.val (.word p))) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  dsimp only
  rw [if_pos hsh_p]
  dsimp only
  let pState := setVarHOLFinite (ofString "p") (.val (.word p)) state
  have hp_loc : pState.locals.lookup (ofString "p") = some (.val (.word p)) := by
    simp [pState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hn_loc : pState.locals.lookup (ofString "n") = some (.val (.word n)) := by
    simp [pState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn,
      show ofString "p" ≠ ofString "n" by decide]
  rw [evaluateHOLFiniteState_seq_line780]
  have hev1 : @evalHOLExact 64 F _ pState.toExact
      (fun a => Classical.propDecidable (pState.memaddrs a))
      (.cmp .lower (.op .sub [.const cMax, .var .local (ofString "p")])
        (.var .local (ofString "n"))) =
      some (.val (.word (if (cMax - p).toNat < n.toNat then 1 else 0))) := by
    simp only [evalHOLExact, evalListHOLExact, hp_loc, hn_loc,
      Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, decide_eq_true_eq]
    rfl
  by_cases hcmp1 : (cMax - p).toNat < n.toNat
  · have hite1 : evaluateHOLFiniteState pState
        (.ite (.cmp .lower (.op .sub [.const cMax, .var .local (ofString "p")])
            (.var .local (ofString "n")))
          (.call (some (none, none)) (ofString "trap_with") [.const 1])
          .skip) =
        evaluateHOLFiniteState pState (.call (some (none, none)) (ofString "trap_with") [.const 1]) := by
      rw [evaluateHOLFiniteState_ite, hev1, if_pos hcmp1]; simp
    rw [hite1]
    have hno_none := evaluate_call_trap_with_no_none pState 1 hcode
    have hno_ret := fun w => evaluate_call_trap_with_no_return pState 1 w hcode
    rcases htr : evaluateHOLFiniteState pState (.call (some (none, none)) (ofString "trap_with") [.const 1]) with ⟨r1, s1⟩
    rw [htr] at hno_none hno_ret
    cases r1 with
    | none => exact absurd rfl hno_none
    | some r1' => intro retVal hret; exact False.elim (hno_ret retVal hret)
  · have hite1 : evaluateHOLFiniteState pState
        (.ite (.cmp .lower (.op .sub [.const cMax, .var .local (ofString "p")])
            (.var .local (ofString "n")))
          (.call (some (none, none)) (ofString "trap_with") [.const 1])
          .skip) = (none, pState) := by
      rw [evaluateHOLFiniteState_ite, hev1, if_neg hcmp1]; simp [evaluateHOLFiniteState_skip]
    rw [hite1]
    dsimp only
    rw [evaluateHOLFiniteState_dec_total]
    let q : BitVec 64 := (p + (n + 7)) &&& ((0 : BitVec 64) - 8)
    have hq_eval : @evalHOLExact 64 F _ pState.toExact
        (fun a => Classical.propDecidable (pState.memaddrs a))
        (.op .and [.op .add [.var .local (ofString "p"), .var .local (ofString "n"), .const 7],
          .op .sub [.const 0, .const 8]]) = some (.val (.word q)) := by
      simp only [evalHOLExact, evalListHOLExact, hp_loc, hn_loc,
        wordOpHOL, wordOp, valueIsWord, valueWord, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr]
      exact congrArg (fun w => some (ValueHOL.val (HolWordLab.word w))) (alloc_q_word_eq p n)
    dsimp only
    rw [hq_eval]
    have hsh_q : shapeEqHOL .one (shapeOfHOLExact (.val (.word q))) = true := by
      simp [shapeEqHOL, shapeOfHOLExact]
    dsimp only
    rw [if_pos hsh_q]
    dsimp only
    let qState := setVarHOLFinite (ofString "q") (.val (.word q)) pState
    have hq_loc : qState.locals.lookup (ofString "q") = some (.val (.word q)) := by
      simp [qState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hp_loc_q : qState.locals.lookup (ofString "p") = some (.val (.word p)) := by
      simp [qState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hp_loc,
        show ofString "q" ≠ ofString "p" by decide]
    rw [evaluateHOLFiniteState_seq_line780]
    have hev2 : @evalHOLExact 64 F _ qState.toExact
        (fun a => Classical.propDecidable (qState.memaddrs a))
        (.cmp .lower (.const cMax) (.var .local (ofString "q"))) =
        some (.val (.word (if cMax.toNat < q.toNat then 1 else 0))) := by
      simp only [evalHOLExact, hq_loc, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, decide_eq_true_eq]
    by_cases hcmp2 : cMax.toNat < q.toNat
    · have hite2 : evaluateHOLFiniteState qState
          (.ite (.cmp .lower (.const cMax) (.var .local (ofString "q")))
            (.call (some (none, none)) (ofString "trap_with") [.const 1])
            .skip) =
          evaluateHOLFiniteState qState (.call (some (none, none)) (ofString "trap_with") [.const 1]) := by
        rw [evaluateHOLFiniteState_ite, hev2, if_pos hcmp2]; simp
      rw [hite2]
      have hno_none := evaluate_call_trap_with_no_none qState 1 hcode
      have hno_ret := fun w => evaluate_call_trap_with_no_return qState 1 w hcode
      rcases htr : evaluateHOLFiniteState qState (.call (some (none, none)) (ofString "trap_with") [.const 1]) with ⟨r2, s2⟩
      rw [htr] at hno_none hno_ret
      cases r2 with
      | none => exact absurd rfl hno_none
      | some r2' => intro retVal hret; exact False.elim (hno_ret retVal hret)
    · have hite2 : evaluateHOLFiniteState qState
          (.ite (.cmp .lower (.const cMax) (.var .local (ofString "q")))
            (.call (some (none, none)) (ofString "trap_with") [.const 1])
            .skip) = (none, qState) := by
        rw [evaluateHOLFiniteState_ite, hev2, if_neg hcmp2]; simp [evaluateHOLFiniteState_skip]
      rw [hite2]
      dsimp only
      have hp_g : qState.globals.lookup (ofString "heap_ptr") = some (.val (.word p)) := hp_lookup
      have heval_end : evaluateHOLFiniteState qState
          (.seq (.assign .global (ofString "heap_ptr") (.var .local (ofString "q")))
            (.return (.var .local (ofString "p")))) =
          (some (.returned (.val (.word p))),
            emptyLocalsHOLFinite (setGlobalHOLFinite (ofString "heap_ptr") (.val (.word q)) qState)) := by
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
        simp [evalHOLExact, hq_loc, hp_loc_q, isValidValueHOLFinite, isValidValueHOLExact,
          lookupKvarHOLFinite, lookupKvarHOLExact, hp_g,
          shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite, setGlobalHOLFinite,
          evaluateHOLFiniteState_return, sizeOfShapeWithContextHOL]
      rw [heval_end]
      have hcMax : cMax.toNat = 2952790016 := rfl
      have hq_eq : q.toNat = (p + (n + 7)).toNat / 8 * 8 := and_neg8_toNat (p + (n + 7))
      have hq_le : q.toNat ≤ cMax.toNat := Nat.le_of_not_lt hcmp2
      have hsub : (cMax - p).toNat = cMax.toNat - p.toNat := by rw [BitVec.toNat_sub]; omega
      have h7 : (7 : BitVec 64).toNat = 7 := rfl
      have hn7 : (n + 7).toNat = n.toNat + 7 := by rw [BitVec.toNat_add, h7]; omega
      have hsum : (p + (n + 7)).toNat = p.toNat + n.toNat + 7 := by rw [BitVec.toNat_add, hn7]; omega
      intro retVal hret
      injection hret with hr; injection hr with hr'
      change retVal = .val (.word p) ∧ p.toNat + n.toNat ≤ q.toNat ∧ q.toNat ≤ cMax.toNat ∧ q.toNat % 8 = 0 ∧ _
      exact ⟨hr'.symm, by omega, hq_le, by omega, rfl⟩

/-! ## 2. Call-Level Combinators (`Ret`) -/

def Ret {F : Type} (s : PanSemStateFiniteExact 64 F) (p : ProgHOL 64)
    (Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop) : Prop :=
  ∀ v, (evaluateHOLFiniteState s p).1 = some (.returned v) → Φ v (evaluateHOLFiniteState s p).2

theorem Ret.seq {F : Type} {s : PanSemStateFiniteExact 64 F} {a b : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (ha : Ret s a Φ) (hb : ∀ t, evaluateHOLFiniteState s a = (none, t) → Ret t b Φ) :
    Ret s (.seq a b) Φ := by
  intro v hv
  rw [evaluateHOLFiniteState_seq_line780] at hv ⊢
  rcases h : evaluateHOLFiniteState s a with ⟨r, t⟩
  simp only [h] at hv
  try simp only [h]
  cases r with
  | none => exact hb t h v hv
  | some _ =>
    have := ha v (by rw [h]; exact hv)
    rw [h] at this
    exact this

theorem Ret.skip_noret {F : Type} {s : PanSemStateFiniteExact 64 F}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop} : Ret s .skip Φ := by
  intro v hv; rw [evaluateHOLFiniteState_skip] at hv; cases hv

theorem Ret.seq_skip {F : Type} {s : PanSemStateFiniteExact 64 F} {b : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop} (hb : Ret s b Φ) :
    Ret s (.seq .skip b) Φ :=
  Ret.seq Ret.skip_noret fun t ht => by rw [evaluateHOLFiniteState_skip] at ht; injection ht with _ e; rw [← e]; exact hb

theorem Ret.dec {F : Type} {s : PanSemStateFiniteExact 64 F} {x : MlS} {sh : ShapeHOL}
    {init : ExpHOL 64} {body : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (h : ∀ val, evalAt s init = some val →
      Ret (setVarHOLFinite x val s) body
        (fun v t => Φ v { t with
          locals := HolFiniteMapExact.resVarEq t.locals (x, s.locals.lookup x) })) :
    Ret s (.dec x sh init body) Φ := by
  intro v
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  cases hval : @evalHOLExact 64 F _ s.toExact (fun addr => Classical.propDecidable (s.memaddrs addr)) init with
  | none => intro hv; simp at hv
  | some val =>
    dsimp only
    by_cases hsh : shapeEqHOL sh (shapeOfHOLExact val) = true
    · rw [if_pos hsh]; exact h val hval v
    · rw [if_neg hsh]; intro hv; simp at hv

theorem Ret.ret {F : Type} {s : PanSemStateFiniteExact 64 F} {e : ExpHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (h : ∀ val, evalAt s e = some val → Φ val (emptyLocalsHOLFinite s)) :
    Ret s (.return e) Φ := by
  intro v
  rw [evaluateHOLFiniteState_return]
  cases hval : @evalHOLExact 64 F _ s.toExact (fun addr => Classical.propDecidable (s.memaddrs addr)) e with
  | none => intro hv; simp at hv
  | some val =>
    dsimp only
    by_cases hsz : sizeOfShapeWithContextHOL s.structs (shapeOfHOLExact val) ≤ 32
    · rw [if_pos hsz]
      intro hv
      injection hv with hv1; injection hv1 with hv2
      subst hv2
      exact h _ hval
    · rw [if_neg hsz]; intro hv; simp at hv

theorem Ret.seq_storeW {F : Type} {s : PanSemStateFiniteExact 64 F} {d e : ExpHOL 64}
    {b : ProgHOL 64} {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (a w : BitVec 64) (hd : evalAt s d = some (.val (.word a))) (he : evalAt s e = some (.val (.word w)))
    (hb : s.memaddrs a → Ret { s with memory := updW s.memory a w } b Φ) :
    Ret s (.seq (.store d e) b) Φ := by
  refine Ret.seq ?_ ?_
  · intro v hv
    have := (evaluate_store_control_frame s d e).1
    rcases this with h | h <;> rw [h] at hv <;> simp at hv
  · intro t ht
    rw [evaluateHOLFiniteState_store] at ht
    unfold evalAt at hd he
    rw [hd] at ht; dsimp only at ht
    rw [he] at ht; dsimp only at ht
    rcases hm : @panMemStoresHOL 64 _ a (flattenHOL (.val (.word w))) s.memaddrs (fun addr => Classical.propDecidable (s.memaddrs addr)) s.memory with _ | m
    · rw [hm] at ht; simp at ht
    · rw [hm] at ht; injection ht with _ hteq; rw [← hteq]
      obtain ⟨hdom, rfl⟩ := stores_word _ hm
      exact hb hdom

theorem Ret.seq_assign {F : Type} {s : PanSemStateFiniteExact 64 F} {x : MlS} {e : ExpHOL 64}
    {b : ProgHOL 64} {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (w : BitVec 64) (he : evalAt s e = some (.val (.word w)))
    (hb : Ret (setVarHOLFinite x (.val (.word w)) s) b Φ) :
    Ret s (.seq (.assign .local x e) b) Φ := by
  refine Ret.seq ?_ ?_
  · intro v hv
    rw [evaluateHOLFiniteState_assign] at hv
    unfold evalAt at he
    rw [he] at hv; dsimp only at hv
    by_cases hvld : s.isValidValueHOLFinite .local x (.val (.word w)) = true
    · rw [if_pos hvld] at hv; simp at hv
    · rw [if_neg hvld] at hv; simp at hv
  · intro t ht
    rw [evaluateHOLFiniteState_assign] at ht
    unfold evalAt at he
    rw [he] at ht; dsimp only at ht
    by_cases hvld : s.isValidValueHOLFinite .local x (.val (.word w)) = true
    · rw [if_pos hvld] at ht; injection ht with _ hteq; rw [← hteq]; exact hb
    · rw [if_neg hvld] at ht; simp at ht

theorem Ret.ite {F : Type} {s : PanSemStateFiniteExact 64 F} {c : ExpHOL 64}
    {y n : ProgHOL 64} {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (h : ∀ cw : BitVec 64, evalAt s c = some (.val (.word cw)) →
      (cw ≠ 0 → Ret s y Φ) ∧ (cw = 0 → Ret s n Φ)) :
    Ret s (.ite c y n) Φ := by
  intro v
  rw [evaluateHOLFiniteState_ite]
  cases hcw : @evalHOLExact 64 F _ s.toExact (fun addr => Classical.propDecidable (s.memaddrs addr)) c with
  | none => intro hv; cases hv
  | some vc =>
    cases vc with
    | val wl =>
      cases wl with
      | word cw =>
        dsimp only
        by_cases hz : cw = 0
        · rw [if_pos hz]; exact (h cw hcw).2 hz v
        · rw [if_neg hz]; exact (h cw hcw).1 hz v
    | rStruct _ => intro hv; cases hv
    | nStruct _ _ => intro hv; cases hv

theorem Ret.seq_ite {F : Type} {s : PanSemStateFiniteExact 64 F} {c : ExpHOL 64}
    {y n b : ProgHOL 64} {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (h : ∀ cw : BitVec 64, evalAt s c = some (.val (.word cw)) →
      (cw ≠ 0 → Ret s (.seq y b) Φ) ∧ (cw = 0 → Ret s (.seq n b) Φ)) :
    Ret s (.seq (.ite c y n) b) Φ := by
  intro v
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
  cases hcw : @evalHOLExact 64 F _ s.toExact (fun addr => Classical.propDecidable (s.memaddrs addr)) c with
  | none => intro hv; cases hv
  | some vc =>
    cases vc with
    | val wl =>
      cases wl with
      | word cw =>
        dsimp only
        by_cases hz : cw = 0
        · rw [if_pos hz]
          have := (h cw hcw).2 hz v
          rw [evaluateHOLFiniteState_seq_line780] at this
          exact this
        · rw [if_neg hz]
          have := (h cw hcw).1 hz v
          rw [evaluateHOLFiniteState_seq_line780] at this
          exact this
    | rStruct _ => intro hv; cases hv
    | nStruct _ _ => intro hv; cases hv

theorem Ret.decCall1 {F : Type} {s : PanSemStateFiniteExact 64 F} {x fname p1 : MlS}
    {e1 : ExpHOL 64} {cont fbody : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hcode : s.code = originalRuntimeCode)
    (hlook : originalRuntimeCode.lookup fname = some ([(p1, .one)], fbody, .one))
    (w1 : BitVec 64) (he1 : evalAt s e1 = some (.val (.word w1)))
    (hk : ∀ w post,
      evaluateHOLFiniteState (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (p1, .val (.word w1)))) fbody =
        (some (.returned (.val (.word w))), post) →
      Ret (setVarHOLFinite x (.val (.word w)) { post with locals := s.locals }) cont
        (fun v t => Φ v { t with locals := HolFiniteMapExact.resVarEq t.locals (x, s.locals.lookup x) })) :
    Ret s (.decCall x .one fname [e1] cont) Φ := by
  intro v
  rw [evaluateHOLFiniteState_decCall_total]
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [e1] =
      some [.val (.word w1)] := by
    unfold evalAt at he1
    simp [evalListHOLFinite, evalListHOLExact, he1]
  have hl := pan_one_word_lookup s.code.lookup fname p1 fbody w1 (by rw [hcode]; exact hlook)
  rw [hargs]; dsimp only
  rw [hl]; dsimp only
  by_cases hcz : s.clock = 0
  · rw [if_pos hcz]; intro hv; cases hv
  · rw [if_neg hcz]
    rw [fixClockHOLFinite_evaluateState]
    cases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (p1, .val (.word w1)))) fbody with
    | mk r post =>
      dsimp only
      cases r with
      | none => intro hv; cases hv
      | some r =>
        cases r with
        | returned rv =>
          dsimp only
          by_cases hsh : (shapeEqHOL (shapeOfHOLExact rv) .one && shapeEqHOL (shapeOfHOLExact rv) .one) = true
          · rw [if_pos hsh]
            rcases rv with ⟨⟨w⟩⟩ | fs | ⟨nm, fs⟩
            · exact hk w post hrun v
            · simp [shapeOfHOLExact, shapeEqHOL] at hsh
            · simp [shapeOfHOLExact, shapeEqHOL] at hsh
          · rw [if_neg hsh]; intro hv; cases hv
        | _ => intro hv; cases hv

theorem Ret.decCall2 {F : Type} {s : PanSemStateFiniteExact 64 F} {x fname p1 p2 : MlS}
    {e1 e2 : ExpHOL 64} {cont fbody : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hcode : s.code = originalRuntimeCode) (hne : p1 ≠ p2)
    (hlook : originalRuntimeCode.lookup fname = some ([(p1, .one), (p2, .one)], fbody, .one))
    (w1 w2 : BitVec 64)
    (he1 : evalAt s e1 = some (.val (.word w1)))
    (he2 : evalAt s e2 = some (.val (.word w2)))
    (hk : ∀ w post,
      evaluateHOLFiniteState (callEntryStateHOLFinite s ((HolFiniteMapExact.empty.update (p1, .val (.word w1))).update (p2, .val (.word w2)))) fbody =
        (some (.returned (.val (.word w))), post) →
      Ret (setVarHOLFinite x (.val (.word w)) { post with locals := s.locals }) cont
        (fun v t => Φ v { t with locals := HolFiniteMapExact.resVarEq t.locals (x, s.locals.lookup x) })) :
    Ret s (.decCall x .one fname [e1, e2] cont) Φ := by
  intro v
  rw [evaluateHOLFiniteState_decCall_total]
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [e1, e2] =
      some [.val (.word w1), .val (.word w2)] := by
    unfold evalAt at he1 he2
    simp [evalListHOLFinite, evalListHOLExact, he1, he2]
  have hl := pan_two_word_lookup s.code.lookup fname p1 p2 fbody w1 w2 hne (by rw [hcode]; exact hlook)
  rw [hargs]; dsimp only
  rw [hl]; dsimp only
  by_cases hcz : s.clock = 0
  · rw [if_pos hcz]; intro hv; cases hv
  · rw [if_neg hcz]
    rw [fixClockHOLFinite_evaluateState]
    cases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s ((HolFiniteMapExact.empty.update (p1, .val (.word w1))).update (p2, .val (.word w2)))) fbody with
    | mk r post =>
      dsimp only
      cases r with
      | none => intro hv; cases hv
      | some r =>
        cases r with
        | returned rv =>
          dsimp only
          by_cases hsh : (shapeEqHOL (shapeOfHOLExact rv) .one && shapeEqHOL (shapeOfHOLExact rv) .one) = true
          · rw [if_pos hsh]
            rcases rv with ⟨⟨w⟩⟩ | fs | ⟨nm, fs⟩
            · exact hk w post hrun v
            · simp [shapeOfHOLExact, shapeEqHOL] at hsh
            · simp [shapeOfHOLExact, shapeEqHOL] at hsh
          · rw [if_neg hsh]; intro hv; cases hv
        | _ => intro hv; cases hv

theorem Ret.decCall3 {F : Type} {s : PanSemStateFiniteExact 64 F} {x fname p1 p2 p3 : MlS}
    {e1 e2 e3 : ExpHOL 64} {cont fbody : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hcode : s.code = originalRuntimeCode) (hne12 : p1 ≠ p2) (hne13 : p1 ≠ p3) (hne23 : p2 ≠ p3)
    (hlook : originalRuntimeCode.lookup fname = some ([(p1, .one), (p2, .one), (p3, .one)], fbody, .one))
    (w1 w2 w3 : BitVec 64)
    (he1 : evalAt s e1 = some (.val (.word w1)))
    (he2 : evalAt s e2 = some (.val (.word w2)))
    (he3 : evalAt s e3 = some (.val (.word w3)))
    (hk : ∀ w post,
      evaluateHOLFiniteState (callEntryStateHOLFinite s (((HolFiniteMapExact.empty.update (p1, .val (.word w1))).update (p2, .val (.word w2))).update (p3, .val (.word w3)))) fbody =
        (some (.returned (.val (.word w))), post) →
      Ret (setVarHOLFinite x (.val (.word w)) { post with locals := s.locals }) cont
        (fun v t => Φ v { t with locals := HolFiniteMapExact.resVarEq t.locals (x, s.locals.lookup x) })) :
    Ret s (.decCall x .one fname [e1, e2, e3] cont) Φ := by
  intro v
  rw [evaluateHOLFiniteState_decCall_total]
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [e1, e2, e3] =
      some [.val (.word w1), .val (.word w2), .val (.word w3)] := by
    unfold evalAt at he1 he2 he3
    simp [evalListHOLFinite, evalListHOLExact, he1, he2, he3]
  have hl := pan_three_word_lookup s.code.lookup fname p1 p2 p3 fbody w1 w2 w3 hne12 hne13 hne23 (by rw [hcode]; exact hlook)
  rw [hargs]; dsimp only
  rw [hl]; dsimp only
  by_cases hcz : s.clock = 0
  · rw [if_pos hcz]; intro hv; cases hv
  · rw [if_neg hcz]
    rw [fixClockHOLFinite_evaluateState]
    cases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s (((HolFiniteMapExact.empty.update (p1, .val (.word w1))).update (p2, .val (.word w2))).update (p3, .val (.word w3)))) fbody with
    | mk r post =>
      dsimp only
      cases r with
      | none => intro hv; cases hv
      | some r =>
        cases r with
        | returned rv =>
          dsimp only
          by_cases hsh : (shapeEqHOL (shapeOfHOLExact rv) .one && shapeEqHOL (shapeOfHOLExact rv) .one) = true
          · rw [if_pos hsh]
            rcases rv with ⟨⟨w⟩⟩ | fs | ⟨nm, fs⟩
            · exact hk w post hrun v
            · simp [shapeOfHOLExact, shapeEqHOL] at hsh
            · simp [shapeOfHOLExact, shapeEqHOL] at hsh
          · rw [if_neg hsh]; intro hv; cases hv
        | _ => intro hv; cases hv

theorem call_none_noRet {F : Type} (s : PanSemStateFiniteExact 64 F)
    (fname : MlS) (args : List (ExpHOL 64)) (v : ValueHOL 64) :
    (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).1 ≠ some (.returned v) := by
  rw [evaluateHOLFiniteState_call]
  rcases ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vs
  · simp
  · dsimp only
    rcases hl : lookupCodeHOLFinite s.code.lookup fname vs with _ | ⟨fb, cl, rs⟩
    · simp
    · dsimp only
      by_cases hcz : s.clock = 0
      · rw [if_pos hcz]; simp
      · rw [if_neg hcz]
        rcases evaluateHOLFiniteState _ _ with ⟨r, _⟩
        cases r with
        | none => simp
        | some r =>
          cases r with
          | returned rv =>
            try dsimp only
            by_cases hsh : shapeEqHOL (shapeOfHOLExact rv) rs = true
            · rw [if_pos hsh]; simp
            · rw [if_neg hsh]; simp
          | _ => simp

theorem Ret.seq_call1 {F : Type} {s : PanSemStateFiniteExact 64 F} {fname p1 : MlS}
    {e1 : ExpHOL 64} {cont fbody : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hcode : s.code = originalRuntimeCode)
    (hlook : originalRuntimeCode.lookup fname = some ([(p1, .one)], fbody, .one))
    (w1 : BitVec 64) (he1 : evalAt s e1 = some (.val (.word w1)))
    (hk : ∀ w post,
      evaluateHOLFiniteState (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (p1, .val (.word w1)))) fbody =
        (some (.returned (.val (.word w))), post) →
      Ret { post with locals := s.locals } cont Φ) :
    Ret s (.seq (.call (some (none, none)) fname [e1]) cont) Φ := by
  refine Ret.seq (fun v hv => False.elim (call_none_noRet s fname [e1] v hv)) ?_
  intro t ht
  rw [evaluateHOLFiniteState_call] at ht
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [e1] =
      some [.val (.word w1)] := by
    unfold evalAt at he1
    simp [evalListHOLFinite, evalListHOLExact, he1]
  have hl := pan_one_word_lookup s.code.lookup fname p1 fbody w1 (by rw [hcode]; exact hlook)
  rw [hargs] at ht; dsimp only at ht
  rw [hl] at ht; dsimp only at ht
  by_cases hcz : s.clock = 0
  · rw [if_pos hcz] at ht; simp at ht
  · rw [if_neg hcz] at ht
    rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (p1, .val (.word w1)))) fbody with ⟨r, post⟩
    rw [hrun] at ht
    rcases r with _ | r
    · simp at ht
    · cases r with
      | returned rv =>
        try dsimp only at ht
        by_cases hsh : shapeEqHOL (shapeOfHOLExact rv) .one = true
        · rw [if_pos hsh] at ht
          rcases rv with ⟨⟨w⟩⟩ | fs | ⟨nm, fs⟩
          · injection ht with _ hteq; rw [← hteq]; exact hk w post hrun
          · simp [shapeOfHOLExact, shapeEqHOL] at hsh
          · simp [shapeOfHOLExact, shapeEqHOL] at hsh
        · rw [if_neg hsh] at ht; simp at ht
      | _ => simp at ht

theorem Ret.seq_call3 {F : Type} {s : PanSemStateFiniteExact 64 F} {fname p1 p2 p3 : MlS}
    {e1 e2 e3 : ExpHOL 64} {cont fbody : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hcode : s.code = originalRuntimeCode) (hne12 : p1 ≠ p2) (hne13 : p1 ≠ p3) (hne23 : p2 ≠ p3)
    (hlook : originalRuntimeCode.lookup fname = some ([(p1, .one), (p2, .one), (p3, .one)], fbody, .one))
    (w1 w2 w3 : BitVec 64)
    (he1 : evalAt s e1 = some (.val (.word w1)))
    (he2 : evalAt s e2 = some (.val (.word w2)))
    (he3 : evalAt s e3 = some (.val (.word w3)))
    (hk : ∀ w post,
      evaluateHOLFiniteState (callEntryStateHOLFinite s (((HolFiniteMapExact.empty.update (p1, .val (.word w1))).update (p2, .val (.word w2))).update (p3, .val (.word w3)))) fbody =
        (some (.returned (.val (.word w))), post) →
      Ret { post with locals := s.locals } cont Φ) :
    Ret s (.seq (.call (some (none, none)) fname [e1, e2, e3]) cont) Φ := by
  refine Ret.seq (fun v hv => False.elim (call_none_noRet s fname [e1, e2, e3] v hv)) ?_
  intro t ht
  rw [evaluateHOLFiniteState_call] at ht
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [e1, e2, e3] =
      some [.val (.word w1), .val (.word w2), .val (.word w3)] := by
    unfold evalAt at he1 he2 he3
    simp [evalListHOLFinite, evalListHOLExact, he1, he2, he3]
  have hl := pan_three_word_lookup s.code.lookup fname p1 p2 p3 fbody w1 w2 w3 hne12 hne13 hne23 (by rw [hcode]; exact hlook)
  rw [hargs] at ht; dsimp only at ht
  rw [hl] at ht; dsimp only at ht
  by_cases hcz : s.clock = 0
  · rw [if_pos hcz] at ht; simp at ht
  · rw [if_neg hcz] at ht
    rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s (((HolFiniteMapExact.empty.update (p1, .val (.word w1))).update (p2, .val (.word w2))).update (p3, .val (.word w3)))) fbody with ⟨r, post⟩
    rw [hrun] at ht
    rcases r with _ | r
    · simp at ht
    · cases r with
      | returned rv =>
        try dsimp only at ht
        by_cases hsh : shapeEqHOL (shapeOfHOLExact rv) .one = true
        · rw [if_pos hsh] at ht
          rcases rv with ⟨⟨w⟩⟩ | fs | ⟨nm, fs⟩
          · injection ht with _ hteq; rw [← hteq]; exact hk w post hrun
          · simp [shapeOfHOLExact, shapeEqHOL] at hsh
          · simp [shapeOfHOLExact, shapeEqHOL] at hsh
        · rw [if_neg hsh] at ht; simp at ht
      | _ => simp at ht

end InitECandidate.Solver.Wave8GuestInv.SoloHtabSet
