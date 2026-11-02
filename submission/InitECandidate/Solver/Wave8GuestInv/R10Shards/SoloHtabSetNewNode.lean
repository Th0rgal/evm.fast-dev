import InitECandidate.Solver.Wave8GuestInv.R10Shards.SoloHtabSetNodes

/-! Normal-form (`NS`) local-insensitive `Ret` combinators and `htab_new_node` postcondition. -/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
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

/-! ## 1. Normal-Form States (`NS`) and Local-Insensitive `Ret` Combinators -/

def NS {F : Type} (s : PanSemStateFiniteExact 64 F) (L G : HolFiniteMapExact MlS (ValueHOL 64))
    (M : BitVec 64 → HolWordLab 64) (C : Nat) : PanSemStateFiniteExact 64 F :=
  { s with locals := L, globals := G, memory := M, clock := C }

section NSlemmas
variable {F : Type} (s : PanSemStateFiniteExact 64 F) (L G : HolFiniteMapExact MlS (ValueHOL 64))
  (M : BitVec 64 → HolWordLab 64) (C : Nat)
@[simp] theorem NS_locals : (NS s L G M C).locals = L := rfl
@[simp] theorem NS_globals : (NS s L G M C).globals = G := rfl
@[simp] theorem NS_memory : (NS s L G M C).memory = M := rfl
@[simp] theorem NS_clock : (NS s L G M C).clock = C := rfl
@[simp] theorem NS_code : (NS s L G M C).code = s.code := rfl
@[simp] theorem NS_memaddrs : (NS s L G M C).memaddrs = s.memaddrs := rfl
@[simp] theorem NS_shMemaddrs : (NS s L G M C).shMemaddrs = s.shMemaddrs := rfl
@[simp] theorem NS_baseAddr : (NS s L G M C).baseAddr = s.baseAddr := rfl
@[simp] theorem NS_be : (NS s L G M C).be = s.be := rfl
@[simp] theorem NS_structs : (NS s L G M C).structs = s.structs := rfl
@[simp] theorem NS_toExact_memaddrs : (NS s L G M C).toExact.memaddrs = s.memaddrs := rfl
@[simp] theorem NS_toExact_memory : (NS s L G M C).toExact.memory = M := rfl
end NSlemmas

def LocFreePost {F : Type} (Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop) : Prop :=
  ∀ v (t : PanSemStateFiniteExact 64 F) L', Φ v { t with locals := L' } → Φ v t

theorem Ret.ite_ret {F : Type} {s : PanSemStateFiniteExact 64 F} {c : ExpHOL 64}
    {y b : ProgHOL 64} {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hyn : ∀ u : PanSemStateFiniteExact 64 F, (evaluateHOLFiniteState s y).1 ≠ none)
    (h : ∀ cw : BitVec 64, evalAt s c = some (.val (.word cw)) →
      (cw ≠ 0 → Ret s y Φ) ∧ (cw = 0 → Ret s b Φ)) :
    Ret s (.seq (.ite c y .skip) b) Φ := by
  refine Ret.seq_ite fun cw hcw => ⟨fun hnz => ?_, fun hz => Ret.seq_skip ((h cw hcw).2 hz)⟩
  exact Ret.seq ((h cw hcw).1 hnz) fun u hu => False.elim (hyn u (congrArg Prod.fst hu))

theorem noFlow_dec {F : Type} {s : PanSemStateFiniteExact 64 F} {x : MlS} {sh : ShapeHOL}
    {init : ExpHOL 64} {body : ProgHOL 64}
    (hb : ∀ s' : PanSemStateFiniteExact 64 F, (evaluateHOLFiniteState s' body).1 ≠ none) :
    (evaluateHOLFiniteState s (.dec x sh init body)).1 ≠ none := by
  rw [evaluateHOLFiniteState_dec_total]; dsimp only
  split
  · simp
  · split
    · exact hb _
    · simp

theorem noFlow_seq_right {F : Type} {s : PanSemStateFiniteExact 64 F} {a b : ProgHOL 64}
    (hb : ∀ s' : PanSemStateFiniteExact 64 F, (evaluateHOLFiniteState s' b).1 ≠ none) :
    (evaluateHOLFiniteState s (.seq a b)).1 ≠ none := by
  rw [evaluateHOLFiniteState_seq_line780]
  rcases evaluateHOLFiniteState s a with ⟨r, m⟩
  cases r with
  | none => exact hb m
  | some _ => simp

theorem noFlow_ret {F : Type} {s : PanSemStateFiniteExact 64 F} {e : ExpHOL 64} :
    (evaluateHOLFiniteState s (.return e)).1 ≠ none := by
  rw [evaluateHOLFiniteState_return]
  split
  · simp
  · split <;> simp

theorem ev_var_node_load {F : Type} (s : PanSemStateFiniteExact 64 F) (x : MlS) (nd w off : BitVec 64)
    (h1 : s.locals.lookup (ofString "nodes") = some (.val (.word nd)))
    (h2 : s.locals.lookup x = some (.val (.word w))) (v : ValueHOL 64)
    (h : evalAt s (.load .one (.op .add [.var .local (ofString "nodes"),
      .panop .mul [.var .local x, .const 32], .const off])) = some v) :
    s.memaddrs (nd + w * 32 + off) ∧ v = .val (s.memory (nd + w * 32 + off)) := by
  simp [evalAt, evalHOLExact, evalListHOLExact, h1, h2, panOpHOL, valueIsWord, valueWord, wordOpHOL,
    wordOp, memLoadHOLExact] at h
  rw [BitVec.add_assoc]
  exact ⟨h.1, h.2.symm⟩

theorem Ret.of_NS {F : Type} {s : PanSemStateFiniteExact 64 F} {p : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (h : Ret (NS s s.locals s.globals s.memory s.clock) p Φ) : Ret s p Φ := by
  cases s; exact h

theorem Ret.ns_dec_lf {F : Type} {s : PanSemStateFiniteExact 64 F} {L G} {M C} {x : MlS}
    {sh : ShapeHOL} {init : ExpHOL 64} {body : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hLF : LocFreePost Φ)
    (h : ∀ val, evalAt (NS s L G M C) init = some val →
      Ret (NS s (L.update (x, val)) G M C) body Φ) :
    Ret (NS s L G M C) (.dec x sh init body) Φ :=
  Ret.dec fun val hval v hv => hLF v _ _ (h val hval v hv)

theorem Ret.ns_storeW {F : Type} {s : PanSemStateFiniteExact 64 F} {L G} {M C}
    {d e : ExpHOL 64} {b : ProgHOL 64} {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (a w : BitVec 64) (hd : evalAt (NS s L G M C) d = some (.val (.word a)))
    (he : evalAt (NS s L G M C) e = some (.val (.word w)))
    (hb : s.memaddrs a → Ret (NS s L G (updW M a w) C) b Φ) :
    Ret (NS s L G M C) (.seq (.store d e) b) Φ :=
  Ret.seq_storeW a w hd he hb

theorem Ret.ns_assign {F : Type} {s : PanSemStateFiniteExact 64 F} {L G} {M C}
    {x : MlS} {e : ExpHOL 64} {b : ProgHOL 64} {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (w : BitVec 64) (he : evalAt (NS s L G M C) e = some (.val (.word w)))
    (hb : Ret (NS s (L.update (x, .val (.word w))) G M C) b Φ) :
    Ret (NS s L G M C) (.seq (.assign .local x e) b) Φ :=
  Ret.seq_assign w he hb

theorem Ret.ns_ret {F : Type} {s : PanSemStateFiniteExact 64 F} {L G} {M C} {e : ExpHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (h : ∀ val, evalAt (NS s L G M C) e = some val →
      Φ val (NS s HolFiniteMapExact.empty G M C)) :
    Ret (NS s L G M C) (.return e) Φ :=
  Ret.ret h

theorem Ret.decCall1_lf {F : Type} {s : PanSemStateFiniteExact 64 F} {x fname p1 : MlS}
    {e1 : ExpHOL 64} {cont fbody : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hLF : LocFreePost Φ)
    (hcode : s.code = originalRuntimeCode)
    (hlook : originalRuntimeCode.lookup fname = some ([(p1, .one)], fbody, .one))
    (w1 : BitVec 64) (he1 : evalAt s e1 = some (.val (.word w1)))
    (hk : ∀ w post,
      evaluateHOLFiniteState (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (p1, .val (.word w1)))) fbody =
        (some (.returned (.val (.word w))), post) →
      Ret (setVarHOLFinite x (.val (.word w)) { post with locals := s.locals }) cont Φ) :
    Ret s (.decCall x .one fname [e1] cont) Φ :=
  Ret.decCall1 hcode hlook w1 he1 fun w post hrun v hv => hLF v _ _ (hk w post hrun v hv)

theorem Ret.decCall2_lf {F : Type} {s : PanSemStateFiniteExact 64 F} {x fname p1 p2 : MlS}
    {e1 e2 : ExpHOL 64} {cont fbody : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hLF : LocFreePost Φ)
    (hcode : s.code = originalRuntimeCode) (hne : p1 ≠ p2)
    (hlook : originalRuntimeCode.lookup fname = some ([(p1, .one), (p2, .one)], fbody, .one))
    (w1 w2 : BitVec 64)
    (he1 : evalAt s e1 = some (.val (.word w1)))
    (he2 : evalAt s e2 = some (.val (.word w2)))
    (hk : ∀ w post,
      evaluateHOLFiniteState (callEntryStateHOLFinite s ((HolFiniteMapExact.empty.update (p1, .val (.word w1))).update (p2, .val (.word w2)))) fbody =
        (some (.returned (.val (.word w))), post) →
      Ret (setVarHOLFinite x (.val (.word w)) { post with locals := s.locals }) cont Φ) :
    Ret s (.decCall x .one fname [e1, e2] cont) Φ :=
  Ret.decCall2 hcode hne hlook w1 w2 he1 he2 fun w post hrun v hv => hLF v _ _ (hk w post hrun v hv)

theorem Ret.decCall3_lf {F : Type} {s : PanSemStateFiniteExact 64 F} {x fname p1 p2 p3 : MlS}
    {e1 e2 e3 : ExpHOL 64} {cont fbody : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hLF : LocFreePost Φ)
    (hcode : s.code = originalRuntimeCode) (hne12 : p1 ≠ p2) (hne13 : p1 ≠ p3) (hne23 : p2 ≠ p3)
    (hlook : originalRuntimeCode.lookup fname = some ([(p1, .one), (p2, .one), (p3, .one)], fbody, .one))
    (w1 w2 w3 : BitVec 64)
    (he1 : evalAt s e1 = some (.val (.word w1)))
    (he2 : evalAt s e2 = some (.val (.word w2)))
    (he3 : evalAt s e3 = some (.val (.word w3)))
    (hk : ∀ w post,
      evaluateHOLFiniteState (callEntryStateHOLFinite s (((HolFiniteMapExact.empty.update (p1, .val (.word w1))).update (p2, .val (.word w2))).update (p3, .val (.word w3)))) fbody =
        (some (.returned (.val (.word w))), post) →
      Ret (setVarHOLFinite x (.val (.word w)) { post with locals := s.locals }) cont Φ) :
    Ret s (.decCall x .one fname [e1, e2, e3] cont) Φ :=
  Ret.decCall3 hcode hne12 hne13 hne23 hlook w1 w2 w3 he1 he2 he3 fun w post hrun v hv => hLF v _ _ (hk w post hrun v hv)

/-! ## 2. Structured Node-Allocation Invariant (`NodeState`) -/

def NodeState {F : Type} (s : PanSemStateFiniteExact 64 F) (t : Nat) (A Fr : List Nat) : Prop :=
  HtabBlocks s t ∧
  (A ++ Fr).Nodup ∧
  (∀ x, x ∈ A ++ Fr ↔ 1 ≤ x ∧ x < hdr s t 8) ∧
  FreeChainF (nodeF s (hdr s t 5)) (hdr s t 9) Fr

theorem htabBlocks_cell_sep {F : Type} {s : PanSemStateFiniteExact 64 F} {t : Nat}
    (hB : HtabBlocks s t) :
    (∀ k < 11, ∀ n < hdr s t 10 + 1, ∀ off, (off = 0 ∨ off = 8 ∨ off = 16 ∨ off = 24) →
      BitVec.ofNat 64 (t + 8 * k) ≠ BitVec.ofNat 64 (hdr s t 5 + 32 * n + off)) ∧
    (∀ k < 11, ∀ i < hdr s t 10 + 1,
      BitVec.ofNat 64 (t + 8 * k) ≠ BitVec.ofNat 64 (hdr s t 6 + 8 * i)) ∧
    (∀ n < hdr s t 10 + 1, ∀ off, (off = 0 ∨ off = 8 ∨ off = 16 ∨ off = 24) →
      ∀ i < hdr s t 10 + 1,
      BitVec.ofNat 64 (hdr s t 6 + 8 * i) ≠ BitVec.ofNat 64 (hdr s t 5 + 32 * n + off)) ∧
    (∀ n1 < hdr s t 10 + 1, ∀ off1, (off1 = 0 ∨ off1 = 8 ∨ off1 = 16 ∨ off1 = 24) →
      ∀ n2 < hdr s t 10 + 1, ∀ off2, (off2 = 0 ∨ off2 = 8 ∨ off2 = 16 ∨ off2 = 24) →
      (n1 ≠ n2 ∨ off1 ≠ off2) →
      BitVec.ofNat 64 (hdr s t 5 + 32 * n1 + off1) ≠ BitVec.ofNat 64 (hdr s t 5 + 32 * n2 + off2)) ∧
    (∀ i1 < hdr s t 10 + 1, ∀ i2 < hdr s t 10 + 1, i1 ≠ i2 →
      BitVec.ofNat 64 (hdr s t 6 + 8 * i1) ≠ BitVec.ofNat 64 (hdr s t 6 + 8 * i2)) := by
  have hhe : heapEnd = 33806089704 := rfl
  have hhdr_in := (hB.1 (t, 88) (by simp [htabFootprint])).1
  have hnd_in := (hB.1 (hdr s t 5, (hdr s t 10 + 1) * 32) (by simp [htabFootprint])).1
  have hord_in := (hB.1 (hdr s t 6, (hdr s t 10 + 1) * 8) (by simp [htabFootprint])).1
  unfold Inside at hhdr_in hnd_in hord_in
  have hpair := hB.2.1
  simp only [htabFootprint, List.pairwise_cons, List.mem_cons] at hpair
  have hd_tn : Disj (t, 88) (hdr s t 5, (hdr s t 10 + 1) * 32) := hpair.1 _ (Or.inr (Or.inl rfl))
  have hd_to : Disj (t, 88) (hdr s t 6, (hdr s t 10 + 1) * 8) := hpair.1 _ (Or.inr (Or.inr (Or.inl rfl)))
  have hd_no : Disj (hdr s t 5, (hdr s t 10 + 1) * 32) (hdr s t 6, (hdr s t 10 + 1) * 8) := hpair.2.2.1 _ (Or.inl rfl)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k hk n hn off hoff
    apply ofNat64_ne_of_ne_of_lt (by omega) (by rcases hoff with rfl | rfl | rfl | rfl <;> omega)
    unfold Disj at hd_tn
    rcases hoff with rfl | rfl | rfl | rfl <;> omega
  · intro k hk i hi
    apply ofNat64_ne_of_ne_of_lt (by omega) (by omega)
    unfold Disj at hd_to; omega
  · intro n hn off hoff i hi
    apply ofNat64_ne_of_ne_of_lt (by omega) (by rcases hoff with rfl | rfl | rfl | rfl <;> omega)
    unfold Disj at hd_no
    rcases hoff with rfl | rfl | rfl | rfl <;> omega
  · intro n1 hn1 off1 hoff1 n2 hn2 off2 hoff2 hne
    apply ofNat64_ne_of_ne_of_lt
      (by rcases hoff1 with rfl | rfl | rfl | rfl <;> omega)
      (by rcases hoff2 with rfl | rfl | rfl | rfl <;> omega)
    rcases hoff1 with rfl | rfl | rfl | rfl <;> rcases hoff2 with rfl | rfl | rfl | rfl <;> omega
  · intro i1 hi1 i2 hi2 hne
    apply ofNat64_ne_of_ne_of_lt (by omega) (by omega)
    omega

theorem wordsOK_updW {F : Type} (s : PanSemStateFiniteExact 64 F)
    (a w : BitVec 64) (i : Ivl) (hi : WordsOK s i) :
    WordsOK { s with memory := updW s.memory a w } i := by
  refine ⟨hi.1, hi.2.1, fun k hk => ?_⟩
  obtain ⟨u, hdom, hu⟩ := hi.2.2 k hk
  by_cases heq : BitVec.ofNat 64 (i.1 + 8 * k) = a
  · exact ⟨w, hdom, by simp [updW, heq]⟩
  · exact ⟨u, hdom, by simp [updW, heq, hu]⟩

theorem htabBlocks_updW_nonlayout {F : Type} {s : PanSemStateFiniteExact 64 F} {t : Nat}
    (a w : BitVec 64) (hB : HtabBlocks s t)
    (hnot0 : BitVec.ofNat 64 (t + 8 * 0) ≠ a)
    (hnot1 : BitVec.ofNat 64 (t + 8 * 1) ≠ a)
    (hnot4 : BitVec.ofNat 64 (t + 8 * 4) ≠ a)
    (hnot5 : BitVec.ofNat 64 (t + 8 * 5) ≠ a)
    (hnot6 : BitVec.ofNat 64 (t + 8 * 6) ≠ a)
    (hnot10 : BitVec.ofNat 64 (t + 8 * 10) ≠ a)
    (hnx_ok : BitVec.ofNat 64 (t + 8 * 8) = a → 1 ≤ w.toNat ∧ w.toNat ≤ hdr s t 10 + 1) :
    let s' := { s with memory := updW s.memory a w }
    HtabBlocks s' t ∧ htabFootprint s' t = htabFootprint s t := by
  intro s'
  have hh0 : hdr s' t 0 = hdr s t 0 := memW_updW_other s a w _ hnot0
  have hh1 : hdr s' t 1 = hdr s t 1 := memW_updW_other s a w _ hnot1
  have hh4 : hdr s' t 4 = hdr s t 4 := memW_updW_other s a w _ hnot4
  have hh5 : hdr s' t 5 = hdr s t 5 := memW_updW_other s a w _ hnot5
  have hh6 : hdr s' t 6 = hdr s t 6 := memW_updW_other s a w _ hnot6
  have hh10 : hdr s' t 10 = hdr s t 10 := memW_updW_other s a w _ hnot10
  have hfp_eq : htabFootprint s' t = htabFootprint s t := by
    simp [htabFootprint, hh1, hh4, hh5, hh6, hh10]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hfp_eq⟩
  · intro iv hiv
    rw [hfp_eq] at hiv
    obtain ⟨hin, hwok⟩ := hB.1 iv hiv
    exact ⟨hin, wordsOK_updW s a w iv hwok⟩
  · rw [hfp_eq]; exact hB.2.1
  · rw [hh0]; exact hB.2.2.1
  · rw [hh0]; exact hB.2.2.2.1
  · rw [hh1, hh0]; exact hB.2.2.2.2.1
  · rw [hh10]; exact hB.2.2.2.2.2.1
  · by_cases h8 : BitVec.ofNat 64 (t + 8 * 8) = a
    · have : hdr s' t 8 = w.toNat := by simp [hdr, memW, s', updW, h8]
      rw [this]; exact (hnx_ok h8).1
    · rw [show hdr s' t 8 = hdr s t 8 from memW_updW_other s a w _ h8]; exact hB.2.2.2.2.2.2.1
  · by_cases h8 : BitVec.ofNat 64 (t + 8 * 8) = a
    · have : hdr s' t 8 = w.toNat := by simp [hdr, memW, s', updW, h8]
      rw [this, hh10]; exact (hnx_ok h8).2
    · rw [show hdr s' t 8 = hdr s t 8 from memW_updW_other s a w _ h8, hh10]; exact hB.2.2.2.2.2.2.2

/-! ## 3. `htab_new_node` Postcondition -/

def NewNodePost {F : Type} (s0 : PanSemStateFiniteExact 64 F) (t : Nat) (A : List Nat)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F) : Prop :=
  let fresh : Ivl := (globN s0 "heap_ptr", globN post "heap_ptr" - globN s0 "heap_ptr")
  ∃ nw : BitVec 64, ∃ Fr1 : List Nat,
    v = .val (.word nw) ∧
    ArenaReady post ∧
    NodeState post t (A ++ [nw.toNat]) Fr1 ∧
    hdr post t 0 = hdr s0 t 0 ∧
    hdr post t 1 = hdr s0 t 1 ∧
    hdr post t 3 = hdr s0 t 3 ∧
    hdr post t 7 = hdr s0 t 7 ∧
    hdr s0 t 10 ≤ hdr post t 10 ∧
    (∀ x ∈ A, ∀ off, (off = 0 ∨ off = 8 ∨ off = 16 ∨ off = 24) →
      nodeF post (hdr post t 5) x off = nodeF s0 (hdr s0 t 5) x off) ∧
    (∀ i, i < hdr s0 t 10 + 1 →
      memW post (hdr post t 6 + 8 * i) = memW s0 (hdr s0 t 6 + 8 * i)) ∧
    globN s0 "heap_ptr" ≤ globN post "heap_ptr" ∧
    (∀ i ∈ htabFootprint post t, Allocated post i ∧
      ((∃ j ∈ htabFootprint s0 t, Inside i j.1 (j.1 + j.2)) ∨ Inside i fresh.1 (fresh.1 + fresh.2))) ∧
    FrameOutside s0 post [(t, 88)] fresh ∧
    (∀ k : MlS, k ∉ (["heap_ptr"] : List String).map ofString →
      s0.globals.lookup k = post.globals.lookup k)

theorem locFree_newNodePost {F : Type} (s0 : PanSemStateFiniteExact 64 F) (t : Nat) (A : List Nat) :
    LocFreePost (NewNodePost s0 t A) := by
  intro v p L' h
  obtain ⟨nw, Fr1, hv, hA, hNS, c0, c1, c3, c7, c10, cnd, cord, chp, cfp, cfr, cg⟩ := h
  exact ⟨nw, Fr1, hv, ⟨guestInv_congr (s := { p with locals := L' }) rfl rfl rfl rfl hA.1, hA.2⟩,
    hNS, c0, c1, c3, c7, c10, cnd, cord, chp, cfp, cfr, cg⟩

theorem htab_new_node_body_spec {F : Type} (s0 : PanSemStateFiniteExact 64 F)
    (tw : BitVec 64) (A Fr0 : List Nat)
    (ht : s0.locals.lookup (ofString "t") = some (.val (.word tw)))
    (hA0 : ArenaReady s0)
    (hNS0 : NodeState s0 tw.toNat A Fr0)
    (hal0 : ∀ i ∈ htabFootprint s0 tw.toNat, Allocated s0 i) :
    Ret s0 (sourceFnBody Guest.Software.guestFn_htab_new_node) (NewNodePost s0 tw.toNat A) := by
  set t := tw.toNat
  have hLF := locFree_newNodePost s0 t A
  obtain ⟨hB0, hnodup0, hmem0, hfc0⟩ := hNS0
  obtain ⟨hncap_lt, hst_ge8, hst_le64, hst_al, ht_lo, ht_hi, ht_al⟩ := htabBlocks_bounds hB0
  have hnx_le0 : hdr s0 t 8 ≤ hdr s0 t 10 + 1 := hB0.2.2.2.2.2.2.2
  have hnx_ge1 : 1 ≤ hdr s0 t 8 := hB0.2.2.2.2.2.2.1
  have hhe : heapEnd = 33806089704 := rfl
  obtain ⟨hdom_t5, hm_t5⟩ := word_of_hdr s0 tw 5 (by omega) hB0
  obtain ⟨hdom_t8, hm_t8⟩ := word_of_hdr s0 tw 8 (by omega) hB0
  obtain ⟨hdom_t9, hm_t9⟩ := word_of_hdr s0 tw 9 (by omega) hB0
  obtain ⟨hdom_t10, hm_t10⟩ := word_of_hdr s0 tw 10 (by omega) hB0
  htab_unfold Guest.Software.guestFn_htab_new_node
  apply Ret.of_NS
  -- 1. dec f := load(t + 72)
  apply Ret.ns_dec_lf hLF; intro vf hvf
  obtain ⟨_, rfl⟩ := ev_field_load _ (ofString "t") tw 72#64 ht vf hvf
  have hm72 : s0.memory (tw + 72#64) = .word (BitVec.ofNat 64 (hdr s0 t 9)) := hm_t9
  simp only [NS_memory, hm72]
  set fw := BitVec.ofNat 64 (hdr s0 t 9)
  -- 2. seq (ite (f != 0) (...) skip) (...)
  apply Ret.seq_ite
  intro cw hcw
  have hcw_spec : (cw ≠ 0 → hdr s0 t 9 ≠ 0) ∧ (cw = 0 → hdr s0 t 9 = 0) := by
    obtain ⟨va, vb, hva, hvb, hcw_eq⟩ := evalAt_cmp _ .notEqual _ _ cw hcw
    simp [evalAt, evalHOLExact, HolFiniteMapExact.lookup_update, FUPDATE] at hva hvb
    subst hva hvb
    have hf_lt : hdr s0 t 9 < 2 ^ 64 := by
      cases Fr0 with
      | nil => simp [FreeChainF] at hfc0; omega
      | cons f0 Fr1 =>
        have hf0_eq : hdr s0 t 9 = f0 := hfc0.1
        have hf0_mem : f0 ∈ A ++ (f0 :: Fr1) := List.mem_append_right _ List.mem_cons_self
        have := (hmem0 f0).mp hf0_mem
        omega
    have hfw_nat : fw.toNat = hdr s0 t 9 := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hf_lt]
    have hz0 : (0#64 : BitVec 64).toNat = 0 := rfl
    constructor
    · intro hnz h0; apply hnz
      have hfw0 : fw = 0#64 := BitVec.eq_of_toNat_eq (by rw [hfw_nat, hz0]; exact h0)
      simp [Compiler.Encoders.Asm.wordCmpHOL, hfw0] at hcw_eq; exact hcw_eq
    · intro hz; by_contra hne
      have hfw_ne : fw ≠ 0#64 := fun h => hne (by have := congrArg BitVec.toNat h; rw [hfw_nat, hz0] at this; exact this)
      simp [Compiler.Encoders.Asm.wordCmpHOL, hfw_ne] at hcw_eq
      rw [hz] at hcw_eq; exact absurd hcw_eq (by decide)
  refine ⟨fun hcw_nz => ?_, fun hcw_z => ?_⟩
  · -- CASE A: Free list non-empty (`hdr s0 t 9 ≠ 0`)!
    have hfree_nz := hcw_spec.1 hcw_nz
    cases Fr0 with
    | nil => simp [FreeChainF] at hfc0; exact absurd hfc0 hfree_nz
    | cons f0 Fr1 =>
      obtain ⟨hf0_eq, hfc1⟩ := hfc0
      have hf0_mem : f0 ∈ A ++ (f0 :: Fr1) := List.mem_append_right _ List.mem_cons_self
      have hf0_rng := (hmem0 f0).mp hf0_mem
      have hfw_nat : fw.toNat = f0 := by rw [BitVec.toNat_ofNat, ← hf0_eq]; omega
      refine Ret.seq ?_ ?_
      · apply Ret.ns_dec_lf hLF; intro vnd hvnd
        obtain ⟨_, rfl⟩ := ev_field_load _ (ofString "t") tw 40#64
          (by simp [HolFiniteMapExact.lookup_update, FUPDATE, ht, show ofString "f" ≠ ofString "t" by decide]) vnd hvnd
        have hm40 : s0.memory (tw + 40#64) = .word (BitVec.ofNat 64 (hdr s0 t 5)) := hm_t5
        simp only [NS_memory, hm40]
        set ndw := BitVec.ofNat 64 (hdr s0 t 5)
        have hndw_nat : ndw.toNat = hdr s0 t 5 := by
          have hnd_in := (hB0.1 (hdr s0 t 5, (hdr s0 t 10 + 1) * 32) (by simp [htabFootprint])).1
          unfold Inside at hnd_in; rw [BitVec.toNat_ofNat]; omega
        apply Ret.ns_dec_lf hLF; intro vnf hvnf
        obtain ⟨_, rfl⟩ := ev_var_node_load _ (ofString "f") ndw fw 0#64
          (by simp [HolFiniteMapExact.lookup_update, FUPDATE])
          (by simp [HolFiniteMapExact.lookup_update, FUPDATE, show ofString "nodes" ≠ ofString "f" by decide]) vnf hvnf
        have hf0_lt_nc0 : fw.toNat < hdr s0 tw.toNat 10 + 1 := by
          change fw.toNat < hdr s0 t 10 + 1
          omega
        obtain ⟨_, hm_nf⟩ := word_of_node s0 tw ndw fw 0 hndw_nat.symm hf0_lt_nc0 (Or.inl rfl) hB0
        have hm_nf' : s0.memory (ndw + fw * 32 + 0#64) = .word (BitVec.ofNat 64 (nodeF s0 (hdr s0 t 5) f0 0)) := by
          rw [← hndw_nat, ← hfw_nat]; exact hm_nf
        set nfw := BitVec.ofNat 64 (nodeF s0 (hdr s0 t 5) f0 0)
        have hnfw_nat : nfw.toNat = nodeF s0 (hdr s0 t 5) f0 0 := by
          cases Fr1 with
          | nil =>
            simp only [FreeChainF] at hfc1
            dsimp only [nfw]
            rw [hfc1]; rfl
          | cons f1 Fr2 =>
            have hf1_eq : nodeF s0 (hdr s0 t 5) f0 0 = f1 := hfc1.1
            have hf1_mem : f1 ∈ A ++ (f0 :: f1 :: Fr2) := List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)
            have := (hmem0 f1).mp hf1_mem
            dsimp only [nfw]
            rw [BitVec.toNat_ofNat, hf1_eq]; omega
        refine Ret.ns_storeW (tw + 72#64) nfw
          (by simp [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact,
                HolFiniteMapExact.lookup_update, FUPDATE, ht,
                show ofString "nf" ≠ ofString "t" by decide, show ofString "nodes" ≠ ofString "t" by decide,
                show ofString "f" ≠ ofString "t" by decide, valueIsWord, valueWord, wordOpHOL, wordOp])
          (by
            simp only [NS_memory, hm_nf']
            simp [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, HolFiniteMapExact.lookup_update, FUPDATE]) ?_
        intro _
        apply Ret.ns_ret; intro val hval
        have hval_eq : val = .val (.word fw) := by
          simp [evalAt, evalHOLExact, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "nf" ≠ ofString "f" by decide, show ofString "nodes" ≠ ofString "f" by decide] at hval
          exact hval.symm
        subst hval_eq
        let s_a := NS s0 HolFiniteMapExact.empty s0.globals (updW s0.memory (tw + 72#64) nfw) s0.clock
        have htw72_eq : BitVec.ofNat 64 (t + 8 * 9) = tw + 72#64 := ofNat_add_toNat tw 72
        have hne_hdr : ∀ k < 11, k ≠ 9 → BitVec.ofNat 64 (t + 8 * k) ≠ tw + 72#64 := by
          intro k hk hne; rw [← htw72_eq]; exact ofNat64_ne_of_ne_of_lt (by omega) (by omega) (by omega)
        obtain ⟨hB_a', hfp_a'⟩ := htabBlocks_updW_nonlayout (tw + 72#64) nfw hB0
          (hne_hdr 0 (by omega) (by omega)) (hne_hdr 1 (by omega) (by omega))
          (hne_hdr 4 (by omega) (by omega)) (hne_hdr 5 (by omega) (by omega))
          (hne_hdr 6 (by omega) (by omega)) (hne_hdr 10 (by omega) (by omega))
          (fun h8 => absurd h8 (hne_hdr 8 (by omega) (by omega)))
        have hsep := htabBlocks_cell_sep hB0
        have hh5_a : hdr s_a t 5 = hdr s0 t 5 := memW_updW_other s0 _ _ _ (hne_hdr 5 (by omega) (by omega))
        have hh6_a : hdr s_a t 6 = hdr s0 t 6 := memW_updW_other s0 _ _ _ (hne_hdr 6 (by omega) (by omega))
        have hh8_a : hdr s_a t 8 = hdr s0 t 8 := memW_updW_other s0 _ _ _ (hne_hdr 8 (by omega) (by omega))
        have hh9_a : hdr s_a t 9 = nfw.toNat := by simp [hdr, memW, s_a, updW, htw72_eq]
        have hnd_same : ∀ n < hdr s0 t 10 + 1, ∀ off, (off = 0 ∨ off = 8 ∨ off = 16 ∨ off = 24) →
            nodeF s_a (hdr s0 t 5) n off = nodeF s0 (hdr s0 t 5) n off := by
          intro n hn off hoff; unfold nodeF; apply memW_updW_other s0; rw [← htw72_eq]
          exact (hsep.1 9 (by omega) n hn off hoff).symm
        have hord_same : ∀ i < hdr s0 t 10 + 1,
            memW s_a (hdr s0 t 6 + 8 * i) = memW s0 (hdr s0 t 6 + 8 * i) := by
          intro i hi; apply memW_updW_other s0; rw [← htw72_eq]
          exact (hsep.2.1 9 (by omega) i hi).symm
        have hperm : List.Perm ((A ++ [f0]) ++ Fr1) (A ++ (f0 :: Fr1)) := by simp [List.append_assoc]
        have hnodup_a : ((A ++ [fw.toNat]) ++ Fr1).Nodup := by
          rw [hfw_nat]; exact hperm.nodup_iff.mpr hnodup0
        have hmem_a : ∀ x, x ∈ (A ++ [fw.toNat]) ++ Fr1 ↔ 1 ≤ x ∧ x < hdr s_a t 8 := by
          intro x; rw [hfw_nat, hh8_a, hperm.mem_iff]; exact hmem0 x
        have hfc_a : FreeChainF (nodeF s_a (hdr s_a t 5)) (hdr s_a t 9) Fr1 := by
          rw [hh5_a, hh9_a, hnfw_nat]
          refine FreeChainF.congr Fr1 _ ?_ hfc1
          intro x hx
          have hx_rng := (hmem0 x).mp (List.mem_append_right _ (List.mem_cons_of_mem _ hx))
          exact hnd_same x (by omega) 0 (Or.inl rfl)
        have hfr_a : FrameOutside s0 s_a [(t, 88)] (globN s0 "heap_ptr", 0) := by
          have htw72_nat : (tw + 72#64).toNat = t + 72 := by rw [BitVec.toNat_add, show (72#64).toNat = 72 from rfl]; omega
          exact frameOutside_updW s0 (tw + 72#64) nfw [(t, 88)] _
            (Or.inl ⟨(t, 88), List.mem_singleton.2 rfl, ⟨by omega, by omega⟩⟩)
        refine ⟨fw, Fr1, rfl, ⟨guestInv_congr (s := s0) rfl rfl rfl rfl hA0.1, hA0.2⟩,
          ⟨hB_a', hnodup_a, hmem_a, hfc_a⟩,
          memW_updW_other s0 _ _ _ (hne_hdr 0 (by omega) (by omega)),
          memW_updW_other s0 _ _ _ (hne_hdr 1 (by omega) (by omega)),
          memW_updW_other s0 _ _ _ (hne_hdr 3 (by omega) (by omega)),
          memW_updW_other s0 _ _ _ (hne_hdr 7 (by omega) (by omega)),
          (by change hdr s0 t 10 ≤ hdr { s0 with memory := updW s0.memory (tw + 72#64) nfw } t 10
              rw [show hdr { s0 with memory := updW s0.memory (tw + 72#64) nfw } t 10 = hdr s0 t 10 from memW_updW_other s0 _ _ _ (hne_hdr 10 (by omega) (by omega))]),
          ?_, ?_, le_rfl, ?_, ?_, fun _ _ => rfl⟩
        · intro x hxA off hoff; rw [hh5_a]
          have hx_rng := (hmem0 x).mp (List.mem_append_left _ hxA)
          exact hnd_same x (by omega) off hoff
        · intro i hi; rw [hh6_a]; exact hord_same i hi
        · change ∀ iv ∈ htabFootprint { s0 with memory := updW s0.memory (tw + 72#64) nfw } t, Allocated s0 iv ∧ _
          rw [hfp_a']; intro iv hiv; exact ⟨hal0 iv hiv, Or.inl ⟨iv, hiv, le_rfl, le_rfl⟩⟩
        · change FrameOutside s0 s_a [(t, 88)] (globN s0 "heap_ptr", globN s0 "heap_ptr" - globN s0 "heap_ptr")
          rw [Nat.sub_self]; exact hfr_a
      · exact fun u hu => False.elim (noFlow_dec (fun _ => noFlow_dec (fun _ => noFlow_seq_right (fun _ => noFlow_ret))) (congrArg Prod.fst hu))
  · -- CASE B: Free list is empty (`hdr s0 t 9 = 0`)!
    have hfree_z := hcw_spec.2 hcw_z
    have hFr0_nil : Fr0 = [] := by
      cases Fr0 with
      | nil => rfl
      | cons f0 Fr1 =>
        have hf0_eq : hdr s0 t 9 = f0 := hfc0.1
        have hf0_rng := (hmem0 f0).mp (List.mem_append_right _ List.mem_cons_self)
        omega
    subst hFr0_nil
    apply Ret.seq_skip
    -- 3. dec next := load(t + 64)
    apply Ret.ns_dec_lf hLF; intro vnx hvnx
    obtain ⟨_, rfl⟩ := ev_field_load _ (ofString "t") tw 64#64
      (by simp [HolFiniteMapExact.lookup_update, FUPDATE, ht, show ofString "f" ≠ ofString "t" by decide]) vnx hvnx
    have hm64 : s0.memory (tw + 64#64) = .word (BitVec.ofNat 64 (hdr s0 t 8)) := hm_t8
    simp only [NS_memory, hm64]
    set nxw := BitVec.ofNat 64 (hdr s0 t 8)
    have hnxw_nat : nxw.toNat = hdr s0 t 8 := by rw [BitVec.toNat_ofNat]; omega
    -- 4. seq (ite (load(t + 80) < next) (call htab_grow(t)) skip) (...)
    apply Ret.seq_ite
    intro cw2 hcw2
    have hcw2_spec : (cw2 ≠ 0 → hdr s0 t 10 < hdr s0 t 8) ∧ (cw2 = 0 → hdr s0 t 8 ≤ hdr s0 t 10) := by
      obtain ⟨va, vb, hva, hvb, hcw2_eq⟩ := evalAt_cmp _ .lower _ _ cw2 hcw2
      obtain ⟨_, hva_mem⟩ := ev_field_load _ (ofString "t") tw 80#64
        (by simp [HolFiniteMapExact.lookup_update, FUPDATE, ht,
          show ofString "next" ≠ ofString "t" by decide, show ofString "f" ≠ ofString "t" by decide]) (.val (.word va)) hva
      have hm80 : s0.memory (tw + 80#64) = .word (BitVec.ofNat 64 (hdr s0 t 10)) := hm_t10
      simp only [NS_memory, hm80, ValueHOL.val.injEq, HolWordLab.word.injEq] at hva_mem
      subst hva_mem
      simp [evalAt, evalHOLExact, HolFiniteMapExact.lookup_update, FUPDATE] at hvb
      subst hvb
      have hnc_nat : (BitVec.ofNat 64 (hdr s0 t 10)).toNat = hdr s0 t 10 := by rw [BitVec.toNat_ofNat]; omega
      constructor
      · intro hnz; by_contra hge
        have hnlt : ¬ (BitVec.ofNat 64 (hdr s0 t 10) < nxw) := by rw [BitVec.lt_def, hnc_nat, hnxw_nat]; omega
        simp [Compiler.Encoders.Asm.wordCmpHOL, hnlt] at hcw2_eq; exact hnz hcw2_eq
      · intro hz; by_contra hlt
        have hlt_bv : BitVec.ofNat 64 (hdr s0 t 10) < nxw := by rw [BitVec.lt_def, hnc_nat, hnxw_nat]; omega
        simp [Compiler.Encoders.Asm.wordCmpHOL, hlt_bv] at hcw2_eq; rw [hz] at hcw2_eq; exact absurd hcw2_eq (by decide)
    have finish_bump : ∀ (sm : PanSemStateFiniteExact 64 F),
        sm.locals.lookup (ofString "t") = some (.val (.word tw)) →
        ArenaReady sm → HtabBlocks sm t →
        hdr sm t 0 = hdr s0 t 0 → hdr sm t 1 = hdr s0 t 1 → hdr sm t 3 = hdr s0 t 3 →
        hdr sm t 7 = hdr s0 t 7 → hdr sm t 8 = hdr s0 t 8 → hdr sm t 9 = 0 →
        hdr s0 t 10 ≤ hdr sm t 10 → hdr sm t 8 ≤ hdr sm t 10 →
        (∀ x ∈ A, ∀ off, (off = 0 ∨ off = 8 ∨ off = 16 ∨ off = 24) →
          nodeF sm (hdr sm t 5) x off = nodeF s0 (hdr s0 t 5) x off) →
        (∀ i, i < hdr s0 t 10 + 1 →
          memW sm (hdr sm t 6 + 8 * i) = memW s0 (hdr s0 t 6 + 8 * i)) →
        globN s0 "heap_ptr" ≤ globN sm "heap_ptr" →
        (∀ i ∈ htabFootprint sm t, Allocated sm i ∧
          ((∃ j ∈ htabFootprint s0 t, Inside i j.1 (j.1 + j.2)) ∨
            Inside i (globN s0 "heap_ptr") (globN s0 "heap_ptr" + (globN sm "heap_ptr" - globN s0 "heap_ptr")))) →
        FrameOutside s0 sm [(t, 88)] (globN s0 "heap_ptr", globN sm "heap_ptr" - globN s0 "heap_ptr") →
        (∀ k : MlS, k ∉ (["heap_ptr"] : List String).map ofString →
          s0.globals.lookup k = sm.globals.lookup k) →
        Ret sm
          (.dec (ofString "n") .one (.load .one (.op .add [.var .local (ofString "t"), .const 64#64]))
            (.seq
              (.store (.op .add [.var .local (ofString "t"), .const 64#64])
                (.op .add [.var .local (ofString "n"), .const 1#64]))
              (.return (.var .local (ofString "n")))))
          (NewNodePost s0 t A) := by
      intro sm ht_sm hAm hBm hh0m hh1m hh3m hh7m hh8m hh9m hnc_le hnx_lt_nc hnd_m hord_m hhp_m hfp_m hfr_m hg_m
      obtain ⟨hncap_m_lt, _, _, _, _, _, _⟩ := htabBlocks_bounds hBm
      obtain ⟨_, hm64_sm⟩ := word_of_hdr sm tw 8 (by omega) hBm
      have hm64_sm' : sm.memory (tw + 64#64) = .word nxw := by rw [hh8m] at hm64_sm; exact hm64_sm
      apply Ret.of_NS
      apply Ret.ns_dec_lf hLF; intro vn hvn
      obtain ⟨_, rfl⟩ := ev_field_load _ (ofString "t") tw 64#64 ht_sm vn hvn
      simp only [NS_memory, hm64_sm']
      have hnx1_eq : nxw + (1#64 + (0 : BitVec 64)) = BitVec.ofNat 64 (hdr s0 t 8 + 1) := by
        apply BitVec.eq_of_toNat_eq
        have h10 : 1#64 + (0 : BitVec 64) = 1#64 := rfl
        have hlt_nx1 : hdr s0 t 8 + 1 < 2 ^ 64 := by omega
        rw [h10, BitVec.toNat_add, hnxw_nat, show (1#64 : BitVec 64).toNat = 1 from rfl, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt hlt_nx1]
      refine Ret.ns_storeW (tw + 64#64) (BitVec.ofNat 64 (hdr s0 t 8 + 1))
        (by simp [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact,
              HolFiniteMapExact.lookup_update, FUPDATE, ht_sm,
              show ofString "n" ≠ ofString "t" by decide, valueIsWord, valueWord, wordOpHOL, wordOp])
        (by
          have hn_lk : (sm.locals.update (ofString "n", .val (.word nxw))).lookup (ofString "n") = some (.val (.word nxw)) := by
            simp [HolFiniteMapExact.lookup_update, FUPDATE]
          simp only [NS_locals, evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact,
            hn_lk, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
            valueIsWord, valueWord, wordOpHOL, wordOp, hnx1_eq]) ?_
      intro _
      apply Ret.ns_ret; intro val hval
      have hval_eq : val = .val (.word nxw) := by
        simp [evalAt, evalHOLExact, HolFiniteMapExact.lookup_update, FUPDATE] at hval; exact hval.symm
      subst hval_eq
      let s_b := NS sm HolFiniteMapExact.empty sm.globals (updW sm.memory (tw + 64#64) (BitVec.ofNat 64 (hdr s0 t 8 + 1))) sm.clock
      have htw64_eq : BitVec.ofNat 64 (t + 8 * 8) = tw + 64#64 := ofNat_add_toNat tw 64
      have hne_hdr : ∀ k < 11, k ≠ 8 → BitVec.ofNat 64 (t + 8 * k) ≠ tw + 64#64 := by
        intro k hk hne; rw [← htw64_eq]; exact ofNat64_ne_of_ne_of_lt (by omega) (by omega) (by omega)
      have hw_nx1_nat : (BitVec.ofNat 64 (hdr s0 t 8 + 1)).toNat = hdr s0 t 8 + 1 := by rw [BitVec.toNat_ofNat]; omega
      obtain ⟨hB_b', hfp_b'⟩ := htabBlocks_updW_nonlayout (tw + 64#64) (BitVec.ofNat 64 (hdr s0 t 8 + 1)) hBm
        (hne_hdr 0 (by omega) (by omega)) (hne_hdr 1 (by omega) (by omega))
        (hne_hdr 4 (by omega) (by omega)) (hne_hdr 5 (by omega) (by omega))
        (hne_hdr 6 (by omega) (by omega)) (hne_hdr 10 (by omega) (by omega))
        (fun _ => by rw [hw_nx1_nat]; omega)
      have hsep_m := htabBlocks_cell_sep hBm
      have hh5_b : hdr s_b t 5 = hdr sm t 5 := memW_updW_other sm _ _ _ (hne_hdr 5 (by omega) (by omega))
      have hh6_b : hdr s_b t 6 = hdr sm t 6 := memW_updW_other sm _ _ _ (hne_hdr 6 (by omega) (by omega))
      have hh8_b : hdr s_b t 8 = hdr s0 t 8 + 1 := by
        change memW { sm with memory := updW sm.memory (tw + 64#64) (BitVec.ofNat 64 (hdr s0 t 8 + 1)) } (t + 8 * 8) = hdr s0 t 8 + 1
        unfold memW
        rw [htw64_eq]
        simp only [updW, ↓reduceIte, hw_nx1_nat]
      have hh9_b : hdr s_b t 9 = 0 := (memW_updW_other sm _ _ _ (hne_hdr 9 (by omega) (by omega))).trans hh9m
      have hnx_not_A : hdr s0 t 8 ∉ A := by
        intro hmemA; have := (hmem0 (hdr s0 t 8)).mp (by simpa using hmemA); omega
      have hnodup_b : ((A ++ [nxw.toNat]) ++ ([] : List Nat)).Nodup := by
        rw [List.append_nil, hnxw_nat, List.nodup_append]
        have hndA : A.Nodup := by simpa using hnodup0
        exact ⟨hndA, List.nodup_singleton _, fun x hx y hy hxy => by simp at hy; subst hy; subst hxy; exact hnx_not_A hx⟩
      have hmem_b : ∀ x, x ∈ (A ++ [nxw.toNat]) ++ ([] : List Nat) ↔ 1 ≤ x ∧ x < hdr s_b t 8 := by
        intro x
        rw [List.append_nil, hnxw_nat, hh8_b, List.mem_append, List.mem_singleton]
        have hx0 := hmem0 x; rw [List.append_nil] at hx0
        constructor
        · rintro (hxA | rfl)
          · have := hx0.mp hxA; omega
          · omega
        · intro ⟨h1, h2⟩
          by_cases heq : x = hdr s0 t 8
          · exact Or.inr heq
          · exact Or.inl (hx0.mpr ⟨h1, by omega⟩)
      have hfc_b : FreeChainF (nodeF s_b (hdr s_b t 5)) (hdr s_b t 9) [] := hh9_b
      have hfr_b : FrameOutside s0 s_b [(t, 88)] (globN s0 "heap_ptr", globN sm "heap_ptr" - globN s0 "heap_ptr") := by
        have htw64_nat : (tw + 64#64).toNat = t + 64 := by rw [BitVec.toNat_add, show (64#64).toNat = 64 from rfl]; omega
        exact frameOutside_trans_same hfr_m
          (frameOutside_updW sm (tw + 64#64) _ [(t, 88)] _
            (Or.inl ⟨(t, 88), List.mem_singleton.2 rfl, ⟨by omega, by omega⟩⟩))
      refine ⟨nxw, [], rfl, ⟨guestInv_congr (s := sm) rfl rfl rfl rfl hAm.1, hAm.2⟩,
        ⟨hB_b', hnodup_b, hmem_b, hfc_b⟩,
        (memW_updW_other sm _ _ _ (hne_hdr 0 (by omega) (by omega))).trans hh0m,
        (memW_updW_other sm _ _ _ (hne_hdr 1 (by omega) (by omega))).trans hh1m,
        (memW_updW_other sm _ _ _ (hne_hdr 3 (by omega) (by omega))).trans hh3m,
        (memW_updW_other sm _ _ _ (hne_hdr 7 (by omega) (by omega))).trans hh7m,
        (by change hdr s0 t 10 ≤ hdr { sm with memory := updW sm.memory (tw + 64#64) (BitVec.ofNat 64 (hdr s0 t 8 + 1)) } t 10
            rw [show hdr { sm with memory := updW sm.memory (tw + 64#64) (BitVec.ofNat 64 (hdr s0 t 8 + 1)) } t 10 = hdr sm t 10 from memW_updW_other sm _ _ _ (hne_hdr 10 (by omega) (by omega))]; exact hnc_le),
        ?_, ?_, hhp_m, ?_, hfr_b, hg_m⟩
      · intro x hxA off hoff; rw [hh5_b]
        have hx_rng := (hmem0 x).mp (by simpa using hxA)
        have h1 : nodeF s_b (hdr sm t 5) x off = nodeF sm (hdr sm t 5) x off := by
          unfold nodeF; apply memW_updW_other sm; rw [← htw64_eq]
          exact (hsep_m.1 8 (by omega) x (by omega) off hoff).symm
        exact h1.trans (hnd_m x hxA off hoff)
      · intro i hi; rw [hh6_b]
        have h1 : memW s_b (hdr sm t 6 + 8 * i) = memW sm (hdr sm t 6 + 8 * i) := by
          apply memW_updW_other sm; rw [← htw64_eq]
          exact (hsep_m.2.1 8 (by omega) i (by omega)).symm
        exact h1.trans (hord_m i hi)
      · change ∀ iv ∈ htabFootprint { sm with memory := updW sm.memory (tw + 64#64) (BitVec.ofNat 64 (hdr s0 t 8 + 1)) } t, Allocated sm iv ∧ _
        rw [hfp_b']; exact hfp_m
    refine ⟨fun hcw2_nz => ?_, fun hcw2_z => ?_⟩
    · have hlt_nc := hcw2_spec.1 hcw2_nz
      have hnx_eq : hdr s0 t 8 = hdr s0 t 10 + 1 := by omega
      let s_pre := NS s0 ((s0.locals.update (ofString "f", .val (.word fw))).update (ofString "next", .val (.word nxw))) s0.globals s0.memory s0.clock
      have ht_pre : s_pre.locals.lookup (ofString "t") = some (.val (.word tw)) := by
        simp [s_pre, HolFiniteMapExact.lookup_update, FUPDATE, ht,
          show ofString "next" ≠ ofString "t" by decide, show ofString "f" ≠ ofString "t" by decide]
      refine Ret.seq_call1 (s := s_pre) hA0.1.code lookup_htab_grow tw
        (by simp [evalAt, evalHOLExact, ht_pre]) ?_
      intro wg gpost hgrow_run
      let gentry := callEntryStateHOLFinite s_pre (HolFiniteMapExact.empty.update (ofString "t", .val (.word tw)))
      have hg_spec := htab_grow_body_spec gentry tw
        (by simp [gentry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
        ⟨guestInv_congr (s := s0) rfl rfl rfl rfl hA0.1, hA0.2⟩ hB0 hal0
        (.val (.word wg)) (by rw [hgrow_run])
      rw [hgrow_run] at hg_spec
      obtain ⟨_, hAg, hBg, hh0g, hh1g, hh3g, hh7g, hh8g, hh9g, hh10g, hnd_g, hord_g, hhp_g, hfp_g, hfr_g, hg_g⟩ := hg_spec
      let sm := { gpost with locals := s_pre.locals }
      have hnc2 : 2 ≤ hdr s0 t 10 := hB0.2.2.2.2.2.1
      have hh10g' : hdr gpost t 10 = 2 * hdr s0 t 10 := hh10g
      have hh8g' : hdr gpost t 8 = hdr s0 t 8 := hh8g
      exact finish_bump sm ht_pre
        ⟨guestInv_congr (s := gpost) rfl rfl rfl rfl hAg.1, hAg.2⟩ hBg
        hh0g hh1g hh3g hh7g hh8g (hh9g.trans hfree_z)
        (by change hdr s0 t 10 ≤ hdr gpost t 10; rw [hh10g']; omega)
        (by change hdr gpost t 8 ≤ hdr gpost t 10; rw [hh8g', hh10g']; omega)
        (fun x hxA off hoff => by
          have hx_rng := (hmem0 x).mp (by simpa using hxA)
          have hlt_x : x < hdr s0 t 10 + 1 := by omega
          exact hnd_g x hlt_x off hoff)
        hord_g hhp_g hfp_g hfr_g hg_g
    · have hle_nc := hcw2_spec.2 hcw2_z
      apply Ret.seq_skip
      let s_pre := NS s0 ((s0.locals.update (ofString "f", .val (.word fw))).update (ofString "next", .val (.word nxw))) s0.globals s0.memory s0.clock
      have ht_pre : s_pre.locals.lookup (ofString "t") = some (.val (.word tw)) := by
        simp [s_pre, HolFiniteMapExact.lookup_update, FUPDATE, ht,
          show ofString "next" ≠ ofString "t" by decide, show ofString "f" ≠ ofString "t" by decide]
      exact finish_bump s_pre ht_pre
        ⟨guestInv_congr (s := s0) rfl rfl rfl rfl hA0.1, hA0.2⟩ hB0
        rfl rfl rfl rfl rfl hfree_z le_rfl hle_nc
        (fun _ _ _ _ => rfl) (fun _ _ => rfl) le_rfl
        (fun iv hiv => ⟨hal0 iv hiv, Or.inl ⟨iv, hiv, le_rfl, le_rfl⟩⟩)
        (fun _ _ _ => rfl) (fun _ _ => rfl)

/-- `Ret.decCall_new_node_lf`: call `htab_new_node(t)` under `LocFreePost Φ`! -/
theorem Ret.decCall_new_node_lf {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {x : MlS} {et : ExpHOL 64} {cont : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hLF : LocFreePost Φ)
    (tw : BitVec 64) (A Fr0 : List Nat)
    (het : evalAt s0 et = some (.val (.word tw)))
    (hA0 : ArenaReady s0)
    (hNS0 : NodeState s0 tw.toNat A Fr0)
    (hal0 : ∀ i ∈ htabFootprint s0 tw.toNat, Allocated s0 i)
    (hk : ∀ (nw : BitVec 64) (Fr1 : List Nat) (s1 : PanSemStateFiniteExact 64 F),
      ArenaReady s1 →
      NodeState s1 tw.toNat (A ++ [nw.toNat]) Fr1 →
      hdr s1 tw.toNat 0 = hdr s0 tw.toNat 0 →
      hdr s1 tw.toNat 1 = hdr s0 tw.toNat 1 →
      hdr s1 tw.toNat 3 = hdr s0 tw.toNat 3 →
      hdr s1 tw.toNat 7 = hdr s0 tw.toNat 7 →
      hdr s0 tw.toNat 10 ≤ hdr s1 tw.toNat 10 →
      (∀ z ∈ A, ∀ off, (off = 0 ∨ off = 8 ∨ off = 16 ∨ off = 24) →
        nodeF s1 (hdr s1 tw.toNat 5) z off = nodeF s0 (hdr s0 tw.toNat 5) z off) →
      (∀ i, i < hdr s0 tw.toNat 10 + 1 →
        memW s1 (hdr s1 tw.toNat 6 + 8 * i) = memW s0 (hdr s0 tw.toNat 6 + 8 * i)) →
      globN s0 "heap_ptr" ≤ globN s1 "heap_ptr" →
      (∀ i ∈ htabFootprint s1 tw.toNat, Allocated s1 i ∧
        ((∃ j ∈ htabFootprint s0 tw.toNat, Inside i j.1 (j.1 + j.2)) ∨
          Inside i (globN s0 "heap_ptr") (globN s0 "heap_ptr" + (globN s1 "heap_ptr" - globN s0 "heap_ptr")))) →
      FrameOutside s0 s1 [(tw.toNat, 88)] (globN s0 "heap_ptr", globN s1 "heap_ptr" - globN s0 "heap_ptr") →
      (∀ k : MlS, k ∉ (["heap_ptr"] : List String).map ofString →
        s0.globals.lookup k = s1.globals.lookup k) →
      s1.locals = s0.locals →
      Ret (setVarHOLFinite x (.val (.word nw)) s1) cont Φ) :
    Ret s0 (.decCall x .one (ofString "htab_new_node") [et] cont) Φ := by
  refine Ret.decCall1_lf hLF hA0.1.code lookup_htab_new_node tw het ?_
  intro nw post hrun
  let entry := callEntryStateHOLFinite s0 (HolFiniteMapExact.empty.update (ofString "t", .val (.word tw)))
  have hspec := htab_new_node_body_spec entry tw A Fr0
    (by simp [entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
    ⟨guestInv_congr (s := s0) rfl rfl rfl rfl hA0.1, hA0.2⟩ hNS0 hal0
    (.val (.word nw)) (by rw [hrun])
  rw [hrun] at hspec
  obtain ⟨nw', Fr1, hnw_eq, hAp, hNSp, hh0, hh1, hh3, hh7, hnc_le, hnd, hord, hhp, hfp, hfr, hg⟩ := hspec
  injection hnw_eq with h1; injection h1 with h2; subst h2
  let s1 := { post with locals := s0.locals }
  exact hk nw Fr1 s1
    ⟨guestInv_congr (s := post) rfl rfl rfl rfl hAp.1, hAp.2⟩
    hNSp hh0 hh1 hh3 hh7 hnc_le hnd hord hhp hfp hfr hg rfl

end InitECandidate.Solver.Wave8GuestInv.SoloHtabSet
