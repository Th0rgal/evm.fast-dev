import InitECandidate.Solver.Wave8GuestInv.R10Shards.SoloHtabSet

/-! Flow/while-invariant rules (`Flw`, `while_inv2`, `while_noRet`), frame-only `memcpy`
(`memcpy_body_frame`, no `Disj` required), `htab_find_leaf` postcondition, and the `htab_set`
descent loop invariant. -/

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

/-! ## 1. `htab_unfold` macro and `FlowR` / `Flw` / `while_inv2` / `while_noRet` -/

macro "htab_unfold" d:ident : tactic => `(tactic| dsimp only [sourceFnBody, sourceFunctionEntry, extractFn, $d:ident,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural, List.map, Option.map])

def FlowR (r : Option (PanSemResultExact 64)) : Prop :=
  r = none ∨ r = some .continue ∨ r = some .break

theorem flowing_of_flowR {r : Option (PanSemResultExact 64)} (h : FlowR r) : Flowing r := by
  rcases h with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl h)

def Flw {F : Type} (s : PanSemStateFiniteExact 64 F) (p : ProgHOL 64)
    (Ψ : Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → Prop) : Prop :=
  FlowR (evaluateHOLFiniteState s p).1 → Ψ (evaluateHOLFiniteState s p).1 (evaluateHOLFiniteState s p).2

section FlwRules
variable {F : Type} {s : PanSemStateFiniteExact 64 F}
  {Ψ : Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → Prop}

theorem Flw.dec {x : MlS} {sh : ShapeHOL} {init : ExpHOL 64} {body : ProgHOL 64}
    (h : ∀ v, evalAt s init = some v →
      Flw (setVarHOLFinite x v s) body
        (fun r t => Ψ r { t with locals := HolFiniteMapExact.resVarEq t.locals (x, s.locals.lookup x) })) :
    Flw s (.dec x sh init body) Ψ := by
  rw [Flw, evaluateHOLFiniteState_dec_total]
  dsimp only
  cases hv : @evalHOLExact 64 F _ s.toExact (fun addr => Classical.propDecidable (s.memaddrs addr)) init with
  | none => intro hf; rcases hf with h' | h' | h' <;> cases h'
  | some v =>
    dsimp only
    by_cases hsh : shapeEqHOL sh (shapeOfHOLExact v) = true
    · rw [if_pos hsh]; exact h v hv
    · rw [if_neg hsh]; intro hf; rcases hf with h' | h' | h' <;> cases h'

theorem Flw.seq {a b : ProgHOL 64}
    (h : Flw s a (fun r t => (r = none → Flw t b Ψ) ∧ (r ≠ none → Ψ r t))) :
    Flw s (.seq a b) Ψ := by
  rw [Flw, evaluateHOLFiniteState_seq_line780]
  cases hr : evaluateHOLFiniteState s a with
  | mk r t =>
    have h' := h
    unfold Flw at h'
    rw [hr] at h'
    dsimp only at h' ⊢
    cases r with
    | none => exact (h' (Or.inl rfl)).1 rfl
    | some _ => intro hf; exact (h' hf).2 (by simp)

theorem Flw.ite {c : ExpHOL 64} {y n : ProgHOL 64}
    (h : ∀ w, evalAt s c = some (.val (.word w)) → (w ≠ 0 → Flw s y Ψ) ∧ (w = 0 → Flw s n Ψ)) :
    Flw s (.ite c y n) Ψ := by
  rw [Flw, evaluateHOLFiniteState_ite]
  cases hcw : @evalHOLExact 64 F _ s.toExact (fun addr => Classical.propDecidable (s.memaddrs addr)) c with
  | none => intro hf; rcases hf with h' | h' | h' <;> cases h'
  | some vc =>
    cases vc with
    | val wl =>
      cases wl with
      | word w =>
        dsimp only
        by_cases hz : w = 0
        · rw [if_pos hz]; exact (h w hcw).2 hz
        · rw [if_neg hz]; exact (h w hcw).1 hz
    | rStruct _ => intro hf; rcases hf with h' | h' | h' <;> cases h'
    | nStruct _ _ => intro hf; rcases hf with h' | h' | h' <;> cases h'

theorem Flw.brk (h : Ψ (some .break) s) : Flw s .break Ψ := by
  intro _; rw [evaluateHOLFiniteState_break]; exact h

theorem Flw.skip (h : Ψ none s) : Flw s .skip Ψ := by
  intro _; rw [evaluateHOLFiniteState_skip]; exact h

theorem Flw.assign {x : MlS} {e : ExpHOL 64}
    (h : ∀ v, evalAt s e = some v → Ψ none (setVarHOLFinite x v s)) :
    Flw s (.assign .local x e) Ψ := by
  rw [Flw, evaluateHOLFiniteState_assign]
  cases hv : @evalHOLExact 64 F _ s.toExact (fun addr => Classical.propDecidable (s.memaddrs addr)) e with
  | none => intro hf; rcases hf with h' | h' | h' <;> cases h'
  | some v =>
    dsimp only
    by_cases hvld : s.isValidValueHOLFinite .local x v = true
    · rw [if_pos hvld]; intro _; exact h v hv
    · rw [if_neg hvld]; intro hf; rcases hf with h' | h' | h' <;> cases h'

end FlwRules

def NoRet (p : ProgHOL 64) : Prop :=
  ∀ {F : Type} (st : PanSemStateFiniteExact 64 F) v,
    (evaluateHOLFiniteState st p).1 ≠ some (.returned v)

theorem NoRet.seq {a b : ProgHOL 64} (ha : NoRet a) (hb : NoRet b) : NoRet (.seq a b) := by
  intro F st v
  rw [evaluateHOLFiniteState_seq_line780]
  cases h : evaluateHOLFiniteState st a with
  | mk r t =>
    have := ha st v
    rw [h] at this
    cases r with
    | none => exact hb t v
    | some _ => exact this

theorem NoRet.ite {c : ExpHOL 64} {y n : ProgHOL 64} (hy : NoRet y) (hn : NoRet n) :
    NoRet (.ite c y n) := by
  intro F st v
  rw [evaluateHOLFiniteState_ite]
  split
  · split
    · exact hn st v
    · exact hy st v
  · simp

theorem NoRet.skip : NoRet .skip := by
  intro F st v; rw [evaluateHOLFiniteState_skip]; simp

theorem NoRet.brk : NoRet .break := by
  intro F st v; rw [evaluateHOLFiniteState_break]; simp

theorem NoRet.assign {x : MlS} {e : ExpHOL 64} : NoRet (.assign .local x e) := by
  intro F st v
  rw [evaluateHOLFiniteState_assign]
  split
  · simp
  · split <;> simp

theorem NoRet.dec' {x : MlS} {sh : ShapeHOL} {e : ExpHOL 64} {p : ProgHOL 64} (hp : NoRet p) :
    NoRet (.dec x sh e p) := by
  intro F st v
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  split
  · simp
  · split
    · exact hp _ v
    · simp

theorem while_noRet {F : Type} (cond : ExpHOL 64) (body : ProgHOL 64)
    (hb : ∀ s : PanSemStateFiniteExact 64 F, ∀ v,
      (evaluateHOLFiniteState s body).1 ≠ some (.returned v)) :
    ∀ (n : Nat) (s : PanSemStateFiniteExact 64 F), s.clock ≤ n → ∀ v,
      (evaluateHOLFiniteState s (.while cond body)).1 ≠ some (.returned v) := by
  intro n
  induction n with
  | zero =>
    intro s hcl v
    rw [evaluateHOLFiniteState_while_fixClockRewrite]
    split
    · rename_i w hw
      by_cases hz : w = 0
      · simp [hz]
      · rw [if_pos hz, if_pos (by omega)]; simp
    · simp
  | succ n ih =>
    intro s hcl v
    rw [evaluateHOLFiniteState_while_fixClockRewrite]
    split
    · rename_i w hw
      by_cases hz : w = 0
      · simp [hz]
      · rw [if_pos hz]
        by_cases hc : s.clock = 0
        · rw [if_pos hc]; simp
        · rw [if_neg hc]
          have hle := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
          have hbv := hb (decClockHOLFinite s) v
          cases hbd : evaluateHOLFiniteState (decClockHOLFinite s) body with
          | mk r t =>
            rw [hbd] at hle hbv
            change t.clock ≤ s.clock - 1 at hle
            dsimp only at hbv ⊢
            cases r with
            | none => exact ih t (by omega) v
            | some r =>
              cases r with
              | «continue» => exact ih t (by omega) v
              | «break» => simp
              | returned v' => exact hbv
              | _ => simp
    · simp

theorem while_inv2 {F : Type} (I Bk : PanSemStateFiniteExact 64 F → Prop) (cond : ExpHOL 64)
    (body : ProgHOL 64)
    (hstep : ∀ s : PanSemStateFiniteExact 64 F, I s → LoopActive cond s → s.clock ≠ 0 →
      (((evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none ∨
        (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = some .continue) →
        I (evaluateHOLFiniteState (decClockHOLFinite s) body).2) ∧
      ((evaluateHOLFiniteState (decClockHOLFinite s) body).1 = some .break →
        Bk (evaluateHOLFiniteState (decClockHOLFinite s) body).2)) :
    ∀ (n : Nat) (s : PanSemStateFiniteExact 64 F), s.clock ≤ n → I s →
      (evaluateHOLFiniteState s (.while cond body)).1 = none →
      (I (evaluateHOLFiniteState s (.while cond body)).2 ∧
        CondFalse cond (evaluateHOLFiniteState s (.while cond body)).2) ∨
      Bk (evaluateHOLFiniteState s (.while cond body)).2 := by
  intro n
  induction n with
  | zero =>
    intro s hcl hs hnone
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnone ⊢
    revert hnone
    split
    · rename_i w hw
      by_cases hz : w = 0
      · subst hz; simp; exact Or.inl ⟨hs, hw⟩
      · rw [if_pos hz, if_pos (by omega)]; simp
    · simp
  | succ n ih =>
    intro s hcl hs hnone
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnone ⊢
    revert hnone
    split
    · rename_i w hw
      by_cases hz : w = 0
      · subst hz; simp; exact Or.inl ⟨hs, hw⟩
      · rw [if_pos hz]
        by_cases hc : s.clock = 0
        · rw [if_pos hc]; simp
        · rw [if_neg hc]
          have hle := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
          have hst := hstep s hs ⟨w, hw, hz⟩ hc
          cases hb : evaluateHOLFiniteState (decClockHOLFinite s) body with
          | mk r t =>
            rw [hb] at hle hst
            change t.clock ≤ s.clock - 1 at hle
            dsimp only at hst ⊢
            cases r with
            | none =>
              intro hn
              exact ih t (by omega) (hst.1 (Or.inl rfl)) hn
            | some r =>
              cases r with
              | «continue» =>
                intro hn
                exact ih t (by omega) (hst.1 (Or.inr rfl)) hn
              | «break» =>
                intro _
                exact Or.inr (hst.2 rfl)
              | _ => simp
    · simp

/-! ## 2. Frame-only `memcpy` postcondition (no `Disj` required) -/

def MemCopyFrame {F : Type} (s0 s : PanSemStateFiniteExact 64 F) (dst : BitVec 64) (len : Nat) : Prop :=
  s.code = s0.code ∧ s.memaddrs = s0.memaddrs ∧ s.shMemaddrs = s0.shMemaddrs ∧
  s.baseAddr = s0.baseAddr ∧ s.be = s0.be ∧ s.globals = s0.globals ∧
  FrameOutside s0 s [(dst.toNat, len)] (0, 0)

theorem memCopyFrame_refl {F : Type} (s0 : PanSemStateFiniteExact 64 F) (dst : BitVec 64) (len : Nat) :
    MemCopyFrame s0 s0 dst len :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ _ => rfl⟩

theorem memCopyFrame_locals_clock {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    {dst : BitVec 64} {len : Nat}
    (h : MemCopyFrame s0 s dst len) (L : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    MemCopyFrame s0 { s with locals := L, clock := k } dst len :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

private theorem mcf_seq_none {F : Type} {s : PanSemStateFiniteExact 64 F}
    {p1 p2 : ProgHOL 64} (h : (evaluateHOLFiniteState s (.seq p1 p2)).1 = none) :
    ∃ m, evaluateHOLFiniteState s p1 = (none, m) ∧
      evaluateHOLFiniteState s (.seq p1 p2) = evaluateHOLFiniteState m p2 := by
  rw [evaluateHOLFiniteState_seq_line780] at h ⊢
  cases hr : evaluateHOLFiniteState s p1 with
  | mk r1 m =>
    rw [hr] at h
    cases r1 with
    | none => exact ⟨m, rfl, rfl⟩
    | some _ => simp at h

private theorem mcf_store_word {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    {dst0 : BitVec 64} {len off : Nat}
    (hoff_le : off + 8 ≤ len) (hd_nw : dst0.toNat + len < 2 ^ 64)
    (hrel : MemCopyFrame s0 s dst0 len)
    (ed es : ExpHOL 64)
    (hed : evalAt s ed = some (.val (.word (dst0 + BitVec.ofNat 64 off))))
    (hnone : (evaluateHOLFiniteState s (.store ed (.load .one es))).1 = none) :
    MemCopyFrame s0 (evaluateHOLFiniteState s (.store ed (.load .one es))).2 dst0 len ∧
    (evaluateHOLFiniteState s (.store ed (.load .one es))).2.locals = s.locals := by
  obtain ⟨hc, hm, hsh, hba, hbe, hg, hfr⟩ := hrel
  have hl := (evaluate_store_control_frame s ed (.load .one es)).2.1
  refine ⟨?_, hl⟩
  rw [evaluateHOLFiniteState_store] at hnone ⊢
  unfold evalAt at hed
  rw [hed] at hnone ⊢
  dsimp only at hnone ⊢
  revert hnone
  split
  · rename_i v hld
    have hv_word : ∃ w, v = .val (.word w) := by
      simp only [evalHOLExact, isWfShapeExactHOL, ↓reduceIte, memLoadHOLExact] at hld
      split at hld
      · rename_i va hva
        split at hld
        · rcases hm_va : s.memory va with ⟨w⟩
          rw [hm_va] at hld
          injection hld with heq
          exact ⟨w, heq.symm⟩
        · cases hld
      · cases hld
    obtain ⟨w, rfl⟩ := hv_word
    cases hst : @panMemStoresHOL 64 _ (dst0 + BitVec.ofNat 64 off) (flattenHOL (.val (.word w)))
        s.memaddrs (fun a => Classical.propDecidable (s.memaddrs a)) s.memory with
    | none => intro hn; cases hn
    | some mem' =>
      intro _
      dsimp only
      obtain ⟨_, rfl⟩ := stores_word _ hst
      set x := dst0 + BitVec.ofNat 64 off
      have hx_nat : x.toNat = dst0.toNat + off := by
        simp only [x, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      refine ⟨hc, hm, hsh, hba, hbe, hg, ?_⟩
      intro c hk hf
      by_cases hcx : c = x
      · exfalso; subst hcx
        exact hk (dst0.toNat, len) (List.mem_singleton.2 rfl) ⟨by omega, by omega⟩
      · simp only [updW, hcx, ↓reduceIte]
        exact hfr c hk hf
  · intro hn; cases hn

private theorem mcf_store_byte {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    {dst0 : BitVec 64} {len off : Nat}
    (hoff_lt : off < len) (hd_nw : dst0.toNat + len < 2 ^ 64)
    (hrel : MemCopyFrame s0 s dst0 len)
    (ed es : ExpHOL 64)
    (hed : evalAt s ed = some (.val (.word (dst0 + BitVec.ofNat 64 off))))
    (hnone : (evaluateHOLFiniteState s (.storeByte ed es)).1 = none) :
    MemCopyFrame s0 (evaluateHOLFiniteState s (.storeByte ed es)).2 dst0 len ∧
    (evaluateHOLFiniteState s (.storeByte ed es)).2.locals = s.locals := by
  obtain ⟨hc, hm, hsh, hba, hbe, hg, hfr⟩ := hrel
  have hl := (evaluate_storeByte_control_frame s ed es).2.2.1
  refine ⟨?_, hl⟩
  rw [evaluateHOLFiniteState_storeByte] at hnone ⊢
  unfold evalAt at hed
  rw [hed] at hnone ⊢
  dsimp only at hnone ⊢
  revert hnone
  split
  · rename_i vw hlb
    set x := dst0 + BitVec.ofNat 64 off
    have hx_nat : x.toNat = dst0.toNat + off := by
      simp only [x, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    split
    · rename_i mem' hst
      intro _
      dsimp only
      have hcell_frame : ∀ c : BitVec 64, c ≠ panByteAlignHOL x → mem' c = s.memory c := by
        intro c hne
        unfold panMemStoreByteWord8HOL at hst
        rcases s.memory (panByteAlignHOL x) with ⟨cell⟩
        dsimp only at hst
        split at hst
        · injection hst with hmeq; subst hmeq; simp [hne]
        · cases hst
      refine ⟨hc, hm, hsh, hba, hbe, hg, ?_⟩
      intro c hk hf
      by_cases hcx : c = panByteAlignHOL x
      · exfalso; subst hcx
        apply hk (dst0.toNat, len) (List.mem_singleton.2 rfl)
        unfold CellHits
        rw [panByteAlign_toNat64]
        omega
      · change mem' c = s0.memory c
        rw [hcell_frame c hcx]
        exact hfr c hk hf
    · intro hn; cases hn
  · intro hn; cases hn

private def mcfNoRet : ProgHOL 64 → Bool
  | .seq a b => mcfNoRet a && mcfNoRet b
  | .ite _ a b => mcfNoRet a && mcfNoRet b
  | .while _ a => mcfNoRet a
  | .assign .local _ _ | .store _ _ | .storeByte _ _ | .skip => true
  | _ => false

private theorem mcf_eval_noRet {F : Type} (p : ProgHOL 64) (hp : mcfNoRet p = true)
    (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64) :
    (evaluateHOLFiniteState s p).1 ≠ some (.returned v) := by
  cases shape : p with
  | skip => rw [evaluateHOLFiniteState_skip]; simp
  | assign k _ _ =>
    cases k with
    | global => simp [shape, mcfNoRet] at hp
    | «local» => rw [evaluateHOLFiniteState_assign]; split <;> [simp; (split <;> simp)]
  | store _ _ =>
    rw [evaluateHOLFiniteState_store]; split <;> [(split <;> [(split <;> simp); simp]); simp]
  | storeByte _ _ =>
    rw [evaluateHOLFiniteState_storeByte]; split <;> [(split <;> [(split <;> simp); simp]); simp]
  | seq a b =>
    have hab : mcfNoRet a = true ∧ mcfNoRet b = true := by
      simpa [shape, mcfNoRet, Bool.and_eq_true] using hp
    have rem := evaluateHOLFiniteState_clock_le s a
    rw [evaluateHOLFiniteState_seq_line780]
    have ha := mcf_eval_noRet a hab.1 s v
    rcases hr : evaluateHOLFiniteState s a with ⟨r, m⟩
    rw [hr] at ha rem
    have mclk : m.clock ≤ s.clock := rem
    cases r with
    | none => exact mcf_eval_noRet b hab.2 m v
    | some _ => exact ha
  | ite _ a b =>
    have hab : mcfNoRet a = true ∧ mcfNoRet b = true := by
      simpa [shape, mcfNoRet, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact mcf_eval_noRet b hab.2 s v
      · exact mcf_eval_noRet a hab.1 s v
    · simp
  | «while» cond body =>
    have hb : mcfNoRet body = true := by simpa [shape, mcfNoRet] using hp
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · simp
        · have dec_lt : (decClockHOLFinite s).clock < s.clock := by
            simp only [decClockHOLFinite]; omega
          dsimp only
          rw [fixClockHOLFinite_evaluateState]
          have ih1 := mcf_eval_noRet body hb (decClockHOLFinite s) v
          have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨r1, mid⟩
          rw [hbr] at ih1 rem
          have smaller : mid.clock < s.clock := by
            change mid.clock ≤ s.clock - 1 at rem; omega
          cases r1 with
          | none => exact mcf_eval_noRet (.while cond body) (by simpa [mcfNoRet] using hb) mid v
          | some r1 =>
            cases r1 with
            | «continue» => exact mcf_eval_noRet (.while cond body) (by simpa [mcfNoRet] using hb) mid v
            | returned _ => exact ih1
            | _ => simp
      · simp
    · simp
  | _ => simp [shape, mcfNoRet] at hp
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

private def mcfNoBreak : ProgHOL 64 → Bool
  | .seq a b => mcfNoBreak a && mcfNoBreak b
  | .assign .local _ _ | .store _ _ | .storeByte _ _ | .skip => true
  | _ => false

private theorem mcf_eval_noBreak {F : Type} (p : ProgHOL 64) (hp : mcfNoBreak p = true)
    (s : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState s p).1 ≠ some .break := by
  cases shape : p with
  | skip => simp [evaluateHOLFiniteState_skip]
  | assign k _ _ =>
    cases k with
    | global => simp [shape, mcfNoBreak] at hp
    | «local» => rw [evaluateHOLFiniteState_assign]; split <;> [simp; (split <;> simp)]
  | store _ _ =>
    rw [evaluateHOLFiniteState_store]; split <;> [(split <;> [(split <;> simp); simp]); simp]
  | storeByte _ _ =>
    rw [evaluateHOLFiniteState_storeByte]; split <;> [(split <;> [(split <;> simp); simp]); simp]
  | seq a b =>
    have hab : mcfNoBreak a = true ∧ mcfNoBreak b = true := by
      simpa [shape, mcfNoBreak, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_seq_line780]
    have ha := mcf_eval_noBreak a hab.1 s
    rcases hr : evaluateHOLFiniteState s a with ⟨r, m⟩
    rw [hr] at ha
    cases r with
    | none => exact mcf_eval_noBreak b hab.2 m
    | some _ => exact ha
  | _ => simp [shape, mcfNoBreak] at hp

private theorem mcf_while_loop {F : Type} (s0 : PanSemStateFiniteExact 64 F)
    (dst n : BitVec 64) (hn_small : n.toNat + 32 < 2 ^ 63)
    (step : BitVec 64) (cond : ExpHOL 64) (body : ProgHOL 64)
    (hnc : noTopContinue body = true) (hnb : mcfNoBreak body = true)
    (hcond : (cond = .cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const step]) ∧ (step = 32#64 ∨ step = 8#64)) ∨
             (cond = .cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n")) ∧ step = 1#64))
    (hbody_spec : ∀ (st : PanSemStateFiniteExact 64 F) (wi : BitVec 64),
      MemCopyFrame s0 st dst n.toNat →
      wi.toNat + step.toNat ≤ n.toNat →
      st.locals.lookup (ofString "dst") = some (.val (.word dst)) →
      st.locals.lookup (ofString "n") = some (.val (.word n)) →
      st.locals.lookup (ofString "i") = some (.val (.word wi)) →
      (evaluateHOLFiniteState st body).1 = none →
      MemCopyFrame s0 (evaluateHOLFiniteState st body).2 dst n.toNat ∧
      (evaluateHOLFiniteState st body).2.locals.lookup (ofString "dst") = some (.val (.word dst)) ∧
      (evaluateHOLFiniteState st body).2.locals.lookup (ofString "n") = some (.val (.word n)) ∧
      (evaluateHOLFiniteState st body).2.locals.lookup (ofString "i") = some (.val (.word (wi + step))))
    (clk : Nat) (s u : PanSemStateFiniteExact 64 F) (wi : BitVec 64)
    (hclk : s.clock ≤ clk)
    (hrel : MemCopyFrame s0 s dst n.toNat)
    (hwi_le : wi.toNat ≤ n.toNat)
    (hd_loc : s.locals.lookup (ofString "dst") = some (.val (.word dst)))
    (hn_loc : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (hi_loc : s.locals.lookup (ofString "i") = some (.val (.word wi)))
    (hrun : evaluateHOLFiniteState s (.while cond body) = (none, u)) :
    ∃ wi' : BitVec 64,
      MemCopyFrame s0 u dst n.toNat ∧
      wi'.toNat ≤ n.toNat ∧
      u.locals.lookup (ofString "dst") = some (.val (.word dst)) ∧
      u.locals.lookup (ofString "n") = some (.val (.word n)) ∧
      u.locals.lookup (ofString "i") = some (.val (.word wi')) := by
  induction clk generalizing s wi with
  | zero =>
    rw [evaluateHOLFiniteState_while_total] at hrun
    split at hrun
    · split at hrun
      · split at hrun
        · simp at hrun
        · omega
      · injection hrun with _ hu; subst hu
        exact ⟨wi, hrel, hwi_le, hd_loc, hn_loc, hi_loc⟩
    · simp at hrun
  | succ clk ih =>
    rw [evaluateHOLFiniteState_while_total] at hrun
    split at hrun
    · rename_i cw hcond_ev
      split at hrun
      · rename_i hcw_nz
        split at hrun
        · simp at hrun
        · dsimp only at hrun
          rw [fixClockHOLFinite_evaluateState] at hrun
          have hstep_le : wi.toNat + step.toNat ≤ n.toNat := by
            rw [evalHOLFinite_eq_toExact] at hcond_ev
            rcases hcond with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩
            · obtain ⟨va, vb, hva, hvb, hcw⟩ := evalAt_cmp s .notLower _ _ cw hcond_ev
              simp [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact, hn_loc, hi_loc, valueIsWord, valueWord, wordOpHOL, wordOp] at hva hvb
              subst hva hvb
              have h32 : (32#64 : BitVec 64).toNat = 32 := rfl
              change wi.toNat + (32#64 : BitVec 64).toNat ≤ n.toNat
              rw [h32]
              have hadd : (wi + 32#64).toNat = wi.toNat + 32 := by rw [BitVec.toNat_add, h32, Nat.mod_eq_of_lt (by omega)]
              by_contra hgt
              have hnle : ¬ (wi + 32#64 ≤ n) := by rw [BitVec.le_def, hadd]; omega
              simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hnle] at hcw
              exact hcw_nz hcw
            · obtain ⟨va, vb, hva, hvb, hcw⟩ := evalAt_cmp s .notLower _ _ cw hcond_ev
              simp [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact, hn_loc, hi_loc, valueIsWord, valueWord, wordOpHOL, wordOp] at hva hvb
              subst hva hvb
              have h8 : (8#64 : BitVec 64).toNat = 8 := rfl
              change wi.toNat + (8#64 : BitVec 64).toNat ≤ n.toNat
              rw [h8]
              have hadd : (wi + 8#64).toNat = wi.toNat + 8 := by rw [BitVec.toNat_add, h8, Nat.mod_eq_of_lt (by omega)]
              by_contra hgt
              have hnle : ¬ (wi + 8#64 ≤ n) := by rw [BitVec.le_def, hadd]; omega
              simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hnle] at hcw
              exact hcw_nz hcw
            · obtain ⟨va, vb, hva, hvb, hcw⟩ := evalAt_cmp s .lower _ _ cw hcond_ev
              simp [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, hn_loc, hi_loc] at hva hvb
              subst hva hvb
              have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
              change wi.toNat + (1#64 : BitVec 64).toNat ≤ n.toNat
              rw [h1]
              by_contra hgt
              have hnlt : ¬ (wi < n) := by rw [BitVec.lt_def]; omega
              simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hnlt] at hcw
              exact hcw_nz hcw
          let sd := decClockHOLFinite s
          have hrel_sd : MemCopyFrame s0 sd dst n.toNat := memCopyFrame_locals_clock hrel s.locals (s.clock - 1)
          have hnc' := evaluate_noTopContinue body hnc sd
          have hnb' := mcf_eval_noBreak body hnb sd
          have hrem := evaluateHOLFiniteState_clock_le sd body
          rcases hbr : evaluateHOLFiniteState sd body with ⟨rb, mid⟩
          rw [hbr] at hrun hnc' hnb' hrem
          cases rb with
          | none =>
            have hb := hbody_spec sd wi hrel_sd hstep_le hd_loc hn_loc hi_loc (by rw [hbr])
            rw [hbr] at hb
            obtain ⟨hrel_m, hd_m, hn_m, hi_m⟩ := hb
            have h263 : (2 ^ 63 : Nat) < 2 ^ 64 := by decide
            have hw_add : (wi + step).toNat = wi.toNat + step.toNat := by
              rcases hcond with ⟨_, rfl | rfl⟩ | ⟨_, rfl⟩
              · rw [BitVec.toNat_add, show (32#64).toNat = 32 from rfl, Nat.mod_eq_of_lt (by omega)]
              · rw [BitVec.toNat_add, show (8#64).toNat = 8 from rfl, Nat.mod_eq_of_lt (by omega)]
              · rw [BitVec.toNat_add, show (1#64).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
            exact ih mid (wi + step) (by change mid.clock ≤ s.clock - 1 at hrem; omega)
              hrel_m (by omega) hd_m hn_m hi_m hrun
          | some r =>
            cases r with
            | «continue» => exact absurd rfl hnc'
            | «break» => exact absurd rfl hnb'
            | _ => simp at hrun
      · injection hrun with _ hu; subst hu
        exact ⟨wi, hrel, hwi_le, hd_loc, hn_loc, hi_loc⟩
    · simp at hrun

/-- Frame-only `memcpy(dst, src, n)` postcondition without any `Disj` requirement:
only cells hitting `(dst.toNat, n.toNat)` can change, and metadata/`be`/`globals` are preserved. -/
theorem memcpy_body_frame {F : Type} (s0 : PanSemStateFiniteExact 64 F)
    (dst n : BitVec 64)
    (hd_nw : dst.toNat + n.toNat < 2 ^ 64)
    (hn_small : n.toNat + 32 < 2 ^ 63)
    (hd_loc : s0.locals.lookup (ofString "dst") = some (.val (.word dst)))
    (hn_loc : s0.locals.lookup (ofString "n") = some (.val (.word n)))
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s0 (sourceFnBody Guest.Software.guestFn_memcpy)).1 =
      some (.returned v)) :
    v = .val (.word 0#64) ∧
    MemCopyFrame s0 (evaluateHOLFiniteState s0 (sourceFnBody Guest.Software.guestFn_memcpy)).2
      dst n.toNat := by
  have seq_ret_or_none : ∀ (s : PanSemStateFiniteExact 64 F) (p1 p2 : ProgHOL 64) (rv : ValueHOL 64),
      (evaluateHOLFiniteState s (.seq p1 p2)).1 = some (.returned rv) →
      (evaluateHOLFiniteState s p1).1 = some (.returned rv) ∨
        ∃ m, evaluateHOLFiniteState s p1 = (none, m) ∧
          (evaluateHOLFiniteState m p2).1 = some (.returned rv) := by
    intro s p1 p2 rv h
    rw [evaluateHOLFiniteState_seq_line780] at h
    rcases hr : evaluateHOLFiniteState s p1 with ⟨r1, m⟩
    rw [hr] at h
    cases r1 with
    | none => exact Or.inr ⟨m, rfl, h⟩
    | some _ => exact Or.inl h
  have ed_i : ∀ (st : PanSemStateFiniteExact 64 F) (wi : BitVec 64),
      st.locals.lookup (ofString "dst") = some (.val (.word dst)) →
      st.locals.lookup (ofString "i") = some (.val (.word wi)) →
      evalAt st (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) =
        some (.val (.word (dst + BitVec.ofNat 64 wi.toNat))) := by
    intro st wi hd hi
    simp [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact, hd, hi, valueIsWord, valueWord, wordOpHOL, wordOp]
  have ed_ik : ∀ (st : PanSemStateFiniteExact 64 F) (wi : BitVec 64) (off : Nat),
      wi.toNat + off ≤ n.toNat →
      st.locals.lookup (ofString "dst") = some (.val (.word dst)) →
      st.locals.lookup (ofString "i") = some (.val (.word wi)) →
      evalAt st (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const (BitVec.ofNat 64 off)]) =
        some (.val (.word (dst + BitVec.ofNat 64 (wi.toNat + off)))) := by
    intro st wi off hle hd hi
    simp only [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact, hd, hi,
      List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
      valueIsWord, valueWord, wordOpHOL, wordOp, BitVec.add_zero,
      Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq]
    apply BitVec.eq_of_toNat_eq
    have hz : (0 : BitVec 64).toNat = 0 := rfl
    have h263 : (2 ^ 63 : Nat) < 2 ^ 64 := by decide
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hz]
    omega
  have assign_inc_ok : ∀ (st : PanSemStateFiniteExact 64 F) (wi step : BitVec 64),
      MemCopyFrame s0 st dst n.toNat →
      st.locals.lookup (ofString "dst") = some (.val (.word dst)) →
      st.locals.lookup (ofString "n") = some (.val (.word n)) →
      st.locals.lookup (ofString "i") = some (.val (.word wi)) →
      MemCopyFrame s0 (evaluateHOLFiniteState st (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const step]))).2 dst n.toNat ∧
      (evaluateHOLFiniteState st (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const step]))).2.locals.lookup (ofString "dst") = some (.val (.word dst)) ∧
      (evaluateHOLFiniteState st (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const step]))).2.locals.lookup (ofString "n") = some (.val (.word n)) ∧
      (evaluateHOLFiniteState st (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const step]))).2.locals.lookup (ofString "i") = some (.val (.word (wi + step))) := by
    intro st wi step hrel hd hn hi
    have hrun : evaluateHOLFiniteState st (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const step])) =
        (none, setVarHOLFinite (ofString "i") (.val (.word (wi + step))) st) := by
      simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hi, wordOpHOL, wordOp,
        valueIsWord, valueWord, lookupKvarHOLExact, isValidValueHOLExact, setKvarHOLFinite,
        shapeOfHOLExact, shapeEqHOL]
    rw [hrun]
    refine ⟨memCopyFrame_locals_clock hrel _ st.clock, ?_, ?_, ?_⟩
    · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hd, show ofString "i" ≠ ofString "dst" by decide]
    · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn, show ofString "i" ≠ ofString "n" by decide]
    · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_memcpy,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map] at hret ⊢
  rw [evaluateHOLFiniteState_dec_total] at hret ⊢
  dsimp only at hret ⊢
  have hev0 : @evalHOLExact 64 F _ s0.toExact (fun x => Classical.propDecidable (s0.memaddrs x)) (.const 0#64) =
      some (.val (.word 0#64)) := rfl
  rw [hev0] at hret ⊢
  dsimp only at hret ⊢
  have hsh0 : shapeEqHOL .one (shapeOfHOLExact (.val (.word 0#64))) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  rw [if_pos hsh0] at hret ⊢
  dsimp only at hret ⊢
  set s1 := setVarHOLFinite (ofString "i") (.val (.word 0#64)) s0
  have hs1_rel : MemCopyFrame s0 s1 dst n.toNat := memCopyFrame_locals_clock (memCopyFrame_refl s0 dst n.toNat) _ s0.clock
  have hs1_d : s1.locals.lookup (ofString "dst") = some (.val (.word dst)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hd_loc, show ofString "i" ≠ ofString "dst" by decide]
  have hs1_n : s1.locals.lookup (ofString "n") = some (.val (.word n)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn_loc, show ofString "i" ≠ ofString "n" by decide]
  have hs1_i : s1.locals.lookup (ofString "i") = some (.val (.word 0#64)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  rcases seq_ret_or_none s1 _ _ _ hret with h_ite_ret | ⟨s2, hs2, hret2⟩
  · exact False.elim (mcf_eval_noRet _ rfl s1 v h_ite_ret)
  have hs2_inv : ∃ wi2 : BitVec 64,
      MemCopyFrame s0 s2 dst n.toNat ∧
      wi2.toNat ≤ n.toNat ∧
      s2.locals.lookup (ofString "dst") = some (.val (.word dst)) ∧
      s2.locals.lookup (ofString "n") = some (.val (.word n)) ∧
      s2.locals.lookup (ofString "i") = some (.val (.word wi2)) := by
    rw [evaluateHOLFiniteState_ite] at hs2
    split at hs2
    · split at hs2
      · rw [evaluateHOLFiniteState_skip] at hs2; injection hs2 with _ e; rw [← e]
        exact ⟨0#64, hs1_rel, Nat.zero_le _, hs1_d, hs1_n, hs1_i⟩
      · obtain ⟨m32, hm32, eq_s2⟩ := mcf_seq_none (congrArg Prod.fst hs2)
        have hs2_8 : evaluateHOLFiniteState m32 _ = (none, s2) := eq_s2.symm.trans hs2
        have hl32 := mcf_while_loop s0 dst n hn_small 32#64 _ _ rfl rfl (Or.inl ⟨rfl, Or.inl rfl⟩)
          (fun st wi hrel hstep hd hn hi hnone => by
            have h32 : (32#64 : BitVec 64).toNat = 32 := rfl
            rw [h32] at hstep
            obtain ⟨m1, hm1, eq1⟩ := mcf_seq_none hnone; rw [eq1] at hnone ⊢
            obtain ⟨r1, hl1⟩ := mcf_store_word (by omega) hd_nw hrel _ _ (ed_i st wi hd hi) (congrArg Prod.fst hm1)
            rw [hm1] at r1 hl1
            obtain ⟨m2, hm2, eq2⟩ := mcf_seq_none hnone; rw [eq2] at hnone ⊢
            obtain ⟨r2, hl2⟩ := mcf_store_word (by omega) hd_nw r1 _ _ (ed_ik m1 wi 8 (by omega) (hl1 ▸ hd) (hl1 ▸ hi)) (congrArg Prod.fst hm2)
            rw [hm2] at r2 hl2; have hl2' := hl2.trans hl1
            obtain ⟨m3, hm3, eq3⟩ := mcf_seq_none hnone; rw [eq3] at hnone ⊢
            obtain ⟨r3, hl3⟩ := mcf_store_word (by omega) hd_nw r2 _ _ (ed_ik m2 wi 16 (by omega) (hl2' ▸ hd) (hl2' ▸ hi)) (congrArg Prod.fst hm3)
            rw [hm3] at r3 hl3; have hl3' := hl3.trans hl2'
            obtain ⟨m4, hm4, eq4⟩ := mcf_seq_none hnone; rw [eq4] at hnone ⊢
            obtain ⟨r4, hl4⟩ := mcf_store_word (by omega) hd_nw r3 _ _ (ed_ik m3 wi 24 (by omega) (hl3' ▸ hd) (hl3' ▸ hi)) (congrArg Prod.fst hm4)
            rw [hm4] at r4 hl4; have hl4' := hl4.trans hl3'
            exact assign_inc_ok m4 wi 32#64 r4 (hl4' ▸ hd) (hl4' ▸ hn) (hl4' ▸ hi))
          s1.clock s1 m32 0#64 le_rfl hs1_rel (Nat.zero_le _) hs1_d hs1_n hs1_i hm32
        obtain ⟨wi1, hrel1, hle1, hd1, hn1, hi1⟩ := hl32
        have hl8w := mcf_while_loop s0 dst n hn_small 8#64 _ _ rfl rfl (Or.inl ⟨rfl, Or.inr rfl⟩)
          (fun st wi hrel hstep hd hn hi hnone => by
            have h8 : (8#64 : BitVec 64).toNat = 8 := rfl
            rw [h8] at hstep
            obtain ⟨m1, hm1, eq1⟩ := mcf_seq_none hnone; rw [eq1] at hnone ⊢
            obtain ⟨r1, hl1⟩ := mcf_store_word (by omega) hd_nw hrel _ _ (ed_i st wi hd hi) (congrArg Prod.fst hm1)
            rw [hm1] at r1 hl1
            exact assign_inc_ok m1 wi 8#64 r1 (hl1 ▸ hd) (hl1 ▸ hn) (hl1 ▸ hi))
          m32.clock m32 s2 wi1 le_rfl hrel1 hle1 hd1 hn1 hi1 hs2_8
        exact hl8w
    · simp at hs2
  obtain ⟨wi2, hrel2, hle2, hd2, hn2, hi2⟩ := hs2_inv
  rcases seq_ret_or_none s2 _ _ _ hret2 with h_l8b_ret | ⟨s3, hs3, hret3⟩
  · exact False.elim (mcf_eval_noRet _ rfl s2 v h_l8b_ret)
  have hl8b := mcf_while_loop s0 dst n hn_small 8#64 _ _ rfl rfl (Or.inl ⟨rfl, Or.inr rfl⟩)
    (fun st wi hrel hstep hd hn hi hnone => by
      have h8 : (8#64 : BitVec 64).toNat = 8 := rfl
      rw [h8] at hstep
      obtain ⟨m0, hm0, eq0⟩ := mcf_seq_none hnone; rw [eq0] at hnone ⊢
      obtain ⟨r0, hl0⟩ := mcf_store_byte (by omega) hd_nw hrel _ _ (ed_i st wi hd hi) (congrArg Prod.fst hm0)
      rw [hm0] at r0 hl0
      obtain ⟨m1, hm1, eq1⟩ := mcf_seq_none hnone; rw [eq1] at hnone ⊢
      obtain ⟨r1, hl1⟩ := mcf_store_byte (by omega) hd_nw r0 _ _ (ed_ik m0 wi 1 (by omega) (hl0 ▸ hd) (hl0 ▸ hi)) (congrArg Prod.fst hm1)
      rw [hm1] at r1 hl1; have hl1' := hl1.trans hl0
      obtain ⟨m2, hm2, eq2⟩ := mcf_seq_none hnone; rw [eq2] at hnone ⊢
      obtain ⟨r2, hl2⟩ := mcf_store_byte (by omega) hd_nw r1 _ _ (ed_ik m1 wi 2 (by omega) (hl1' ▸ hd) (hl1' ▸ hi)) (congrArg Prod.fst hm2)
      rw [hm2] at r2 hl2; have hl2' := hl2.trans hl1'
      obtain ⟨m3, hm3, eq3⟩ := mcf_seq_none hnone; rw [eq3] at hnone ⊢
      obtain ⟨r3, hl3⟩ := mcf_store_byte (by omega) hd_nw r2 _ _ (ed_ik m2 wi 3 (by omega) (hl2' ▸ hd) (hl2' ▸ hi)) (congrArg Prod.fst hm3)
      rw [hm3] at r3 hl3; have hl3' := hl3.trans hl2'
      obtain ⟨m4, hm4, eq4⟩ := mcf_seq_none hnone; rw [eq4] at hnone ⊢
      obtain ⟨r4, hl4⟩ := mcf_store_byte (by omega) hd_nw r3 _ _ (ed_ik m3 wi 4 (by omega) (hl3' ▸ hd) (hl3' ▸ hi)) (congrArg Prod.fst hm4)
      rw [hm4] at r4 hl4; have hl4' := hl4.trans hl3'
      obtain ⟨m5, hm5, eq5⟩ := mcf_seq_none hnone; rw [eq5] at hnone ⊢
      obtain ⟨r5, hl5⟩ := mcf_store_byte (by omega) hd_nw r4 _ _ (ed_ik m4 wi 5 (by omega) (hl4' ▸ hd) (hl4' ▸ hi)) (congrArg Prod.fst hm5)
      rw [hm5] at r5 hl5; have hl5' := hl5.trans hl4'
      obtain ⟨m6, hm6, eq6⟩ := mcf_seq_none hnone; rw [eq6] at hnone ⊢
      obtain ⟨r6, hl6⟩ := mcf_store_byte (by omega) hd_nw r5 _ _ (ed_ik m5 wi 6 (by omega) (hl5' ▸ hd) (hl5' ▸ hi)) (congrArg Prod.fst hm6)
      rw [hm6] at r6 hl6; have hl6' := hl6.trans hl5'
      obtain ⟨m7, hm7, eq7⟩ := mcf_seq_none hnone; rw [eq7] at hnone ⊢
      obtain ⟨r7, hl7⟩ := mcf_store_byte (by omega) hd_nw r6 _ _ (ed_ik m6 wi 7 (by omega) (hl6' ▸ hd) (hl6' ▸ hi)) (congrArg Prod.fst hm7)
      rw [hm7] at r7 hl7; have hl7' := hl7.trans hl6'
      exact assign_inc_ok m7 wi 8#64 r7 (hl7' ▸ hd) (hl7' ▸ hn) (hl7' ▸ hi))
    s2.clock s2 s3 wi2 le_rfl hrel2 hle2 hd2 hn2 hi2 hs3
  obtain ⟨wi3, hrel3, hle3, hd3, hn3, hi3⟩ := hl8b
  rcases seq_ret_or_none s3 _ _ _ hret3 with h_l1b_ret | ⟨s4, hs4, hret4⟩
  · exact False.elim (mcf_eval_noRet _ rfl s3 v h_l1b_ret)
  have hl1b := mcf_while_loop s0 dst n hn_small 1#64 _ _ rfl rfl (Or.inr ⟨rfl, rfl⟩)
    (fun st wi hrel hstep hd hn hi hnone => by
      have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
      rw [h1] at hstep
      obtain ⟨m0, hm0, eq0⟩ := mcf_seq_none hnone; rw [eq0] at hnone ⊢
      obtain ⟨r0, hl0⟩ := mcf_store_byte (by omega) hd_nw hrel _ _ (ed_i st wi hd hi) (congrArg Prod.fst hm0)
      rw [hm0] at r0 hl0
      exact assign_inc_ok m0 wi 1#64 r0 (hl0 ▸ hd) (hl0 ▸ hn) (hl0 ▸ hi))
    s3.clock s3 s4 wi3 le_rfl hrel3 hle3 hd3 hn3 hi3 hs4
  obtain ⟨_, hrel4, _, _, _, _⟩ := hl1b
  have hret_eval : evaluateHOLFiniteState s4 (.return (.const 0#64)) =
      (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite s4) := by
    simp [evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL]
  rw [hret_eval] at hret4
  injection hret4 with hv_eq; injection hv_eq with hv_eq'
  refine ⟨hv_eq'.symm, ?_⟩
  rw [evaluateHOLFiniteState_seq_line780, hs2]
  dsimp only
  rw [evaluateHOLFiniteState_seq_line780, hs3]
  dsimp only
  rw [evaluateHOLFiniteState_seq_line780, hs4]
  dsimp only
  rw [hret_eval]
  exact memCopyFrame_locals_clock hrel4 _ s4.clock

/-! ## 3. `htab_find_leaf` and `htab_set` descent loop -/

theorem memW_node {F : Type} (x : PanSemStateFiniteExact 64 F) (nd w : BitVec 64) (off : Nat) :
    memW x (nd.toNat + 32 * w.toNat + off) =
      (match x.memory (nd + w * 32 + BitVec.ofNat 64 off) with | .word u => u.toNat) := by
  unfold memW; rw [ofNat_node_addr]

theorem ev_node_load {F : Type} (s : PanSemStateFiniteExact 64 F) (nd w off : BitVec 64)
    (h1 : s.locals.lookup (ofString "nodes") = some (.val (.word nd)))
    (h2 : s.locals.lookup (ofString "n") = some (.val (.word w))) (v : ValueHOL 64)
    (h : evalAt s (.load .one (.op .add [.var .local (ofString "nodes"),
      .panop .mul [.var .local (ofString "n"), .const 32], .const off])) = some v) :
    s.memaddrs (nd + w * 32 + off) ∧ v = .val (s.memory (nd + w * 32 + off)) := by
  simp [evalAt, evalHOLExact, evalListHOLExact, h1, h2, panOpHOL, valueIsWord, valueWord, wordOpHOL,
    wordOp, memLoadHOLExact] at h
  rw [BitVec.add_assoc]
  exact ⟨h.1, h.2.symm⟩

theorem ev_field_load {F : Type} (s : PanSemStateFiniteExact 64 F) (x : MlS) (tw off : BitVec 64)
    (h1 : s.locals.lookup x = some (.val (.word tw))) (v : ValueHOL 64)
    (h : evalAt s (.load .one (.op .add [.var .local x, .const off])) = some v) :
    s.memaddrs (tw + off) ∧ v = .val (s.memory (tw + off)) := by
  simp [evalAt, evalHOLExact, evalListHOLExact, h1, valueIsWord, valueWord, wordOpHOL,
    wordOp, memLoadHOLExact] at h
  exact ⟨h.1, h.2.symm⟩

theorem LocFrame.setVar {F : Type} {s t : PanSemStateFiniteExact 64 F} (h : LocFrame s t)
    (x : MlS) (v : ValueHOL 64) : LocFrame s (setVarHOLFinite x v t) := h.locals _

theorem LocFrame.emptyLocals {F : Type} {s t : PanSemStateFiniteExact 64 F} (h : LocFrame s t) :
    LocFrame s (emptyLocalsHOLFinite t) := h.locals _

theorem LocFrame.memory {F : Type} {s t : PanSemStateFiniteExact 64 F} (h : LocFrame s t) :
    t.memory = s.memory := by
  unfold LocFrame at h; rw [h]

theorem locFrameW_dec {F : Type} {s : PanSemStateFiniteExact 64 F} (p : ProgHOL 64)
    (hp : locOnlyW p = true) : LocFrame s (evaluateHOLFiniteState (decClockHOLFinite s) p).2 := by
  have := locFrameW_eval p hp (decClockHOLFinite s)
  unfold LocFrame at this ⊢
  rw [this]; rfl

theorem active_n_ne {F : Type} (x : PanSemStateFiniteExact 64 F) (w : BitVec 64)
    (hn : x.locals.lookup (ofString "n") = some (.val (.word w)))
    (h : LoopActive (.cmp .notEqual (.var .local (ofString "n")) (.const 0)) x) : w ≠ 0 := by
  obtain ⟨c, hc, hnz⟩ := h
  change evalAt x _ = _ at hc
  obtain ⟨a, b, ha, hb, hcw⟩ := evalAt_cmp x .notEqual _ _ c hc
  simp [evalAt, evalHOLExact, hn] at ha
  simp [evalAt, evalHOLExact] at hb
  subst ha hb
  intro hw; subst hw
  simp [Compiler.Encoders.Asm.wordCmpHOL] at hcw
  exact hnz hcw

theorem condFalse_n_eq_zero {F : Type} (x : PanSemStateFiniteExact 64 F) (w : BitVec 64)
    (hn : x.locals.lookup (ofString "n") = some (.val (.word w)))
    (hcf : CondFalse (.cmp .notEqual (.var .local (ofString "n")) (.const 0)) x) : w = 0 := by
  unfold CondFalse at hcf
  change evalAt x _ = _ at hcf
  obtain ⟨a, b, ha, hb, hcw⟩ := evalAt_cmp x .notEqual _ _ 0 hcf
  simp [evalAt, evalHOLExact, hn] at ha hb
  subst ha hb
  by_cases hw0 : w = 0#64
  · exact hw0
  · exfalso; simp [Compiler.Encoders.Asm.wordCmpHOL, hw0] at hcw

theorem fl_iter {F : Type} (x : PanSemStateFiniteExact 64 F) (nd w kb : BitVec 64)
    (S : List Nat)
    (hnd : x.locals.lookup (ofString "nodes") = some (.val (.word nd)))
    (hn : x.locals.lookup (ofString "n") = some (.val (.word w)))
    (hkb : x.locals.lookup (ofString "keybits") = some (.val (.word kb)))
    (hw : w.toNat ∈ S)
    (htree : memW x (nd.toNat + 32 * w.toNat + 24) ≠ kb.toNat →
      memW x (nd.toNat + 32 * w.toNat + 8) ∈ S ∧ memW x (nd.toNat + 32 * w.toNat + 16) ∈ S)
    (body : ProgHOL 64)
    (hbody : body = .dec (ofString "b") .one (.load .one (.op .add [.var .local (ofString "nodes"),
        .panop .mul [.var .local (ofString "n"), .const 32], .const 24]))
      (.seq (.ite (.cmp .equal (.var .local (ofString "b")) (.var .local (ofString "keybits")))
          .break .skip)
        (.ite (.cmp .equal (.op .and [.shift .lsr (.loadByte (.op .add [.var .local (ofString "key"),
            .shift .lsr (.var .local (ofString "b")) (.const 3)])) (.op .sub [.const 7,
            .op .and [.var .local (ofString "b"), .const 7]]), .const 1]) (.const 0))
          (.assign .local (ofString "n") (.load .one (.op .add [.var .local (ofString "nodes"),
            .panop .mul [.var .local (ofString "n"), .const 32], .const 8])))
          (.assign .local (ofString "n") (.load .one (.op .add [.var .local (ofString "nodes"),
            .panop .mul [.var .local (ofString "n"), .const 32], .const 16]))))))
    : Flw x body (fun _ t => ∃ w' : BitVec 64,
        t.locals.lookup (ofString "n") = some (.val (.word w')) ∧ w'.toNat ∈ S) := by
  subst hbody
  apply Flw.dec
  intro bv hbv
  obtain ⟨_, rfl⟩ := ev_node_load x nd w 24 hnd hn bv hbv
  apply Flw.seq
  apply Flw.ite
  intro c hc
  constructor
  · intro _
    apply Flw.brk
    refine ⟨fun h => absurd h (by simp), fun _ => ?_⟩
    refine ⟨w, ?_, hw⟩
    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, PanRunBounded.resVarEq_lookup, hn,
      show ofString "n" ≠ ofString "b" by decide, show ofString "b" ≠ ofString "n" by decide]
  · intro hz
    apply Flw.skip
    refine ⟨fun _ => ?_, fun h => absurd rfl h⟩
    have hne : memW x (nd.toNat + 32 * w.toNat + 24) ≠ kb.toNat := by
      obtain ⟨a, b, ha, hb, hcw⟩ := evalAt_cmp _ .equal _ _ c hc
      simp [evalAt, evalHOLExact, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE] at ha
      simp [evalAt, evalHOLExact, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        hkb, show ofString "b" ≠ ofString "keybits" by decide] at hb
      subst hb
      rw [memW_node]
      have ha' : x.memory (nd + w * 32 + BitVec.ofNat 64 24) = .word a := ha
      rw [ha']
      intro heq
      have := BitVec.eq_of_toNat_eq heq
      subst this hz
      simp [Compiler.Encoders.Asm.wordCmpHOL] at hcw
    obtain ⟨h8, h16⟩ := htree hne
    apply Flw.ite
    intro c2 _
    constructor
    · intro _
      apply Flw.assign
      intro v hv
      obtain ⟨_, rfl⟩ := ev_node_load _ nd w 8
        (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hnd, show ofString "b" ≠ ofString "nodes" by decide])
        (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn, show ofString "b" ≠ ofString "n" by decide]) v hv
      rw [memW_node] at h8
      rcases hm : x.memory (nd + w * 32 + 8) with ⟨u⟩
      refine ⟨u, ?_, ?_⟩
      · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          PanRunBounded.resVarEq_lookup, show ofString "n" ≠ ofString "b" by decide]
        exact hm
      · have : x.memory (nd + w * 32 + BitVec.ofNat 64 8) = .word u := hm
        rw [this] at h8; exact h8
    · intro _
      apply Flw.assign
      intro v hv
      obtain ⟨_, rfl⟩ := ev_node_load _ nd w 16
        (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hnd, show ofString "b" ≠ ofString "nodes" by decide])
        (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn, show ofString "b" ≠ ofString "n" by decide]) v hv
      rw [memW_node] at h16
      rcases hm : x.memory (nd + w * 32 + 16) with ⟨u⟩
      refine ⟨u, ?_, ?_⟩
      · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          PanRunBounded.resVarEq_lookup, show ofString "n" ≠ ofString "b" by decide]
        exact hm
      · have : x.memory (nd + w * 32 + BitVec.ofNat 64 16) = .word u := hm
        rw [this] at h16; exact h16

theorem fl_brk {F : Type} (x : PanSemStateFiniteExact 64 F) (nd w kb : BitVec 64)
    (hnd : x.locals.lookup (ofString "nodes") = some (.val (.word nd)))
    (hn : x.locals.lookup (ofString "n") = some (.val (.word w)))
    (hkb : x.locals.lookup (ofString "keybits") = some (.val (.word kb)))
    (body : ProgHOL 64)
    (hbody : body = .dec (ofString "b") .one (.load .one (.op .add [.var .local (ofString "nodes"),
        .panop .mul [.var .local (ofString "n"), .const 32], .const 24]))
      (.seq (.ite (.cmp .equal (.var .local (ofString "b")) (.var .local (ofString "keybits")))
          .break .skip)
        (.ite (.cmp .equal (.op .and [.shift .lsr (.loadByte (.op .add [.var .local (ofString "key"),
            .shift .lsr (.var .local (ofString "b")) (.const 3)])) (.op .sub [.const 7,
            .op .and [.var .local (ofString "b"), .const 7]]), .const 1]) (.const 0))
          (.assign .local (ofString "n") (.load .one (.op .add [.var .local (ofString "nodes"),
            .panop .mul [.var .local (ofString "n"), .const 32], .const 8])))
          (.assign .local (ofString "n") (.load .one (.op .add [.var .local (ofString "nodes"),
            .panop .mul [.var .local (ofString "n"), .const 32], .const 16]))))))
    : Flw x body (fun r t => r = some .break →
        t.locals.lookup (ofString "n") = some (.val (.word w)) ∧
        memW x (nd.toNat + 32 * w.toNat + 24) = kb.toNat) := by
  subst hbody
  apply Flw.dec
  intro bv hbv
  obtain ⟨_, rfl⟩ := ev_node_load x nd w 24 hnd hn bv hbv
  apply Flw.seq
  apply Flw.ite
  intro c hc
  constructor
  · intro hc0
    apply Flw.brk
    refine ⟨fun h => absurd h (by simp), fun _ _ => ⟨?_, ?_⟩⟩
    · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        PanRunBounded.resVarEq_lookup, hn, show ofString "n" ≠ ofString "b" by decide,
        show ofString "b" ≠ ofString "n" by decide]
    · obtain ⟨a, b, ha, hb, hcw⟩ := evalAt_cmp _ .equal _ _ c hc
      simp [evalAt, evalHOLExact, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE] at ha
      simp [evalAt, evalHOLExact, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        hkb, show ofString "b" ≠ ofString "keybits" by decide] at hb
      subst hb
      have hab : a = kb := by
        by_contra hne
        simp [Compiler.Encoders.Asm.wordCmpHOL, hne] at hcw
        exact hc0 hcw
      subst hab
      rw [memW_node]
      have ha' : x.memory (nd + w * 32 + BitVec.ofNat 64 24) = .word a := ha
      rw [ha']
  · intro _
    apply Flw.skip
    refine ⟨fun _ => ?_, fun h => absurd rfl h⟩
    apply Flw.ite
    intro c2 _
    constructor <;> intro _ <;> apply Flw.assign <;> intro v _ <;> intro h <;> cases h

theorem find_leaf_ret2 {F : Type} (E : PanSemStateFiniteExact 64 F)
    (tw : BitVec 64) (ht : E.locals.lookup (ofString "t") = some (.val (.word tw)))
    (S : List Nat)
    (hroot : ∀ u, E.memory (tw + 56) = .word u → u.toNat ∈ S)
    (htree : ∀ nd k : BitVec 64, E.memory (tw + 40) = .word nd → E.memory (tw + 0) = .word k →
      ∀ w : BitVec 64, w.toNat ∈ S → w ≠ 0 →
        memW E (nd.toNat + 32 * w.toNat + 24) ≠ (k * 8).toNat →
        memW E (nd.toNat + 32 * w.toNat + 8) ∈ S ∧ memW E (nd.toNat + 32 * w.toNat + 16) ∈ S) :
    Ret E (sourceFnBody Guest.Software.guestFn_htab_find_leaf)
      (fun v post => ∃ w : BitVec 64, v = .val (.word w) ∧ w.toNat ∈ S ∧ LocFrame E post ∧
        (w ≠ 0 → ∀ nd k : BitVec 64, E.memory (tw + 40) = .word nd → E.memory (tw + 0) = .word k →
          memW E (nd.toNat + 32 * w.toNat + 24) = (k * 8).toNat)) := by
  htab_unfold Guest.Software.guestFn_htab_find_leaf
  apply Ret.dec
  intro kbv hkbv
  rcases hk : E.memory (tw + 0) with ⟨k⟩
  have hk' : E.memory tw = .word k := by simpa using hk
  have hkbv' : kbv = .val (.word (k * 8)) := by
    simp [evalAt, evalHOLExact, evalListHOLExact, ht, valueIsWord, valueWord, wordOpHOL, wordOp,
      memLoadHOLExact, panOpHOL, hk'] at hkbv
    by_cases hm : E.memaddrs tw
    · simp [hm] at hkbv; exact hkbv.symm
    · simp [hm] at hkbv
  subst hkbv'
  apply Ret.dec
  intro ndv hndv
  rcases hnd : E.memory (tw + 40) with ⟨nd⟩
  obtain ⟨_, rfl⟩ := ev_field_load _ (ofString "t") tw 40
    (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht, show ofString "keybits" ≠ ofString "t" by decide]) ndv hndv
  apply Ret.dec
  intro nv hnv
  rcases hrt : E.memory (tw + 56) with ⟨r0⟩
  obtain ⟨_, rfl⟩ := ev_field_load _ (ofString "t") tw 56
    (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht,
      show ofString "nodes" ≠ ofString "t" by decide, show ofString "keybits" ≠ ofString "t" by decide]) nv hnv
  simp only [setVarHOLFinite] at *
  set E3 := { E with locals := ((E.locals.update (ofString "keybits", .val (.word (k * 8)))).update
    (ofString "nodes", .val (E.memory (tw + 40)))).update (ofString "n", .val (E.memory (tw + 56))) }
    with hE3
  apply Ret.seq
  · intro w hw
    exfalso
    revert hw
    apply while_noRet _ _ _ _ _ le_rfl
    exact NoRet.dec' (NoRet.seq (NoRet.ite NoRet.brk NoRet.skip) (NoRet.ite NoRet.assign NoRet.assign))
  · intro u hu
    let J : PanSemStateFiniteExact 64 F → Prop := fun y =>
      LocFrame E y ∧ y.locals.lookup (ofString "nodes") = some (.val (.word nd)) ∧
        y.locals.lookup (ofString "keybits") = some (.val (.word (k * 8))) ∧
        ∃ w : BitVec 64, y.locals.lookup (ofString "n") = some (.val (.word w)) ∧ w.toNat ∈ S
    have hJ3 : J E3 := by
      refine ⟨LocFrame.locals (LocFrame.refl E) _, ?_, ?_, r0, ?_, hroot r0 hrt⟩
      · simp [hE3, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "n" ≠ ofString "nodes" by decide]; exact hnd
      · simp [hE3, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "n" ≠ ofString "keybits" by decide, show ofString "nodes" ≠ ofString "keybits" by decide]
      · simp [hE3, HolFiniteMapExact.lookup_update, FUPDATE]; exact hrt
    let Bk : PanSemStateFiniteExact 64 F → Prop := fun y => J y ∧
      ∃ w : BitVec 64, y.locals.lookup (ofString "n") = some (.val (.word w)) ∧
        memW E (nd.toNat + 32 * w.toNat + 24) = (k * 8).toNat
    have hJu : (J u ∧ CondFalse (.cmp .notEqual (.var .local (ofString "n")) (.const 0)) u) ∨ Bk u := by
      have := while_inv2 J Bk _ _ ?_ E3.clock E3 le_rfl hJ3 (by rw [hu])
      · rw [hu] at this; exact this
      · intro x hx hact _
        obtain ⟨hfr, hxnd, hxkb, w, hxn, hwS⟩ := hx
        have hw0 := active_n_ne x w hxn hact
        have hmem := hfr.memory
        have hm : ∀ a, memW (decClockHOLFinite x) a = memW E a := fun a => by
          simp only [memW, decClockHOLFinite, hmem]
        constructor
        · intro hflow
          have hflow' : FlowR _ := hflow.elim Or.inl (fun h => Or.inr (Or.inl h))
          have hit := fl_iter (decClockHOLFinite x) nd w (k * 8) S hxnd hxn hxkb hwS (by
            intro hne
            simp only [hm] at hne ⊢
            exact htree nd k hnd hk w hwS hw0 hne) _ rfl hflow'
          obtain ⟨w', hw', hw'S⟩ := hit
          refine ⟨hfr.trans (locFrameW_dec _ (by rfl)), ?_, ?_, w', hw', hw'S⟩
          · rw [evaluate_avoidsLocal_flowing _ _ (by simp [avoidsLocal]; decide) _ (flowing_of_flowR hflow')]
            exact hxnd
          · rw [evaluate_avoidsLocal_flowing _ _ (by simp [avoidsLocal]; decide) _ (flowing_of_flowR hflow')]
            exact hxkb
        · intro hbrk
          have hflow' : FlowR _ := Or.inr (Or.inr hbrk)
          have hbk := fl_brk (decClockHOLFinite x) nd w (k * 8) hxnd hxn hxkb _ rfl hflow' hbrk
          obtain ⟨hn', hcrit⟩ := hbk
          refine ⟨⟨hfr.trans (locFrameW_dec _ (by rfl)), ?_, ?_, w, hn', hwS⟩, w, hn', ?_⟩
          · rw [evaluate_avoidsLocal_flowing _ _ (by simp [avoidsLocal]; decide) _ (flowing_of_flowR hflow')]
            exact hxnd
          · rw [evaluate_avoidsLocal_flowing _ _ (by simp [avoidsLocal]; decide) _ (flowing_of_flowR hflow')]
            exact hxkb
          · rw [hm] at hcrit
            exact hcrit
    apply Ret.ret
    intro val hval
    rcases hJu with ⟨⟨hfr, _, _, w, hun, hwS⟩, hcf⟩ | ⟨⟨hfr, _, _, w0, hun0, hwS0⟩, w, hun, hcrit⟩
    · simp [evalAt, evalHOLExact, hun] at hval
      subst hval
      refine ⟨w, rfl, hwS, (hfr.emptyLocals.locals _).locals _ |>.locals _ |>.locals _, ?_⟩
      intro hw0
      exact absurd (condFalse_n_eq_zero u w hun hcf) hw0
    · simp [evalAt, evalHOLExact, hun] at hval
      subst hval
      refine ⟨w, rfl, ?_, (hfr.emptyLocals.locals _).locals _ |>.locals _ |>.locals _, ?_⟩
      · rw [hun0] at hun
        simp at hun
        rw [← hun]; exact hwS0
      · intro _ nd' k' hnd' hk'
        simp only [HolWordLab.word.injEq] at hnd' hk'
        subst hnd' hk'
        exact hcrit

/-- Corollary of `find_leaf_ret2` specialized to a well-formed table `HtabWF E tw.toNat`:
- If `cnt = 0`, returns `w = 0`.
- If `0 < cnt`, returns `w` with `w.toNat ∈ L` (a live leaf!).
Wait: can `htab_find_leaf` return `0` when `0 < cnt`?
In `HtabWF`: `0 < cnt → root ∈ L ++ I`, and every `n ∈ L ++ I` has `1 ≤ n < next` so `n ≠ 0`!
And every `n ∈ I` has `nd n 8 ∈ L ++ I` and `nd n 16 ∈ L ++ I`, which are also `≥ 1` so `≠ 0`!
Thus when `0 < cnt`, `S = L ++ I` (WITHOUT `0`!) is closed under root and children!
Wait — THAT'S HUGE!!
Let's check! When `0 < cnt`, `root ∈ L ++ I`. Every `n ∈ L ++ I` satisfies `1 ≤ n`, so `w ≠ 0`!
Wait: what if `w.toNat ∈ L ++ I` and `w` is a 64-bit word with `w.toNat ≥ 1`? Then `w ≠ 0`!
So the loop NEVER exits via `n == 0` when `0 < cnt` — it ONLY exits via `break` when `b == keybits`,
and since every `n ∈ I` has `nd n 24 < 8 * klen = (k * 8).toNat`, `w.toNat` CANNOT be in `I`, so `w.toNat ∈ L`!
WAIT A SECOND! Is `htab_find_leaf` guaranteed to return `w = 0` iff `cnt = 0`?!
Let's verify!!
1. Suppose `cnt = 0`. By `HtabWF`, `cnt = 0 → root = 0`. And `r0.toNat = hdr E tw 7 = root = 0`, so `r0 = 0`!
   Take `S = [0]`: `r0.toNat = 0 ∈ [0]`, and `htree` has hypothesis `w.toNat ∈ [0]` and `w ≠ 0`, which is vacuously false!
   So `find_leaf_ret2` with `S = [0]` gives `w.toNat ∈ [0]`, hence `w = 0`!
2. Suppose `0 < cnt`. Take `S = L ++ I`!
   - `hroot`: `u.toNat = hdr E tw 7 = root ∈ L ++ I = S`!
   - `htree`: if `w.toNat ∈ L ++ I` and `nd w 24 ≠ 8 * klen`, then `w.toNat ∉ L` (since leaves have `nd _ 24 = 8 * klen`), so `w.toNat ∈ I`, hence `nd w 8 ∈ L ++ I` and `nd w 16 ∈ L ++ I`!
   - Then `find_leaf_ret2` gives `w.toNat ∈ L ++ I`!
   - Since `∀ x ∈ L ++ I, 1 ≤ x`, we have `1 ≤ w.toNat`, so `w ≠ 0`!
   - Therefore `hcrit` fires: `nd w.toNat 24 = 8 * klen`!
   - Since `∀ x ∈ I, nd x 24 < 8 * klen`, `w.toNat ∉ I`, so `w.toNat ∈ L`!!
MIND BLOWN!! That simultaneously proves:
- In branch `leaf == 0` of `htab_set`: `cnt = 0` (table is empty! `L = []`, `I = []`, `root = 0`)!
- In branch `leaf != 0` of `htab_set`: `0 < cnt` AND `leaf.toNat ∈ L` (so `1 ≤ leaf.toNat < next ≤ ncap + 1`, and in overwrite or `memeq` / `htab_first_diff`, `keys + leaf * stride` is in-bounds of `keys`, and `nodes + leaf * 32 + 8` is a leaf's `+8` field)! -/
theorem find_leaf_spec_wf {F : Type} (E : PanSemStateFiniteExact 64 F)
    (tw : BitVec 64) (ht : E.locals.lookup (ofString "t") = some (.val (.word tw)))
    (hW : HtabWF E tw.toNat) :
    Ret E (sourceFnBody Guest.Software.guestFn_htab_find_leaf)
      (fun v post => ∃ w : BitVec 64, v = .val (.word w) ∧ LocFrame E post ∧
        ((w = 0 ∧ hdr E tw.toNat 3 = 0) ∨
         (w ≠ 0 ∧ 0 < hdr E tw.toNat 3 ∧
          ∀ L I Fr, TreeWF L I Fr (hdr E tw.toNat 8) (hdr E tw.toNat 0) (hdr E tw.toNat 3)
            (hdr E tw.toNat 7) (hdr E tw.toNat 9) (nodeF E (hdr E tw.toNat 5))
            (fun i => memW E (hdr E tw.toNat 6 + 8 * i)) → w.toNat ∈ L))) := by
  have ⟨hB, L0, I0, Fr0, hT0⟩ := (htabWF_iff E tw.toNat).mp hW
  obtain ⟨_, hk_mem⟩ := word_of_hdr E tw 0 (by omega) hB
  obtain ⟨_, hnd_mem⟩ := word_of_hdr E tw 5 (by omega) hB
  obtain ⟨_, hrt_mem⟩ := word_of_hdr E tw 7 (by omega) hB
  have hk0 : tw + BitVec.ofNat 64 (8 * 0) = tw + 0 := rfl
  have hnd40 : tw + BitVec.ofNat 64 (8 * 5) = tw + 40 := rfl
  have hrt56 : tw + BitVec.ofNat 64 (8 * 7) = tw + 56 := rfl
  rw [hk0] at hk_mem; rw [hnd40] at hnd_mem; rw [hrt56] at hrt_mem
  have hk_lt : hdr E tw.toNat 0 ≤ 60 := hB.2.2.2.1
  by_cases hcnt0 : hdr E tw.toNat 3 = 0
  · have hr0 : hdr E tw.toNat 7 = 0 := hT0.2.2.2.2.2.2.1 hcnt0
    intro v hv
    obtain ⟨w, rfl, hwS, hfr, _⟩ := find_leaf_ret2 E tw ht [0]
      (fun u hu => by
        rw [hrt_mem, hr0] at hu
        injection hu with hu'; subst hu'; simp)
      (fun _ _ _ _ w hwS hw0 _ => by
        simp at hwS
        exact absurd (BitVec.eq_of_toNat_eq (by simpa using hwS)) hw0)
      v hv
    simp at hwS
    exact ⟨w, rfl, hfr, Or.inl ⟨BitVec.eq_of_toNat_eq (by simpa using hwS), hcnt0⟩⟩
  · have hcnt_pos : 0 < hdr E tw.toNat 3 := by omega
    intro v hv
    obtain ⟨w, rfl, hwS, hfr, hcrit⟩ := find_leaf_ret2 E tw ht (L0 ++ I0)
      (fun u hu => by
        rw [hrt_mem] at hu; injection hu with hu'; subst hu'
        have hr_lt : hdr E tw.toNat 7 < 2 ^ 64 := by
          have hmem := (hT0.2.2.1 _).mp (List.mem_append_left _ (hT0.2.2.2.2.2.2.2.1 hcnt_pos).1)
          have hnodes_in := (hB.1 (hdr E tw.toNat 5, (hdr E tw.toNat 10 + 1) * 32) (by simp [htabFootprint])).1
          have hhe : heapEnd < 2 ^ 64 := by decide
          have hnx := hB.2.2.2.2.2.2.2
          unfold Inside at hnodes_in
          omega
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr_lt]
        exact (hT0.2.2.2.2.2.2.2.1 hcnt_pos).1)
      (fun nd' k' hnd' hk' w hwS hw0 hne => by
        rw [hnd_mem] at hnd'; rw [hk_mem] at hk'
        injection hnd' with hnd_eq; injection hk' with hk_eq
        subst hnd_eq hk_eq
        have hnd_lt : hdr E tw.toNat 5 < 2 ^ 64 := by
          have hnodes_in := (hB.1 (hdr E tw.toNat 5, (hdr E tw.toNat 10 + 1) * 32) (by simp [htabFootprint])).1
          have hhe : heapEnd < 2 ^ 64 := by decide
          unfold Inside at hnodes_in; omega
        have hnd_nat : (BitVec.ofNat 64 (hdr E tw.toNat 5)).toNat = hdr E tw.toNat 5 := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnd_lt]
        have hk8_nat : (BitVec.ofNat 64 (hdr E tw.toNat 0) * 8).toNat = 8 * hdr E tw.toNat 0 := by
          rw [BitVec.toNat_mul, BitVec.toNat_ofNat, show (8 : BitVec 64).toNat = 8 from rfl]
          omega
        rw [hnd_nat] at hne ⊢
        rw [hk8_nat] at hne
        rcases List.mem_append.mp hwS with hwL | hwI
        · exfalso
          obtain ⟨i, hi, hiw⟩ := List.getElem_of_mem hwL
          have hc := (hT0.2.2.2.2.1 i hi).2.1
          rw [hiw] at hc
          exact hne hc
        · obtain ⟨_, h8, h16, _⟩ := hT0.2.2.2.2.2.1 _ hwI
          exact ⟨h8, h16⟩)
      v hv
    have hw_ge1 : 1 ≤ w.toNat := ((hT0.2.2.1 w.toNat).mp (List.mem_append_left _ hwS)).1
    have hw_nz : w ≠ 0 := by
      intro h0; subst h0; simp at hw_ge1
    have hc := hcrit hw_nz _ _ hnd_mem hk_mem
    have hnd_lt : hdr E tw.toNat 5 < 2 ^ 64 := by
      have hnodes_in := (hB.1 (hdr E tw.toNat 5, (hdr E tw.toNat 10 + 1) * 32) (by simp [htabFootprint])).1
      have hhe : heapEnd < 2 ^ 64 := by decide
      unfold Inside at hnodes_in; omega
    have hnd_nat : (BitVec.ofNat 64 (hdr E tw.toNat 5)).toNat = hdr E tw.toNat 5 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnd_lt]
    have hk8_nat : (BitVec.ofNat 64 (hdr E tw.toNat 0) * 8).toNat = 8 * hdr E tw.toNat 0 := by
      rw [BitVec.toNat_mul, BitVec.toNat_ofNat, show (8 : BitVec 64).toNat = 8 from rfl]
      omega
    rw [hnd_nat, hk8_nat] at hc
    refine ⟨w, rfl, hfr, Or.inr ⟨hw_nz, hcnt_pos, ?_⟩⟩
    intro L I Fr hT
    have hw_lt : w.toNat < hdr E tw.toNat 8 := ((hT0.2.2.1 w.toNat).mp (List.mem_append_left _ hwS)).2
    have hw_mem : w.toNat ∈ L ++ I ++ Fr := (hT.2.2.1 w.toNat).mpr ⟨hw_ge1, hw_lt⟩
    -- Wait: can `w.toNat` be in `Fr` for another decomposition `(L, I, Fr)`?
    -- Wait: `L` is uniquely determined by `order[0..cnt)`! Every `L[i] = ord i`!
    -- Even simpler: let's also check `L = L0` because `L.length = cnt = L0.length` and `L[i] = ord i = L0[i]`!
    have hLw0 : w.toNat ∈ L0 := by
      rcases List.mem_append.mp hwS with hwL | hwI
      · exact hwL
      · exfalso
        have hlt := (hT0.2.2.2.2.2.1 _ hwI).1
        unfold nodeF at hlt
        omega
    obtain ⟨i, hi, hiw⟩ := List.getElem_of_mem hLw0
    have hlen_eq : L.length = L0.length := hT.1.trans hT0.1.symm
    have hiL : i < L.length := by omega
    have hord_i0 := (hT0.2.2.2.2.1 i hi).1
    have hord_i := (hT.2.2.2.2.1 i hiL).1
    have heq_elem : L[i] = w.toNat := by omega
    rw [← heq_elem]
    exact List.getElem_mem hiL

/-! ### `htab_set` descent loop invariant -/

/-- One iteration of `htab_set`'s `while (n != 0)` loop:
```
dec b := load(nodes + n * 32 + 24);
if (b >= d) break;
p := n;
if (((loadByte(key + (b >>> 3)) >>> (7 - (b & 7))) & 1) == 0)
  n := load(nodes + n * 32 + 8)
else
  n := load(nodes + n * 32 + 16)
```
When `0 < cnt`, `n` starts at `root ∈ L ++ I` and `p` starts at `0`, so the pair `(p, n)` satisfies:
`n.toNat ∈ L ++ I ∧ ((p = 0 ∧ n.toNat = root) ∨ (p.toNat ∈ I ∧ n.toNat ≠ root ∧ p.toNat = nodeF E nodes n.toNat 0))`.
And because `d < 8 * klen`:
- If `b < d`, then `b < 8 * klen`, so `n.toNat ∉ L` (since leaves have `b = 8 * klen`), hence `n.toNat ∈ I`!
  Then `p' := n` has `p'.toNat ∈ I`, and `n'` is either `nd n 8` or `nd n 16`, both of which are in `L ++ I`,
  satisfy `n' ≠ root` (by `hrc`), and satisfy `nd n' 0 = n.toNat = p'.toNat` (by `hint`)!
- And `n'` always satisfies `1 ≤ n'.toNat` so `n' ≠ 0`, meaning the `CondFalse` (`n == 0`) exit is impossible! -/
theorem set_descent_iter {F : Type} (x : PanSemStateFiniteExact 64 F)
    (nd dw pw nw : BitVec 64) (L I : List Nat) (klen root : Nat)
    (hnd : x.locals.lookup (ofString "nodes") = some (.val (.word nd)))
    (hd_loc : x.locals.lookup (ofString "d") = some (.val (.word dw)))
    (hp_loc : x.locals.lookup (ofString "p") = some (.val (.word pw)))
    (hn_loc : x.locals.lookup (ofString "n") = some (.val (.word nw)))
    (hd_lt : dw.toNat < 8 * klen)
    (hn_LI : nw.toNat ∈ L ++ I)
    (hleaves : ∀ z ∈ L, nodeF x nd.toNat z 24 = 8 * klen)
    (hint : ∀ z ∈ I, nodeF x nd.toNat z 24 < 8 * klen ∧
      nodeF x nd.toNat z 8 ∈ L ++ I ∧ nodeF x nd.toNat z 16 ∈ L ++ I ∧
      nodeF x nd.toNat z 8 ≠ root ∧ nodeF x nd.toNat z 16 ≠ root ∧
      nodeF x nd.toNat (nodeF x nd.toNat z 8) 0 = z ∧
      nodeF x nd.toNat (nodeF x nd.toNat z 16) 0 = z)
    (body : ProgHOL 64)
    (hbody : body = .dec (ofString "b") .one (.load .one (.op .add [.var .local (ofString "nodes"),
        .panop .mul [.var .local (ofString "n"), .const 32], .const 24]))
      (.seq (.ite (.cmp .notLower (.var .local (ofString "b")) (.var .local (ofString "d")))
          .break .skip)
        (.seq (.assign .local (ofString "p") (.var .local (ofString "n")))
          (.ite (.cmp .equal (.op .and [.shift .lsr (.loadByte (.op .add [.var .local (ofString "key"),
              .shift .lsr (.var .local (ofString "b")) (.const 3)])) (.op .sub [.const 7,
              .op .and [.var .local (ofString "b"), .const 7]]), .const 1]) (.const 0))
            (.assign .local (ofString "n") (.load .one (.op .add [.var .local (ofString "nodes"),
              .panop .mul [.var .local (ofString "n"), .const 32], .const 8])))
            (.assign .local (ofString "n") (.load .one (.op .add [.var .local (ofString "nodes"),
              .panop .mul [.var .local (ofString "n"), .const 32], .const 16]))))))) :
    Flw x body (fun r t =>
      (r = some .break →
        t.locals.lookup (ofString "p") = some (.val (.word pw)) ∧
        t.locals.lookup (ofString "n") = some (.val (.word nw))) ∧
      (r ≠ some .break →
        ∃ nw' : BitVec 64,
          t.locals.lookup (ofString "p") = some (.val (.word nw)) ∧
          t.locals.lookup (ofString "n") = some (.val (.word nw')) ∧
          nw'.toNat ∈ L ++ I ∧ nw.toNat ∈ I ∧ nw'.toNat ≠ root ∧
          nw.toNat = nodeF x nd.toNat nw'.toNat 0)) := by
  subst hbody
  apply Flw.dec
  intro bv hbv
  obtain ⟨_, rfl⟩ := ev_node_load x nd nw 24 hnd hn_loc bv hbv
  apply Flw.seq
  apply Flw.ite
  intro c hc
  constructor
  · intro _
    apply Flw.brk
    refine ⟨fun h => absurd h (by simp), fun _ => ⟨fun _ => ⟨?_, ?_⟩, fun h => absurd rfl h⟩⟩
    · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        PanRunBounded.resVarEq_lookup, hp_loc,
        show ofString "p" ≠ ofString "b" by decide, show ofString "b" ≠ ofString "p" by decide]
    · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        PanRunBounded.resVarEq_lookup, hn_loc,
        show ofString "n" ≠ ofString "b" by decide, show ofString "b" ≠ ofString "n" by decide]
  · intro hz
    apply Flw.skip
    refine ⟨fun _ => ?_, fun h => absurd rfl h⟩
    have hlt_d : nodeF x nd.toNat nw.toNat 24 < dw.toNat := by
      obtain ⟨a, b, ha, hb, hcw⟩ := evalAt_cmp _ .notLower _ _ c hc
      simp [evalAt, evalHOLExact, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE] at ha
      simp [evalAt, evalHOLExact, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        hd_loc, show ofString "b" ≠ ofString "d" by decide] at hb
      subst hb
      unfold nodeF
      rw [memW_node]
      have ha' : x.memory (nd + nw * 32 + BitVec.ofNat 64 24) = .word a := ha
      rw [ha']
      dsimp only
      by_contra hge
      have hle_bv : dw ≤ a := by rw [BitVec.le_def]; omega
      simp [Compiler.Encoders.Asm.wordCmpHOL, hle_bv] at hcw
      exact absurd hcw (by rw [hz]; decide)
    have hnw_I : nw.toNat ∈ I := by
      rcases List.mem_append.mp hn_LI with hL | hI
      · exfalso; have := hleaves _ hL; omega
      · exact hI
    obtain ⟨_, h8_LI, h16_LI, h8_nr, h16_nr, h8_p, h16_p⟩ := hint _ hnw_I
    apply Flw.seq
    apply Flw.assign
    intro pv hpv
    have hpv_eq : pv = .val (.word nw) := by
      simp [evalAt, evalHOLExact, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        hn_loc, show ofString "b" ≠ ofString "n" by decide] at hpv
      exact hpv.symm
    subst hpv_eq
    refine ⟨fun _ => ?_, fun h => absurd rfl h⟩
    apply Flw.ite
    intro c2 _
    constructor
    · intro _
      apply Flw.assign
      intro v8 hv8
      obtain ⟨_, rfl⟩ := ev_node_load _ nd nw 8
        (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hnd,
          show ofString "p" ≠ ofString "nodes" by decide, show ofString "b" ≠ ofString "nodes" by decide])
        (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn_loc,
          show ofString "p" ≠ ofString "n" by decide, show ofString "b" ≠ ofString "n" by decide]) v8 hv8
      cases hm8 : x.memory (nd + nw * 32 + 8) with
      | word u8 =>
        have hu8_eq : nodeF x nd.toNat nw.toNat 8 = u8.toNat := by
          unfold nodeF; rw [memW_node]
          have hm8' : x.memory (nd + nw * 32 + BitVec.ofNat 64 8) = .word u8 := hm8
          rw [hm8']
        constructor
        · intro h; cases h
        · intro _
          refine ⟨u8, ?_, ?_, ?_, hnw_I, ?_, ?_⟩
          · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              PanRunBounded.resVarEq_lookup,
              show ofString "p" ≠ ofString "b" by decide, show ofString "b" ≠ ofString "p" by decide,
              show ofString "n" ≠ ofString "p" by decide]
          · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              PanRunBounded.resVarEq_lookup, show ofString "n" ≠ ofString "b" by decide,
              show ofString "b" ≠ ofString "n" by decide]
            exact hm8
          · rw [← hu8_eq]; exact h8_LI
          · rw [← hu8_eq]; exact h8_nr
          · rw [← hu8_eq]; exact h8_p.symm
    · intro _
      apply Flw.assign
      intro v16 hv16
      obtain ⟨_, rfl⟩ := ev_node_load _ nd nw 16
        (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hnd,
          show ofString "p" ≠ ofString "nodes" by decide, show ofString "b" ≠ ofString "nodes" by decide])
        (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn_loc,
          show ofString "p" ≠ ofString "n" by decide, show ofString "b" ≠ ofString "n" by decide]) v16 hv16
      cases hm16 : x.memory (nd + nw * 32 + 16) with
      | word u16 =>
        have hu16_eq : nodeF x nd.toNat nw.toNat 16 = u16.toNat := by
          unfold nodeF; rw [memW_node]
          have hm16' : x.memory (nd + nw * 32 + BitVec.ofNat 64 16) = .word u16 := hm16
          rw [hm16']
        constructor
        · intro h; cases h
        · intro _
          refine ⟨u16, ?_, ?_, ?_, hnw_I, ?_, ?_⟩
          · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              PanRunBounded.resVarEq_lookup,
              show ofString "p" ≠ ofString "b" by decide, show ofString "b" ≠ ofString "p" by decide,
              show ofString "n" ≠ ofString "p" by decide]
          · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              PanRunBounded.resVarEq_lookup, show ofString "n" ≠ ofString "b" by decide,
              show ofString "b" ≠ ofString "n" by decide]
            exact hm16
          · rw [← hu16_eq]; exact h16_LI
          · rw [← hu16_eq]; exact h16_nr
          · rw [← hu16_eq]; exact h16_p.symm

/-- Full `while (n != 0)` descent loop of `htab_set`: preserves `LocFrame`, avoids all locals
except `p` and `n`, and exits with `n.toNat ∈ L ++ I` and `(p = 0 ∧ n = root) ∨ (p ∈ I ∧ n ≠ root ∧ p = nd n 0)`. -/
theorem set_descent_loop {F : Type} (s0 u : PanSemStateFiniteExact 64 F)
    (nd dw rw0 : BitVec 64) (L I Fr : List Nat) (next klen cnt root free : Nat)
    (ord : Nat → Nat)
    (hcnt_pos : 0 < cnt)
    (hd_lt : dw.toNat < 8 * klen)
    (hnext_lt : next ≤ 2 ^ 64)
    (hrw0 : rw0.toNat = root)
    (hT : TreeWF L I Fr next klen cnt root free (nodeF s0 nd.toNat) ord)
    (hnd_s0 : s0.locals.lookup (ofString "nodes") = some (.val (.word nd)))
    (hd_s0 : s0.locals.lookup (ofString "d") = some (.val (.word dw)))
    (hp_s0 : s0.locals.lookup (ofString "p") = some (.val (.word 0#64)))
    (hn_s0 : s0.locals.lookup (ofString "n") = some (.val (.word rw0)))
    (body : ProgHOL 64)
    (hbody : body = .dec (ofString "b") .one (.load .one (.op .add [.var .local (ofString "nodes"),
        .panop .mul [.var .local (ofString "n"), .const 32], .const 24]))
      (.seq (.ite (.cmp .notLower (.var .local (ofString "b")) (.var .local (ofString "d")))
          .break .skip)
        (.seq (.assign .local (ofString "p") (.var .local (ofString "n")))
          (.ite (.cmp .equal (.op .and [.shift .lsr (.loadByte (.op .add [.var .local (ofString "key"),
              .shift .lsr (.var .local (ofString "b")) (.const 3)])) (.op .sub [.const 7,
              .op .and [.var .local (ofString "b"), .const 7]]), .const 1]) (.const 0))
            (.assign .local (ofString "n") (.load .one (.op .add [.var .local (ofString "nodes"),
              .panop .mul [.var .local (ofString "n"), .const 32], .const 8])))
            (.assign .local (ofString "n") (.load .one (.op .add [.var .local (ofString "nodes"),
              .panop .mul [.var .local (ofString "n"), .const 32], .const 16])))))))
    (hu : evaluateHOLFiniteState s0 (.while (.cmp .notEqual (.var .local (ofString "n")) (.const 0)) body) = (none, u)) :
    LocFrame s0 u ∧
    (∀ k : MlS, k ≠ ofString "p" → k ≠ ofString "n" → u.locals.lookup k = s0.locals.lookup k) ∧
    ∃ pw nw : BitVec 64,
      u.locals.lookup (ofString "p") = some (.val (.word pw)) ∧
      u.locals.lookup (ofString "n") = some (.val (.word nw)) ∧
      nw.toNat ∈ L ++ I ∧
      ((pw.toNat = 0 ∧ nw.toNat = root) ∨
       (pw.toNat ∈ I ∧ nw.toNat ≠ root ∧ pw.toNat = nodeF s0 nd.toNat nw.toNat 0)) := by
  have hloc_keep : ∀ k : MlS, k ≠ ofString "p" → k ≠ ofString "n" → u.locals.lookup k = s0.locals.lookup k := by
    intro k hkp hkn
    have hav : avoidsLocal k (.while (.cmp .notEqual (.var .local (ofString "n")) (.const 0)) body) = true := by
      subst hbody
      by_cases hkb : ofString "b" = k
      · simp [avoidsLocal, hkb]
      · simp [avoidsLocal, hkb, Ne.symm hkp, Ne.symm hkn]
    have hfl : Flowing (evaluateHOLFiniteState s0 (.while (.cmp .notEqual (.var .local (ofString "n")) (.const 0)) body)).1 := by
      rw [hu]; exact Or.inl rfl
    have heq := evaluate_avoidsLocal_flowing k _ hav s0 hfl
    rw [hu] at heq
    exact heq
  obtain ⟨hLlen, _, hmem, _, hord_spec, hint_spec, _, hr1, hrc, _, _, _⟩ := hT
  have hleaves : ∀ z ∈ L, nodeF s0 nd.toNat z 24 = 8 * klen := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hz
    exact (hord_spec i hi).2.1
  have hint_all : ∀ z ∈ I, nodeF s0 nd.toNat z 24 < 8 * klen ∧
      nodeF s0 nd.toNat z 8 ∈ L ++ I ∧ nodeF s0 nd.toNat z 16 ∈ L ++ I ∧
      nodeF s0 nd.toNat z 8 ≠ root ∧ nodeF s0 nd.toNat z 16 ≠ root ∧
      nodeF s0 nd.toNat (nodeF s0 nd.toNat z 8) 0 = z ∧
      nodeF s0 nd.toNat (nodeF s0 nd.toNat z 16) 0 = z := by
    intro z hz
    obtain ⟨a1, a2, a3, _, a5, a6⟩ := hint_spec z hz
    obtain ⟨b1, b2⟩ := hrc z hz
    exact ⟨a1, a2, a3, b1, b2, a5, a6⟩
  have hbound_LI : ∀ z ∈ L ++ I, z < 2 ^ 64 := by
    intro z hz
    have := (hmem z).mp (List.mem_append_left _ hz)
    omega
  let J : PanSemStateFiniteExact 64 F → Prop := fun y =>
    LocFrame s0 y ∧
    y.locals.lookup (ofString "nodes") = some (.val (.word nd)) ∧
    y.locals.lookup (ofString "d") = some (.val (.word dw)) ∧
    ∃ pw nw : BitVec 64,
      y.locals.lookup (ofString "p") = some (.val (.word pw)) ∧
      y.locals.lookup (ofString "n") = some (.val (.word nw)) ∧
      nw.toNat ∈ L ++ I ∧
      ((pw.toNat = 0 ∧ nw.toNat = root) ∨
       (pw.toNat ∈ I ∧ nw.toNat ≠ root ∧ pw.toNat = nodeF s0 nd.toNat nw.toNat 0))
  have hJ0 : J s0 := by
    refine ⟨LocFrame.refl s0, hnd_s0, hd_s0, 0#64, rw0, hp_s0, hn_s0, ?_, Or.inl ⟨rfl, hrw0⟩⟩
    rw [hrw0]; exact (hr1 hcnt_pos).1
  have hJu : (J u ∧ CondFalse (.cmp .notEqual (.var .local (ofString "n")) (.const 0)) u) ∨ J u := by
    have := while_inv2 J J _ _ ?_ s0.clock s0 le_rfl hJ0 (by rw [hu])
    · rw [hu] at this; exact this
    · intro x hx hact _
      obtain ⟨hfr, hxnd, hxd, pw, nw, hxp, hxn, hnw_LI, hrel_pn⟩ := hx
      have hmem_eq := hfr.memory
      have hnodeF_eq : ∀ z off, nodeF (decClockHOLFinite x) nd.toNat z off = nodeF s0 nd.toNat z off := by
        intro z off; simp [nodeF, memW, decClockHOLFinite, hmem_eq]
      have hloc_body : locOnlyW body = true := by subst hbody; rfl
      have hav_nd : avoidsLocal (ofString "nodes") body = true := by subst hbody; decide
      have hav_d : avoidsLocal (ofString "d") body = true := by subst hbody; decide
      constructor
      · intro hflow
        have hflow' : FlowR _ := hflow.elim Or.inl (fun h => Or.inr (Or.inl h))
        have hit := set_descent_iter (decClockHOLFinite x) nd dw pw nw L I klen root
          hxnd hxd hxp hxn hd_lt hnw_LI
          (fun z hz => by rw [hnodeF_eq]; exact hleaves z hz)
          (fun z hz => by simp only [hnodeF_eq]; exact hint_all z hz)
          body hbody hflow'
        have hnot_brk : (evaluateHOLFiniteState (decClockHOLFinite x) body).1 ≠ some .break := by
          rcases hflow with h | h <;> rw [h] <;> simp
        obtain ⟨nw', hp', hn', hnw'_LI, hnw_I, hnw'_nr, hpar_eq⟩ := hit.2 hnot_brk
        rw [hnodeF_eq] at hpar_eq
        refine ⟨hfr.trans (locFrameW_dec body hloc_body), ?_, ?_, nw, nw', hp', hn', hnw'_LI,
          Or.inr ⟨hnw_I, hnw'_nr, hpar_eq⟩⟩
        · rw [evaluate_avoidsLocal_flowing _ _ hav_nd _ (flowing_of_flowR hflow')]; exact hxnd
        · rw [evaluate_avoidsLocal_flowing _ _ hav_d _ (flowing_of_flowR hflow')]; exact hxd
      · intro hbrk
        have hflow' : FlowR _ := Or.inr (Or.inr hbrk)
        have hit := set_descent_iter (decClockHOLFinite x) nd dw pw nw L I klen root
          hxnd hxd hxp hxn hd_lt hnw_LI
          (fun z hz => by rw [hnodeF_eq]; exact hleaves z hz)
          (fun z hz => by simp only [hnodeF_eq]; exact hint_all z hz)
          body hbody hflow'
        obtain ⟨hp', hn'⟩ := hit.1 hbrk
        refine ⟨hfr.trans (locFrameW_dec body hloc_body), ?_, ?_, pw, nw, hp', hn', hnw_LI, hrel_pn⟩
        · rw [evaluate_avoidsLocal_flowing _ _ hav_nd _ (flowing_of_flowR hflow')]; exact hxnd
        · rw [evaluate_avoidsLocal_flowing _ _ hav_d _ (flowing_of_flowR hflow')]; exact hxd
  have hJu' : J u := hJu.elim And.left id
  obtain ⟨hfr, _, _, pw, nw, hup, hun, hnw_LI, hrel_pn⟩ := hJu'
  exact ⟨hfr, hloc_keep, pw, nw, hup, hun, hnw_LI, hrel_pn⟩

end InitECandidate.Solver.Wave8GuestInv.SoloHtabSet
