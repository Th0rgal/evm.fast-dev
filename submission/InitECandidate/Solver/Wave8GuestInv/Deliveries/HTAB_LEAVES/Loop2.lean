import InitECandidate.Solver.Wave8GuestInv.Deliveries.HTAB_LEAVES.Loop

/-! Read-only loops carrying two words `x`, `y`, where every continuing iteration runs
`y = x` (the `htab_set` descent: `p = n; n = child(n)`). The assignment succeeds only if `y`
already holds a word (Pancake keeps the shape of a local), so the two words determine every
earlier loop head up to the clock and a non-`.timeOut` run makes at most `2^128` iterations. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace InitECandidate.Solver.Wave8GuestInv.Htab

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

/-- Bodies that, on every normal or `continue` completion, have run `y = x` with `x` unchanged
before and `y` unchanged after. -/
inductive CopiesTo (y x : MlS) : ProgHOL 64 → Prop
  | here : CopiesTo y x (.assign .local y (.var .local x))
  | seqL (first : ProgHOL 64) {rest : ProgHOL 64}
      (ax : avoidsLocal x first = true) (ay : avoidsLocal y first = true)
      (noCont : noTopContinue first = true) (h : CopiesTo y x rest) :
      CopiesTo y x (.seq first rest)
  | seqR {first : ProgHOL 64} (second : ProgHOL 64) (h : CopiesTo y x first)
      (ay : avoidsLocal y second = true) : CopiesTo y x (.seq first second)
  | dec (name : MlS) (shape : ShapeHOL) (init : ExpHOL 64) {body : ProgHOL 64}
      (dy : y ≠ name) (dx : x ≠ name) (h : CopiesTo y x body) :
      CopiesTo y x (.dec name shape init body)

theorem word_of_shape_one (v : ValueHOL 64) (h : shapeOfHOLExact v = .one) :
    ∃ w, v = .val (.word w) := by
  cases v with
  | val l => cases l with | word w => exact ⟨w, rfl⟩
  | rStruct fs => simp [shapeOfHOLExact] at h
  | nStruct n fs => simp [shapeOfHOLExact] at h

theorem CopiesTo.run {y x : MlS} {body : ProgHOL 64} (hb : CopiesTo y x body) :
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (wx : BitVec 64),
      s.locals.lookup x = some (.val (.word wx)) →
      ((evaluateHOLFiniteState s body).1 = none ∨
        (evaluateHOLFiniteState s body).1 = some .continue) →
      (∃ w, s.locals.lookup y = some (.val (.word w))) ∧
        (evaluateHOLFiniteState s body).2.locals.lookup y = some (.val (.word wx)) := by
  induction hb with
  | here =>
    intro F s wx hx hflow
    rw [evaluateHOLFiniteState_assign] at hflow ⊢
    have hev : @evalHOLExact 64 F _ s.toExact
        (fun address => Classical.propDecidable (s.memaddrs address)) (.var .local x) =
        some (.val (.word wx)) := by simpa [evalHOLExact] using hx
    simp only [hev] at hflow ⊢
    by_cases hv : isValidValueHOLFinite s .local y (.val (.word wx)) = true
    · simp only [hv, ↓reduceIte] at hflow ⊢
      refine ⟨?_, by simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update,
        FUPDATE]⟩
      simp only [isValidValueHOLFinite, lookupKvarHOLFinite] at hv
      split at hv
      · rename_i existing hex
        have hsh : shapeOfHOLExact existing = .one := by
          revert hv
          simp only [shapeOfHOLExact]
          cases hs : shapeOfHOLExact existing <;> simp [shapeEqHOL]
        obtain ⟨w, rfl⟩ := word_of_shape_one existing hsh
        exact ⟨w, by simpa using hex⟩
      · cases hv
    · simp only [hv, Bool.false_eq_true, ↓reduceIte] at hflow
      rcases hflow with h | h <;> cases h
  | seqL first ax ay noCont rest ih =>
    intro F s wx hx hflow
    have fx := evaluate_avoidsLocal_flowing x first ax s
    have fy := evaluate_avoidsLocal_flowing y first ay s
    have noContinue := evaluate_noTopContinue first noCont s
    rw [evaluateHOLFiniteState_seq_line780] at hflow ⊢
    cases firstRun : evaluateHOLFiniteState s first with
    | mk result middle =>
      rw [firstRun] at fx fy noContinue hflow
      dsimp only at fx fy noContinue hflow ⊢
      cases result with
      | none =>
        dsimp only at hflow ⊢
        have hx' := (fx (Or.inl rfl)).trans hx
        obtain ⟨⟨w, hw⟩, hpost⟩ := ih middle wx hx' hflow
        exact ⟨⟨w, (fy (Or.inl rfl)).symm.trans hw⟩, hpost⟩
      | some r =>
        dsimp only at hflow
        rcases hflow with h | h
        · cases h
        · exact absurd h noContinue
  | seqR second h ay ih =>
    rename_i first
    intro F s wx hx hflow
    rw [evaluateHOLFiniteState_seq_line780] at hflow ⊢
    cases firstRun : evaluateHOLFiniteState s first with
    | mk result middle =>
      have ih' := ih s wx hx
      rw [firstRun] at ih' hflow
      dsimp only at ih' hflow ⊢
      cases result with
      | none =>
        dsimp only at hflow ⊢
        obtain ⟨hy0, hmid⟩ := ih' (Or.inl rfl)
        have fy := evaluate_avoidsLocal_flowing y second ay middle
          (by rcases hflow with h | h <;> simp [Flowing, h])
        exact ⟨hy0, fy.trans hmid⟩
      | some r =>
        dsimp only at hflow ⊢
        rcases hflow with h | h
        · cases h
        · exact ih' (Or.inr h)
  | dec name shape init dy dx h ih =>
    intro F s wx hx hflow
    rcases hrun : evaluateHOLFiniteState s (.dec name shape init _) with ⟨r, post⟩
    rw [hrun] at hflow
    dsimp only at hflow ⊢
    obtain ⟨value, inner, hin, hpost⟩ :=
      dec_flowing (by rcases hflow with h | h <;> simp [Flowing, h]) hrun
    have hx' : (setVarHOLFinite name value s).locals.lookup x = some (.val (.word wx)) := by
      simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm dx, hx]
    have := ih (setVarHOLFinite name value s) wx hx' (by rw [hin]; exact hflow)
    rw [hin] at this
    obtain ⟨⟨w, hw⟩, hinner⟩ := this
    refine ⟨⟨w, ?_⟩, ?_⟩
    · simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm dy] using hw
    · rw [hpost, PanRunBounded.resVarEq_lookup, if_neg dy]
      exact hinner

/-- Key of a head carrying the words `x` and `y`. -/
def wordKey2 (x y : MlS) {F : Type} (s : PanSemStateFiniteExact 64 F) : Fin (2 ^ 128) :=
  ⟨(wordKey x s).val * 2 ^ 64 + (wordKey y s).val, by
    have := (wordKey x s).isLt
    have := (wordKey y s).isLt
    omega⟩

/-- Frame of the two-word loop: only the clock, `x` and `y` change, and `y` holds a word at
both ends. -/
def TwoWordFrame (x y : MlS) {F : Type} (s t : PanSemStateFiniteExact 64 F) : Prop :=
  LocFrame s t ∧ (∀ z, z ≠ x → z ≠ y → t.locals.lookup z = s.locals.lookup z) ∧
    (∃ w, s.locals.lookup y = some (.val (.word w))) ∧
    (∃ w, t.locals.lookup y = some (.val (.word w)))

theorem while_twoWord_guestInv (x y : MlS) (hxy : x ≠ y) {condition : ExpHOL 64}
    {body : ProgHOL 64} {B : Nat}
    (hbody : TerminatingProgBoundedOn GuestInv body B)
    (hloc : locOnly body = true)
    (havoid : ∀ z, z ≠ x → z ≠ y → avoidsLocal z body = true)
    (hcopy : CopiesTo y x body)
    (hact : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), LoopActive condition s →
      ∃ w, s.locals.lookup x = some (.val (.word w))) :
    TerminatingProgBoundedOn GuestInv (.while condition body) ((2 ^ 128 + 1) * (B + 1)) := by
  have hloop : NoRepeatLoop GuestInv GuestInv (TwoWordFrame x y) (wordKey2 x y) condition body B :=
    { body_bound := hbody
      entry := fun s _ _ hPs _ _ _ => guestInv_with_locals_clock s s.locals _ hPs
      step := by
        intro F s w _ hPs hcond hw _ _
        intro _
        intro hflow
        have hacts : LoopActive condition s := ⟨w, hcond, hw⟩
        obtain ⟨wx, hx⟩ := hact s hacts
        have hfr := locFrame_eval body hloc (decClockHOLFinite s)
        have hfr' : LocFrame s (evaluateHOLFiniteState (decClockHOLFinite s) body).2 := by
          unfold LocFrame at hfr ⊢
          rw [hfr]; rfl
        obtain ⟨hy0, hy1⟩ := hcopy.run (decClockHOLFinite s) wx hx hflow
        refine ⟨?_, hfr', ?_, hy0, ⟨wx, hy1⟩⟩
        · unfold LocFrame at hfr'
          rw [hfr']
          exact guestInv_with_locals_clock s _ _ hPs
        · intro z hzx hzy
          exact evaluate_avoidsLocal_flowing z body (havoid z hzx hzy) (decClockHOLFinite s)
            (by rcases hflow with h | h
                · exact Or.inl h
                · exact Or.inr (Or.inr h))
      trans := fun a b c hab hbc =>
        ⟨hab.1.trans hbc.1, fun z hzx hzy => (hbc.2.1 z hzx hzy).trans (hab.2.1 z hzx hzy),
          hab.2.2.1, hbc.2.2.2⟩
      key := by
        intro F a b hab hacta hactb hk
        obtain ⟨wa, ha⟩ := hact a hacta
        obtain ⟨wb, hb⟩ := hact b hactb
        obtain ⟨hfr, hoth, ⟨va, hva⟩, ⟨vb, hvb⟩⟩ := hab
        have hk' := congrArg Fin.val hk
        simp only [wordKey2, wordKey, ha, hb, hva, hvb] at hk'
        have hlt1 := wa.isLt
        have hlt2 := wb.isLt
        have hlt3 := va.isLt
        have hlt4 := vb.isLt
        have e1 : wa.toNat = wb.toNat := by omega
        have e2 : va.toNat = vb.toNat := by omega
        have hl : b.locals = a.locals := locals_ext fun z => by
          by_cases hzx : z = x
          · subst hzx; rw [ha, hb, BitVec.eq_of_toNat_eq e1]
          · by_cases hzy : z = y
            · subst hzy; rw [hva, hvb, BitVec.eq_of_toNat_eq e2]
            · exact hoth z hzx hzy
        unfold LocFrame at hfr
        rw [hl] at hfr
        exact hfr }
  intro F s hc hPs
  exact while_noRepeat hloop s hc hPs

end InitECandidate.Solver.Wave8GuestInv.Htab
