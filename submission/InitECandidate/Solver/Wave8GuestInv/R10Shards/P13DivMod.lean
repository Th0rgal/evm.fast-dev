import InitECandidate.Solver.Wave8GuestInv.R10Shards.P13Callees

/-! Verified R11 bounds for `digits_len`, `div64by32`, `udivmod`, `u256_divmod`, and `u256_mod`
(via guarded bounds on `divmnu` and `digits_divmod` for `m ≤ 16`).
Imports only `R10Shards.P13Callees` (zero `LeafStatements.lean` dependency). -/

set_option autoImplicit false
set_option linter.unusedTactic false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.P13.DivMod

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup InitECandidate.Solver.GuestUniformClockBound
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.P13.Common
open InitECandidate.Solver.Wave8GuestInv.P13.Callees

/-! ### 1. Heterogeneous composition combinators and `GuestLocalsOnly` -/

/-- A predicate that depends ONLY on `GuestInv` and a finite list of local variables `names`
(ignoring memory, globals, structs, and clock). -/
structure GuestLocalsOnly (names : List String)
    (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop) : Prop where
  toGuest : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → GuestInv s
  congr : ∀ {F : Type} (s t : PanSemStateFiniteExact 64 F),
    GuestInv t → (∀ n ∈ names, t.locals.lookup (ofString n) = s.locals.lookup (ofString n)) →
    P s → P t

theorem GuestLocalsOnly.toLocalsOnly {names : List String}
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} (h : GuestLocalsOnly names P) :
    LocalsOnly names P :=
  fun s locals k hkeep hP =>
    h.congr s _ (guestInv_with_locals_clock s locals k (h.toGuest s hP)) hkeep hP

theorem seq_to_guestInv {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (hPG : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → GuestInv s)
    {first second : ProgHOL 64} {a b : Nat}
    (h1 : TerminatingProgBoundedOn P first a)
    (h2 : TerminatingProgBoundedOn GuestInv second b) :
    TerminatingProgBoundedOn P (.seq first second) (a + b) := by
  intro F state hcode hP hnt
  have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata state first
  have hmidG := guestInv_evaluate state first (hPG state hP)
  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
  rcases hr1 : evaluateHOLFiniteState state first with ⟨r1, mid⟩
  simp only [hr1] at hmeta hmidG hnt ⊢
  cases r1 with
  | none =>
    dsimp only at hnt ⊢
    obtain ⟨s1, k1⟩ := h1 state hcode hP (by simp [hr1])
    rw [hr1] at s1 k1; dsimp only at s1 k1
    obtain ⟨s2, k2⟩ := h2 mid (hmeta.1.trans hcode) hmidG hnt
    exact ⟨by omega, by omega⟩
  | some _ =>
    dsimp only at hnt ⊢
    obtain ⟨s1, k1⟩ := h1 state hcode hP (by simpa [hr1] using hnt)
    rw [hr1] at s1 k1; dsimp only at s1 k1
    exact ⟨by omega, k1⟩

theorem seq_step_on {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {first second : ProgHOL 64} {a b : Nat}
    (h1 : TerminatingProgBoundedOn P first a)
    (hstep : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      s.code = originalRuntimeCode → P s → (evaluateHOLFiniteState s first).1 = none →
      Q (evaluateHOLFiniteState s first).2)
    (h2 : TerminatingProgBoundedOn Q second b) :
    TerminatingProgBoundedOn P (.seq first second) (a + b) := by
  intro F state hcode hP hnt
  have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata state first
  have hmid := hstep state hcode hP
  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
  rcases hr1 : evaluateHOLFiniteState state first with ⟨r1, mid⟩
  simp only [hr1] at hmeta hmid hnt ⊢
  cases r1 with
  | none =>
    dsimp only at hnt ⊢
    obtain ⟨s1, k1⟩ := h1 state hcode hP (by simp [hr1])
    rw [hr1] at s1 k1; dsimp only at s1 k1
    obtain ⟨s2, k2⟩ := h2 mid (hmeta.1.trans hcode) (hmid rfl) hnt
    exact ⟨by omega, by omega⟩
  | some _ =>
    dsimp only at hnt ⊢
    obtain ⟨s1, k1⟩ := h1 state hcode hP (by simpa [hr1] using hnt)
    rw [hr1] at s1 k1; dsimp only at s1 k1
    exact ⟨by omega, k1⟩

theorem seq_avoids_on {names : List String} {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (hP : GuestLocalsOnly names P)
    {first second : ProgHOL 64} {a b : Nat}
    (h1 : TerminatingProgBoundedOn GuestInv first a)
    (havoid : ∀ n ∈ names, avoidsLocal (ofString n) first = true)
    (h2 : TerminatingProgBoundedOn P second b) :
    TerminatingProgBoundedOn P (.seq first second) (a + b) := by
  refine seq_step_on (fun s hc hp => h1 s hc (hP.toGuest s hp)) ?_ h2
  intro F s _ hp hnone
  refine hP.congr s _ (guestInv_evaluate s first (hP.toGuest s hp)) ?_ hp
  intro n hn
  exact evaluate_avoidsLocal_flowing (ofString n) first (havoid n hn) s (Or.inl hnone)

theorem dec_avoids_on {names : List String} {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (hP : GuestLocalsOnly names P)
    (name : MlS) (hname : ∀ n ∈ names, ofString n ≠ name)
    (shape : ShapeHOL) (init : ExpHOL 64) {body : ProgHOL 64} {K : Nat}
    (hbody : TerminatingProgBoundedOn P body K) :
    TerminatingProgBoundedOn P (.dec name shape init body) K :=
  TerminatingProgBoundedOn.dec_onLocals hP.toLocalsOnly name hname shape init hbody

theorem decCall_avoids_on {names : List String} {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (hP : GuestLocalsOnly names P)
    {fname : MlS} {B Bc : Nat}
    (hf : TerminatingFunBoundedOn GuestInv fname B)
    (name : MlS) (hname : ∀ n ∈ names, ofString n ≠ name)
    (shape : ShapeHOL) (arguments : List (ExpHOL 64)) {continuation : ProgHOL 64}
    (hcont : TerminatingProgBoundedOn P continuation Bc) :
    TerminatingProgBoundedOn P (.decCall name shape fname arguments continuation) (B + Bc + 1) := by
  refine TerminatingProgBoundedOn.decCall_on hf name shape arguments
    (fun s _ _ callee _ _ hp _ _ => guestInv_callEntry s callee (hP.toGuest s hp)) ?_ hcont
  intro F state values body' callee ret' value post _ hp _ _ hrun
  have hpostG : GuestInv post := by
    have := guestInv_evaluate (callEntryStateHOLFinite state callee) body'
      (guestInv_callEntry state callee (hP.toGuest state hp))
    rw [hrun] at this; exact this
  have hresG : GuestInv (setVarHOLFinite name value { post with locals := state.locals }) :=
    guestInv_setVar name value _ (guestInv_with_locals_clock post state.locals post.clock hpostG)
  refine hP.congr state _ hresG ?_ hp
  intro n hn
  have hne := hname n hn
  simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hne]

/-! ### 2. `digits_len`, `div64by32`, `udivmod` -/

theorem fb_digits_len : TerminatingFunBoundedOn GuestInv (ofString "digits_len") K.«digits_len» := by
  fb_unfold 66 Guest.Software.guestFn_digits_len
  apply TerminatingProgBoundedOn.weaken'
  · apply TerminatingProgBoundedOn.seq_guestInv
    · exact while_down_unsigned_guestInv _ (straightOn _ rfl) (by counter_step)
    · exact straightOn _ rfl
  · fb_arith K.«digits_len»

theorem fb_div64by32 : TerminatingFunBoundedOn GuestInv (ofString "div64by32") K.«div64by32» := by
  fb_unfold 63 Guest.Software.guestFn_div64by32
  apply TerminatingProgBoundedOn.weaken'
  · apply dec_guestInv
    apply dec_guestInv
    apply dec_const_cap_guestInv "i" 32#64
    exact seq_to_guestInv (fun _ h => h.1)
      (while_down_first_capped_on .less (Or.inl rfl) "i" (straightOn _ rfl) rfl)
      (straightOn _ rfl)
  · rw [show (32#64 : BitVec 64).toNat = 32 by decide]
    fb_arith K.«div64by32»

theorem fb_udivmod : TerminatingFunBoundedOn GuestInv (ofString "udivmod") K.«udivmod» := by
  have _ := fb_trap_with
  fb_unfold 33 Guest.Software.guestFn_udivmod
  apply TerminatingProgBoundedOn.weaken'
  · apply TerminatingProgBoundedOn.seq_guestInv
    · fb_auto
    · apply TerminatingProgBoundedOn.seq_guestInv
      · fb_auto
      · apply dec_guestInv
        apply dec_guestInv
        apply dec_const_cap_guestInv "i" 64#64
        exact seq_to_guestInv (fun _ h => h.1)
          (while_down_first_capped_on .less (Or.inl rfl) "i" (straightOn _ rfl) rfl)
          (straightOn _ rfl)
  · rw [show (64#64 : BitVec 64).toNat = 64 by decide]
    fb_arith K.«udivmod»

/-! ### 3. Knuth D3 correction loop (`divmnu` Loop #4) -/

private theorem ite_flow_property {F : Type} (s : PanSemStateFiniteExact 64 F)
    (condition : ExpHOL 64) (yes no : ProgHOL 64) (R : PanSemStateFiniteExact 64 F → Prop)
    (hyes : ∀ w : BitVec 64,
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) condition = some (.val (.word w)) →
      w ≠ 0 →
      ((evaluateHOLFiniteState s yes).1 = none ∨ (evaluateHOLFiniteState s yes).1 = some .continue) →
      R (evaluateHOLFiniteState s yes).2)
    (hno : ((evaluateHOLFiniteState s no).1 = none ∨ (evaluateHOLFiniteState s no).1 = some .continue) →
      R (evaluateHOLFiniteState s no).2) :
    ((evaluateHOLFiniteState s (.ite condition yes no)).1 = none ∨
      (evaluateHOLFiniteState s (.ite condition yes no)).1 = some .continue) →
    R (evaluateHOLFiniteState s (.ite condition yes no)).2 := by
  rw [evaluateHOLFiniteState_ite]
  split
  · rename_i w hw
    split
    · exact hno
    · rename_i hnz
      exact hyes w hw hnz
  · intro hf; rcases hf with h | h <;> simp at h

private theorem mul_nonzero_local {F : Type} (s : PanSemStateFiniteExact 64 F)
    (counter : MlS) (factor : ExpHOL 64) (result : BitVec 64)
    (hr : evalAt s (.panop .mul [.var .local counter, factor]) = some (.val (.word result)))
    (hnz : result ≠ 0) :
    ∃ w : BitVec 64, s.locals.lookup counter = some (.val (.word w)) ∧ w ≠ 0 := by
  cases hl : s.locals.lookup counter with
  | none => simp [evalAt, evalHOLExact, evalListHOLExact, hl] at hr
  | some value =>
    cases value with
    | rStruct _ =>
      cases hf : evalAt s factor <;>
        simp [evalAt, evalHOLExact, evalListHOLExact, hl, hf, valueIsWord] at hr
    | nStruct _ _ =>
      cases hf : evalAt s factor <;>
        simp [evalAt, evalHOLExact, evalListHOLExact, hl, hf, valueIsWord] at hr
    | val wordval =>
      cases wordval with
      | word w =>
        refine ⟨w, rfl, ?_⟩
        intro hz; subst w
        cases hf : evalAt s factor with
        | none => simp [evalAt, evalHOLExact, evalListHOLExact, hl, hf] at hr
        | some v =>
          cases v with
          | rStruct _ => simp [evalAt, evalHOLExact, evalListHOLExact, hl, hf, valueIsWord] at hr
          | nStruct _ _ => simp [evalAt, evalHOLExact, evalListHOLExact, hl, hf, valueIsWord] at hr
          | val wv =>
            cases wv with
            | word z =>
              simp [evalAt, evalHOLExact, evalListHOLExact, hl, hf, valueIsWord, valueWord, panOpHOL] at hr
              subst result; exact hnz rfl

private theorem correction_test_nonzero {F : Type} (s : PanSemStateFiniteExact 64 F)
    (counter : MlS) (factor left : ExpHOL 64) (result : BitVec 64)
    (hc : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .lower left (.panop .mul [.var .local counter, factor])) = some (.val (.word result)))
    (hnz : result ≠ 0) :
    ∃ w : BitVec 64, s.locals.lookup counter = some (.val (.word w)) ∧ w ≠ 0 := by
  change evalAt s _ = _ at hc
  obtain ⟨_, r, _, hr, hword⟩ := evalAt_cmp s .lower _ _ result hc
  apply mul_nonzero_local s counter factor r hr
  intro hz; subst r
  simp [wordCmpHOL, BitVec.lt_def] at hword
  exact hnz hword

private def correctionCondition : ExpHOL 64 := .cmp .equal (.var .local (ofString "again")) (.const 1)
private def correctionOuter : ExpHOL 64 := .cmp .lower (.var .local (ofString "rhat")) (.const 4294967296)
private def correctionInner : ExpHOL 64 :=
  .cmp .lower
    (.op .or [.shift .lsl (.var .local (ofString "rhat")) (.const 32), .var .local (ofString "ujn2")])
    (.panop .mul [.var .local (ofString "qhat"), .var .local (ofString "vsec")])
private def correctionDecrement : ProgHOL 64 :=
  .seq (.assign .local (ofString "qhat") (.op .sub [.var .local (ofString "qhat"), .const 1]))
    (.seq (.assign .local (ofString "rhat") (.op .add [.var .local (ofString "rhat"), .var .local (ofString "vtop")]))
      (.assign .local (ofString "again") (.const 1)))
private def correctionBody : ProgHOL 64 :=
  .seq (.assign .local (ofString "again") (.const 0))
    (.ite correctionOuter (.ite correctionInner correctionDecrement .skip) .skip)

private noncomputable def correctionRank {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat := by
  classical
  exact if s.locals.lookup (ofString "again") = some (.val (.word 1#64)) then
    match s.locals.lookup (ofString "qhat") with
    | some (.val (.word w)) => w.toNat + 1
    | _ => 1
  else 0

theorem divisionCorrection_bound_guestInv :
    TerminatingProgBoundedOn GuestInv (.while correctionCondition correctionBody)
      ((2 ^ 64 + 1) * (0 + 1)) := by
  refine @TerminatingProgBoundedOn.while_rank GuestInv
    correctionCondition correctionBody 0 (2 ^ 64)
    correctionRank
    (fun s hs => guestInv_decClock s hs)
    (straightOn correctionBody rfl)
    (fun _ _ _ _ => by
      unfold correctionRank
      split
      · split
        · rename_i w _; have := w.isLt; omega
        · omega
      · omega)
    ?_
  intro F s _ hs hact hflow
  refine ⟨guestInv_evaluate _ _ (guestInv_decClock s hs), ?_⟩
  obtain ⟨word, hw, hnz⟩ := hact
  change evalAt s _ = _ at hw
  obtain ⟨a, v, ha, hv, hword⟩ := evalAt_cmp s .equal _ _ word hw
  have hv1 : v = 1#64 := by simpa [evalAt, evalHOLExact] using hv.symm
  subst v
  have hla : s.locals.lookup (ofString "again") = some (.val (.word a)) := by
    simpa [evalAt, evalHOLExact] using ha
  have ha1 : a = 1#64 := by
    by_cases hcmp : wordCmpHOL .equal a 1#64 = true
    · simpa [wordCmpHOL] using hcmp
    · simp [hcmp] at hword; exact absurd hword hnz
  subst a
  have hpositive : 0 < correctionRank s := by
    unfold correctionRank
    rw [if_pos hla]
    split <;> omega
  let s0 := setVarHOLFinite (ofString "again") (.val (.word 0#64)) (decClockHOLFinite s)
  have hreset : evaluateHOLFiniteState (decClockHOLFinite s)
      (.assign .local (ofString "again") (.const 0)) = (none, s0) := by
    simp [s0, evaluateHOLFiniteState_assign, evalHOLExact, isValidValueHOLExact,
      setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL, lookupKvarHOLExact, decClockHOLFinite, hla]
  have hzero : correctionRank s0 = 0 := by
    simp [correctionRank, s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  unfold correctionBody at hflow ⊢
  rw [evaluateHOLFiniteState_seq_line780, hreset] at hflow ⊢
  dsimp only at hflow ⊢
  refine ite_flow_property s0 correctionOuter (.ite correctionInner correctionDecrement .skip) .skip
    (fun t => correctionRank t < correctionRank s) ?_ ?_ hflow
  · intro _ _ _ hflowInner
    refine ite_flow_property s0 correctionInner correctionDecrement .skip
      (fun t => correctionRank t < correctionRank s) ?_ ?_ hflowInner
    · intro inner hin hinner hflowDec
      obtain ⟨q, hq, hqnz⟩ := correction_test_nonzero s0 (ofString "qhat")
        (.var .local (ofString "vsec")) _ inner hin hinner
      have hqs : s.locals.lookup (ofString "qhat") = some (.val (.word q)) := by
        have hne : (ofString "again" == ofString "qhat") = false := by decide
        have hq' := hq
        simp only [s0, decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Bool.false_eq_true, ↓reduceIte] at hq'
        exact hq'
      have heffect : CounterStep (ofString "qhat") (-1) correctionDecrement :=
        CounterStep.suffix _ _ _ (CounterStep.sub_one _) (by decide)
      have hpost : (evaluateHOLFiniteState s0 correctionDecrement).2.locals.lookup (ofString "qhat") =
          some (.val (.word (q - 1))) := by
        simpa only [BitVec.sub_eq_add_neg] using heffect s0 q hq hflowDec
      have hpostrank : correctionRank (evaluateHOLFiniteState s0 correctionDecrement).2 ≤
          (q - 1).toNat + 1 := by
        unfold correctionRank
        split <;> simp [hpost]
      have hbefore : correctionRank s = q.toNat + 1 := by
        unfold correctionRank
        rw [if_pos hla, hqs]
      have hqpos : 0 < q.toNat := by
        by_contra hc
        have hq0 : q = 0#64 := BitVec.eq_of_toNat_eq (by simpa using Nat.eq_zero_of_not_pos hc)
        exact hqnz hq0
      have hdrop : (q - 1).toNat < q.toNat := by
        rw [BitVec.toNat_sub]
        change (18446744073709551615 + q.toNat) % 18446744073709551616 < q.toNat
        have := q.isLt
        omega
      rw [hbefore]
      omega
    · intro _; simpa only [evaluateHOLFiniteState_skip, hzero] using hpositive
  · intro _; simpa only [evaluateHOLFiniteState_skip, hzero] using hpositive

/-! ### 4. Downward scaled-8 memory walk (`divmnu` Loop #1: bound + no-fallthrough when `n = 0`) -/

def downDomainRank (a : BitVec 64) : Nat :=
  if sourceBase ≤ a.toNat ∧ a.toNat < heapEnd then a.toNat - sourceBase + 8 else 0

theorem downDomainRank_bound (a : BitVec 64) : downDomainRank a ≤ domainBytes + 8 := by
  unfold downDomainRank domainBytes
  split_ifs <;> omega

theorem downDomainRank_sub_lt (a : BitVec 64) (ha : sourceBase ≤ a.toNat ∧ a.toNat < heapEnd) :
    downDomainRank (a - BitVec.ofNat 64 8) < downDomainRank a := by
  have hs : 8 ≤ sourceBase := by decide
  have hsub : (a - BitVec.ofNat 64 8).toNat = a.toNat - 8 := by
    rw [BitVec.toNat_sub]
    change (18446744073709551616 - 8 + a.toNat) % 18446744073709551616 = a.toNat - 8
    have := a.isLt
    omega
  unfold downDomainRank
  rw [if_pos ha, hsub]
  split_ifs <;> omega

def scaledDownMu (base counter : MlS) {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat :=
  match s.locals.lookup base, s.locals.lookup counter with
  | some (.val (.word b)), some (.val (.word i)) => downDomainRank (b + i * 8)
  | _, _ => 0

theorem scaledDownMu_le (base counter : MlS) {F : Type} (s : PanSemStateFiniteExact 64 F) :
    scaledDownMu base counter s ≤ domainBytes + 8 := by
  unfold scaledDownMu
  split
  · exact downDomainRank_bound _
  · omega

private theorem scaled8_locals_inv {F : Type} (s : PanSemStateFiniteExact 64 F)
    (base counter : MlS) (address : BitVec 64)
    (h : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .local base, .panop .mul [.var .local counter, .const 8#64]]) = some (.val (.word address))) :
    ∃ b i : BitVec 64, s.locals.lookup base = some (.val (.word b)) ∧
      s.locals.lookup counter = some (.val (.word i)) ∧ address = b + i * 8 := by
  cases hb : s.locals.lookup base with
  | none => simp [evalHOLExact, evalListHOLExact, hb] at h
  | some bv =>
    cases bv with
    | rStruct _ =>
      cases hi : s.locals.lookup counter with
      | none => simp [evalHOLExact, evalListHOLExact, hb, hi] at h
      | some v =>
        cases v with
        | val w => cases w; simp [evalHOLExact, evalListHOLExact, hb, hi, valueIsWord, valueWord, panOpHOL] at h
        | rStruct _ => simp [evalHOLExact, evalListHOLExact, hb, hi, valueIsWord] at h
        | nStruct _ _ => simp [evalHOLExact, evalListHOLExact, hb, hi, valueIsWord] at h
    | nStruct _ _ =>
      cases hi : s.locals.lookup counter with
      | none => simp [evalHOLExact, evalListHOLExact, hb, hi] at h
      | some v =>
        cases v with
        | val w => cases w; simp [evalHOLExact, evalListHOLExact, hb, hi, valueIsWord, valueWord, panOpHOL] at h
        | rStruct _ => simp [evalHOLExact, evalListHOLExact, hb, hi, valueIsWord] at h
        | nStruct _ _ => simp [evalHOLExact, evalListHOLExact, hb, hi, valueIsWord] at h
    | val bw =>
      cases bw with
      | word b =>
        cases hi : s.locals.lookup counter with
        | none => simp [evalHOLExact, evalListHOLExact, hb, hi] at h
        | some iv =>
          cases iv with
          | rStruct _ => simp [evalHOLExact, evalListHOLExact, hb, hi, valueIsWord] at h
          | nStruct _ _ => simp [evalHOLExact, evalListHOLExact, hb, hi, valueIsWord] at h
          | val iw =>
            cases iw with
            | word i =>
              refine ⟨b, i, rfl, rfl, ?_⟩
              simpa [evalHOLExact, evalListHOLExact, hb, hi, valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL] using h.symm

def scaled8DownBody (base counter : MlS) (valExp : ExpHOL 64) : ProgHOL 64 :=
  .seq (.store (.op .add [.var .local base, .panop .mul [.var .local counter, .const 8#64]]) valExp)
       (.assign .local counter (.op .sub [.var .local counter, .const 1#64]))

def scaled8DownCond (counter : MlS) : ExpHOL 64 :=
  .cmp .lower (.const 0#64) (.var .local counter)

private theorem scaled8DownBody_noBreak {F : Type} (s : PanSemStateFiniteExact 64 F)
    (base counter : MlS) (valExp : ExpHOL 64) :
    (evaluateHOLFiniteState s (scaled8DownBody base counter valExp)).1 ≠ some .break := by
  unfold scaled8DownBody
  rw [evaluateHOLFiniteState_seq_line780]
  have hsf := evaluate_store_control_frame s
    (.op .add [.var .local base, .panop .mul [.var .local counter, .const 8#64]]) valExp
  rcases hst : evaluateHOLFiniteState s
    (.store (.op .add [.var .local base, .panop .mul [.var .local counter, .const 8#64]]) valExp) with ⟨ra, mid⟩
  simp only [hst] at hsf ⊢
  cases ra with
  | none =>
    dsimp only
    rw [evaluateHOLFiniteState_assign]
    split
    · simp
    · split <;> simp
  | some ra =>
    rcases hsf.1 with h1 | h2 <;> simp_all

private theorem store_scaled8_step {F : Type} (s : PanSemStateFiniteExact 64 F)
    (base counter : MlS) (valExp : ExpHOL 64)
    (hw : WordExpression valExp) (hne : base ≠ counter) (hg : GuestInv s)
    (hflow : (evaluateHOLFiniteState s (scaled8DownBody base counter valExp)).1 = none) :
    ∃ b i : BitVec 64,
      s.locals.lookup base = some (.val (.word b)) ∧
      s.locals.lookup counter = some (.val (.word i)) ∧
      sourceBase ≤ (b + i * 8).toNat ∧ (b + i * 8).toNat < heapEnd ∧
      (evaluateHOLFiniteState s (scaled8DownBody base counter valExp)).2.locals.lookup base = some (.val (.word b)) ∧
      (evaluateHOLFiniteState s (scaled8DownBody base counter valExp)).2.locals.lookup counter = some (.val (.word (i - 1))) := by
  unfold scaled8DownBody at hflow ⊢
  set stProg := ProgHOL.store (.op .add [.var .local base, .panop .mul [.var .local counter, .const 8#64]]) valExp
  set asProg := ProgHOL.assign .local counter (.op .sub [.var .local counter, .const 1#64])
  rw [evaluateHOLFiniteState_seq_line780] at hflow ⊢
  have hstFrame := evaluate_store_control_frame s (.op .add [.var .local base, .panop .mul [.var .local counter, .const 8#64]]) valExp
  rcases hst : evaluateHOLFiniteState s stProg with ⟨r1, mid⟩
  rw [hst] at hflow hstFrame
  cases r1 with
  | some _ => simp at hflow
  | none =>
    dsimp only at hflow hstFrame ⊢
    have hmid_loc : mid.locals = s.locals := hstFrame.2.1
    have hst' := hst
    unfold stProg at hst'
    rw [evaluateHOLFiniteState_store] at hst'
    split at hst'
    · rename_i addr haddr
      obtain ⟨b, i, hb, hi, rfl⟩ := scaled8_locals_inv s base counter addr haddr
      split at hst'
      · rename_i v hv
        obtain ⟨_, rfl⟩ := hw s v hv
        simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL] at hst'
        by_cases hd : s.memaddrs (b + i * 8)
        · rw [hg.memaddrs] at hd
          have hdom := ordinaryDomain_interval (b + i * 8) hd
          have hmid_i : mid.locals.lookup counter = some (.val (.word i)) := by rw [hmid_loc]; exact hi
          have hmid_b : mid.locals.lookup base = some (.val (.word b)) := by rw [hmid_loc]; exact hb
          have hass : evaluateHOLFiniteState mid asProg =
              (none, setVarHOLFinite counter (.val (.word (i - 1))) mid) := by
            simp [asProg, evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hmid_i,
              wordOpHOL, wordOp, valueIsWord, valueWord, lookupKvarHOLExact, isValidValueHOLExact,
              setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL]
          rw [hass]
          refine ⟨b, i, hb, hi, hdom.1, by omega, ?_, ?_⟩
          · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hne, hmid_b]
          · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        · rw [if_neg hd] at hst'; simp at hst'
      · simp at hst'
    · simp at hst'

def localWordNat (counter : MlS) {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat :=
  match s.locals.lookup counter with
  | some (.val (.word i)) => i.toNat
  | _ => 0

theorem while_scaled8_down_bound_and_nofallthrough
    (base counter : MlS) (valExp : ExpHOL 64)
    (hw : WordExpression valExp) (hne : base ≠ counter) :
    TerminatingProgBoundedOn GuestInv (.while (scaled8DownCond counter) (scaled8DownBody base counter valExp))
      ((domainBytes + 8 + 1) * (0 + 1)) ∧
    (∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      GuestInv s →
      domainBytes + 8 < localWordNat counter s →
      (evaluateHOLFiniteState s (.while (scaled8DownCond counter) (scaled8DownBody base counter valExp))).1 ≠ none) := by
  have hstep : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      s.code = originalRuntimeCode → GuestInv s → LoopActive (scaled8DownCond counter) s →
      ((evaluateHOLFiniteState (decClockHOLFinite s) (scaled8DownBody base counter valExp)).1 = none ∨
        (evaluateHOLFiniteState (decClockHOLFinite s) (scaled8DownBody base counter valExp)).1 = some .continue) →
      GuestInv (evaluateHOLFiniteState (decClockHOLFinite s) (scaled8DownBody base counter valExp)).2 ∧
        scaledDownMu base counter (evaluateHOLFiniteState (decClockHOLFinite s) (scaled8DownBody base counter valExp)).2 <
          scaledDownMu base counter s := by
    intro F s _ hg _ hflow
    have hnone : (evaluateHOLFiniteState (decClockHOLFinite s) (scaled8DownBody base counter valExp)).1 = none :=
      hflow.resolve_right (evaluate_noTopContinue (scaled8DownBody base counter valExp) rfl (decClockHOLFinite s))
    obtain ⟨b, i, hb, hi, hlo, hhi, hb', hi'⟩ :=
      store_scaled8_step (decClockHOLFinite s) base counter valExp hw hne
        (guestInv_decClock s hg) hnone
    refine ⟨guestInv_evaluate _ _ (guestInv_decClock s hg), ?_⟩
    change s.locals.lookup base = some (.val (.word b)) at hb
    change s.locals.lookup counter = some (.val (.word i)) at hi
    unfold scaledDownMu
    rw [hb', hi', hb, hi]
    dsimp only
    have heq : b + (i - 1) * 8 = (b + i * 8) - BitVec.ofNat 64 8 := by bv_omega
    rw [heq]
    exact downDomainRank_sub_lt (b + i * 8) ⟨hlo, hhi⟩
  refine ⟨?_, ?_⟩
  · refine @TerminatingProgBoundedOn.while_rank GuestInv
      (scaled8DownCond counter) (scaled8DownBody base counter valExp) 0 (domainBytes + 8)
      (scaledDownMu base counter)
      (fun s hs => guestInv_decClock s hs)
      (straightOn (scaled8DownBody base counter valExp) rfl)
      (fun s _ _ _ => scaledDownMu_le base counter s)
      hstep
  · suffices haux : ∀ (rk : Nat) {F : Type} (s : PanSemStateFiniteExact 64 F),
        GuestInv s →
        rk = scaledDownMu base counter s →
        rk < localWordNat counter s →
        (evaluateHOLFiniteState s (.while (scaled8DownCond counter) (scaled8DownBody base counter valExp))).1 ≠ none by
      intro F s hg hbig
      have hle := scaledDownMu_le base counter s
      exact haux (scaledDownMu base counter s) s hg rfl (by omega)
    intro rk
    induction rk using Nat.strongRecOn with
    | ind rk ih =>
      intro F s hg hrk hgt hnone
      rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnone
      cases hi : s.locals.lookup counter with
      | none => simp [localWordNat, hi] at hgt
      | some vc =>
        cases vc with
        | rStruct _ => simp [localWordNat, hi] at hgt
        | nStruct _ _ => simp [localWordNat, hi] at hgt
        | val wv =>
          cases wv with
          | word i =>
            simp only [localWordNat, hi] at hgt
            have hcmp : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
                (scaled8DownCond counter) = some (.val (.word 1#64)) := by
              simp [scaled8DownCond, evalHOLFinite, evalHOLExact, hi, wordCmpHOL, BitVec.lt_def]
              omega
            rw [hcmp] at hnone
            dsimp only at hnone
            rw [if_pos (show (1#64 : BitVec 64) ≠ 0 by decide)] at hnone
            by_cases hclk : s.clock = 0
            · rw [if_pos hclk] at hnone; simp at hnone
            · rw [if_neg hclk] at hnone
              have hnc := evaluate_noTopContinue (scaled8DownBody base counter valExp) rfl (decClockHOLFinite s)
              have hnb := scaled8DownBody_noBreak (decClockHOLFinite s) base counter valExp
              rcases hbody : evaluateHOLFiniteState (decClockHOLFinite s) (scaled8DownBody base counter valExp) with ⟨r1, post⟩
              rw [hbody] at hnone hnc hnb
              cases r1 with
              | some r => cases r <;> simp_all
              | none =>
                dsimp only at hnone
                have hbody_none : (evaluateHOLFiniteState (decClockHOLFinite s) (scaled8DownBody base counter valExp)).1 = none := by rw [hbody]
                obtain ⟨b0, i0, hb0, hi0, hlo0, hhi0, hb0', hi0'⟩ :=
                  store_scaled8_step (decClockHOLFinite s) base counter valExp hw hne
                    (guestInv_decClock s hg) hbody_none
                rw [hbody] at hb0' hi0'
                dsimp only at hb0' hi0'
                change s.locals.lookup base = some (.val (.word b0)) at hb0
                change s.locals.lookup counter = some (.val (.word i0)) at hi0
                have hi_eq : i0 = i := by
                  have := hi0.symm.trans hi
                  cases this; rfl
                subst hi_eq
                have hlt_mu : scaledDownMu base counter post < rk := by
                  rw [hrk]
                  unfold scaledDownMu
                  rw [hb0', hi0', hb0, hi]
                  dsimp only
                  have heq : b0 + (i0 - 1) * 8 = (b0 + i0 * 8) - BitVec.ofNat 64 8 := by bv_omega
                  rw [heq]
                  exact downDomainRank_sub_lt (b0 + i0 * 8) ⟨hlo0, hhi0⟩
                have hi0_sub : (i0 - 1).toNat = i0.toNat - 1 := by
                  rw [BitVec.toNat_sub]
                  change (18446744073709551615 + i0.toNat) % 18446744073709551616 = i0.toNat - 1
                  have := i0.isLt
                  omega
                have hpost_gt : scaledDownMu base counter post < localWordNat counter post := by
                  simp only [localWordNat, hi0', hi0_sub]
                  omega
                have hg_post : GuestInv post := by
                  have := guestInv_evaluate (decClockHOLFinite s) (scaled8DownBody base counter valExp)
                    (guestInv_decClock s hg)
                  rw [hbody] at this; exact this
                exact ih (scaledDownMu base counter post) hlt_mu post hg_post rfl hpost_gt hnone

/-! ### 5. `digits_len` return-value bound (`ret ≤ n`) -/

theorem locN_setVar_self {F : Type} (s : PanSemStateFiniteExact 64 F) (name : String) (w : BitVec 64) :
    locN (setVarHOLFinite (ofString name) (.val (.word w)) s) name = w.toNat := by
  simp [locN, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]

private def digitsLenBody : ProgHOL 64 :=
  InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
    (extractFn Guest.Software.guestFn_digits_len).body

private def digitsLenLoop : ProgHOL 64 :=
  match digitsLenBody with
  | .seq w _ => w
  | _ => .skip

private def digitsLenStep : ProgHOL 64 :=
  match digitsLenLoop with
  | .while _ b => b
  | _ => .skip

private theorem digitsLenStep_cases {F : Type} (s : PanSemStateFiniteExact 64 F) (w : BitVec 64)
    (hn : s.locals.lookup (ofString "n") = some (.val (.word w))) :
    (evaluateHOLFiniteState s digitsLenStep = (none, setVarHOLFinite (ofString "n") (.val (.word (w - 1))) s)) ∨
    (∃ post, evaluateHOLFiniteState s digitsLenStep = (some (.returned (.val (.word w))), post)) ∨
    (∃ post, evaluateHOLFiniteState s digitsLenStep = (some .error, post)) := by
  have hstep : digitsLenStep = (ProgHOL.ite (.cmp .notEqual (.load .one (.op .add [.var .local (ofString "p"),
      .panop .mul [.op .sub [.var .local (ofString "n"), .const 1#64], .const 8#64]])) (.const 0#64))
      (.return (.var .local (ofString "n"))) .skip).seq
      (.assign .local (ofString "n") (.op .sub [.var .local (ofString "n"), .const 1#64])) := rfl
  rw [hstep, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
  split
  · split
    · rw [evaluateHOLFiniteState_skip]
      dsimp only
      left
      simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hn,
        wordOpHOL, wordOp, valueIsWord, valueWord, lookupKvarHOLExact, isValidValueHOLExact,
        setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL]
    · rw [evaluateHOLFiniteState_return]
      simp only [evalHOLExact, hn, shapeOfHOLExact, sizeOfShapeWithContextHOL, show (1 : Nat) ≤ 32 by decide, ↓reduceIte]
      exact Or.inr (Or.inl ⟨_, rfl⟩)
  · exact Or.inr (Or.inr ⟨_, rfl⟩)

private theorem digitsLenLoop_ret_le :
    ∀ (fuel : Nat) {F : Type} (s post : PanSemStateFiniteExact 64 F) (N : Nat) (v : ValueHOL 64),
      fuel = locN s "n" →
      locN s "n" ≤ N →
      evaluateHOLFiniteState s digitsLenLoop = (some (.returned v), post) →
      ∃ w : BitVec 64, v = .val (.word w) ∧ w.toNat ≤ N := by
  intro fuel
  induction fuel with
  | zero =>
    intro F s post N v hfuel _ hrun
    have hloop : digitsLenLoop = .while (.cmp .lower (.const 0#64) (.var .local (ofString "n"))) digitsLenStep := rfl
    rw [hloop, evaluateHOLFiniteState_while_fixClockRewrite] at hrun
    cases hn : s.locals.lookup (ofString "n") with
    | none => simp [evalHOLFinite, evalHOLExact, hn] at hrun
    | some val =>
      cases val with
      | rStruct _ => simp [evalHOLFinite, evalHOLExact, hn] at hrun
      | nStruct _ _ => simp [evalHOLFinite, evalHOLExact, hn] at hrun
      | val wv =>
        cases wv with
        | word w =>
          have hw0 : w = 0 := by
            simp [locN, hn] at hfuel
            exact BitVec.eq_of_toNat_eq (by simpa using hfuel.symm)
          subst hw0
          simp [evalHOLFinite, evalHOLExact, hn, wordCmpHOL] at hrun
  | succ k ih =>
    intro F s post N v hfuel hle hrun
    have hloop : digitsLenLoop = .while (.cmp .lower (.const 0#64) (.var .local (ofString "n"))) digitsLenStep := rfl
    rw [hloop, evaluateHOLFiniteState_while_fixClockRewrite] at hrun
    cases hn : s.locals.lookup (ofString "n") with
    | none => simp [locN, hn] at hfuel
    | some val =>
      cases val with
      | rStruct _ => simp [locN, hn] at hfuel
      | nStruct _ _ => simp [locN, hn] at hfuel
      | val wv =>
        cases wv with
        | word w =>
          have hw_eq : w.toNat = k + 1 := by simpa [locN, hn] using hfuel.symm
          have hcmp : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
              (.cmp .lower (.const 0#64) (.var .local (ofString "n"))) = some (.val (.word 1#64)) := by
            simp [evalHOLFinite, evalHOLExact, hn, wordCmpHOL, BitVec.lt_def]
            omega
          rw [hcmp] at hrun
          dsimp only at hrun
          rw [if_pos (show (1#64 : BitVec 64) ≠ 0 by decide)] at hrun
          by_cases hclk : s.clock = 0
          · rw [if_pos hclk] at hrun; simp at hrun
          · rw [if_neg hclk] at hrun
            rcases digitsLenStep_cases (decClockHOLFinite s) w hn with hnext | ⟨_, hret⟩ | ⟨_, herr⟩
            · rw [hnext] at hrun
              dsimp only at hrun
              rw [← hloop] at hrun
              have hloc' : locN (setVarHOLFinite (ofString "n") (.val (.word (w - 1))) (decClockHOLFinite s)) "n" = k := by
                rw [locN_setVar_self, BitVec.toNat_sub]
                change (18446744073709551615 + w.toNat) % 18446744073709551616 = k
                have := w.isLt
                omega
              exact ih _ post N v hloc'.symm (by omega) hrun
            · rw [hret] at hrun
              simp at hrun
              exact ⟨w, hrun.1.symm, by omega⟩
            · rw [herr] at hrun
              simp at hrun

theorem digits_len_ret_le {F : Type} (s post : PanSemStateFiniteExact 64 F) (N : Nat) (v : ValueHOL 64)
    (hle : locN s "n" ≤ N)
    (hrun : evaluateHOLFiniteState s digitsLenBody = (some (.returned v), post)) :
    ∃ w : BitVec 64, v = .val (.word w) ∧ w.toNat ≤ N := by
  have hseq : digitsLenBody = .seq digitsLenLoop (.return (.const 0#64)) := rfl
  rw [hseq, evaluateHOLFiniteState_seq_line780] at hrun
  rcases hw : evaluateHOLFiniteState s digitsLenLoop with ⟨res, mid⟩
  rw [hw] at hrun
  cases res with
  | none =>
    dsimp only at hrun
    rw [evaluateHOLFiniteState_return] at hrun
    simp [evalHOLExact, shapeOfHOLExact] at hrun
    exact ⟨0, hrun.1.symm, Nat.zero_le _⟩
  | some r =>
    dsimp only at hrun
    obtain ⟨h1, rfl⟩ := Prod.mk.inj hrun
    have hr : r = .returned v := Option.some.inj h1
    subst hr
    exact digitsLenLoop_ret_le (locN s "n") s mid N v rfl hle hw

/-! ### 6. Guarded bound on `divmnu` under `DivMnuGuard` (`n ≤ m ≤ 16`) -/

def DivMnuGuard : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => GuestInv s ∧ ∃ wm wn : BitVec 64,
    s.locals.lookup (ofString "m") = some (.val (.word wm)) ∧
    s.locals.lookup (ofString "n") = some (.val (.word wn)) ∧
    wn.toNat ≤ wm.toNat ∧ wm.toNat ≤ 16

theorem glo_divMnuGuard : GuestLocalsOnly ["m", "n"] DivMnuGuard where
  toGuest := fun _ h => h.1
  congr := fun _ _ hg hkeep ⟨_, wm, wn, hm, hn, hnm, hm16⟩ =>
    ⟨hg, wm, wn, (hkeep "m" (by simp)).trans hm, (hkeep "n" (by simp)).trans hn, hnm, hm16⟩

def DivMnuPostIte : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => GuestInv s ∧ ∃ wm wn : BitVec 64,
    s.locals.lookup (ofString "m") = some (.val (.word wm)) ∧
    s.locals.lookup (ofString "n") = some (.val (.word wn)) ∧
    wn.toNat ≠ 1 ∧ wn.toNat ≤ wm.toNat ∧ wm.toNat ≤ 16

theorem glo_divMnuPostIte : GuestLocalsOnly ["m", "n"] DivMnuPostIte where
  toGuest := fun _ h => h.1
  congr := fun _ _ hg hkeep ⟨_, wm, wn, hm, hn, hn1, hnm, hm16⟩ =>
    ⟨hg, wm, wn, (hkeep "m" (by simp)).trans hm, (hkeep "n" (by simp)).trans hn, hn1, hnm, hm16⟩

def DivMnuGe2 : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => GuestInv s ∧ ∃ wm wn : BitVec 64,
    s.locals.lookup (ofString "m") = some (.val (.word wm)) ∧
    s.locals.lookup (ofString "n") = some (.val (.word wn)) ∧
    2 ≤ wn.toNat ∧ wn.toNat ≤ wm.toNat ∧ wm.toNat ≤ 16

theorem glo_divMnuGe2 : GuestLocalsOnly ["m", "n"] DivMnuGe2 where
  toGuest := fun _ h => h.1
  congr := fun _ _ hg hkeep ⟨_, wm, wn, hm, hn, hge2, hnm, hm16⟩ =>
    ⟨hg, wm, wn, (hkeep "m" (by simp)).trans hm, (hkeep "n" (by simp)).trans hn, hge2, hnm, hm16⟩

private theorem noFallthrough_return (e : ExpHOL 64) {F : Type} (s : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState s (.return e)).1 ≠ none := by
  rw [evaluateHOLFiniteState_return]
  split
  · simp
  · split <;> simp

private theorem noFallthrough_tailCall (fn : MlS) (args : List (ExpHOL 64))
    {F : Type} (s : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState s (.call none fn args)).1 ≠ none := by
  rw [evaluateHOLFiniteState_call]
  split
  · simp
  · split
    · simp
    · split
      · simp
      · dsimp only
        rcases evaluateHOLFiniteState _ _ with ⟨r, _⟩
        cases r with
        | none => simp
        | some r => cases r <;> simp; split <;> simp

private theorem noFallthrough_seq_right (a b : ProgHOL 64) {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hb : ∀ (t : PanSemStateFiniteExact 64 F), (evaluateHOLFiniteState t b).1 ≠ none) :
    (evaluateHOLFiniteState s (.seq a b)).1 ≠ none := by
  rw [evaluateHOLFiniteState_seq_line780]
  rcases evaluateHOLFiniteState s a with ⟨r1, mid⟩
  cases r1 with
  | none => exact hb mid
  | some _ => simp

private theorem noFallthrough_dec (name : MlS) (sh : ShapeHOL) (init : ExpHOL 64) (body : ProgHOL 64)
    {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hb : ∀ (t : PanSemStateFiniteExact 64 F), (evaluateHOLFiniteState t body).1 ≠ none) :
    (evaluateHOLFiniteState s (.dec name sh init body)).1 ≠ none := by
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  split
  · simp
  · rename_i val _
    split
    · have h := hb (setVarHOLFinite name val s)
      rcases hr : evaluateHOLFiniteState (setVarHOLFinite name val s) body with ⟨r, _⟩
      rw [hr] at h
      exact h
    · simp

private theorem assign_local_word_none {F : Type} (s : PanSemStateFiniteExact 64 F)
    (name : MlS) (e : ExpHOL 64) (w : BitVec 64)
    (he : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e = some (.val (.word w)))
    (hnone : (evaluateHOLFiniteState s (.assign .local name e)).1 = none) :
    (evaluateHOLFiniteState s (.assign .local name e)).2 = setVarHOLFinite name (.val (.word w)) s := by
  rw [evaluateHOLFiniteState_assign] at hnone ⊢
  rw [he] at hnone ⊢
  dsimp only at hnone ⊢
  split at hnone
  · rename_i hv
    rw [if_pos hv]
    rfl
  · simp at hnone

theorem fb_divmnu_guarded : TerminatingFunBoundedOn DivMnuGuard (ofString "divmnu") K.«divmnu» := by
  have _ := fb_div64by32
  have _ := fb_nlz32
  refine ⟨_, _, _, lookup_of_guestAst_getElem 67 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_divmnu) rfl, ?_⟩
  dsimp only [extractFn, Guest.Software.guestFn_divmnu,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  have hLoop1 := while_scaled8_down_bound_and_nofallthrough (ofString "vn") (ofString "i")
    (.op .and [.op .or [.shift .lsl (.load .one (.op .add [.var .local (ofString "v"), .panop .mul [.var .local (ofString "i"), .const 8#64]])) (.var .local (ofString "s")),
      .shift .lsr (.load .one (.op .add [.var .local (ofString "v"), .panop .mul [.op .sub [.var .local (ofString "i"), .const 1#64], .const 8#64]])) (.op .sub [.const 32#64, .var .local (ofString "s")])],
      .const 4294967295#64])
    (WordExpression.op _ _) (by decide)
  apply TerminatingProgBoundedOn.weaken'
  · apply dec_avoids_on glo_divMnuGuard _ (by decide)
    apply dec_avoids_on glo_divMnuGuard _ (by decide)
    apply seq_step_on (Q := DivMnuPostIte)
    · exact TerminatingProgBoundedOn.ite_on
        (fun s hc hP =>
          (dec_guestInv _ _ _ (dec_guestInv _ _ _
            (TerminatingProgBoundedOn.seq_guestInv (straightOn _ rfl)
              (TerminatingProgBoundedOn.seq_guestInv
                (while_down_unsigned_guestInv _
                  (TerminatingProgBoundedOn.seq_guestInv (straightOn _ rfl)
                    (decCall_guestInv' fb_div64by32 (straightOn _ rfl)))
                  (CounterStep.suffix _ _ _ (CounterStep.sub_one _) (by decide)))
                (straightOn _ rfl))))) s hc hP.1)
        (fun s hc hP => straightOn _ rfl s hc hP.1)
    · intro F s _ ⟨hg, wm, wn, hm, hn, hnm, hm16⟩ hnone
      rw [evaluateHOLFiniteState_ite] at hnone ⊢
      have hcond : @evalHOLExact 64 _ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
          (.cmp .equal (.var .local (ofString "n")) (.const 1#64)) =
          some (.val (.word (if wn == 1#64 then 1#64 else 0#64))) := by
        simp [evalHOLExact, hn, wordCmpHOL]
      rw [hcond] at hnone ⊢
      by_cases h1 : wn == 1#64
      · simp only [h1, ↓reduceIte, show ¬ ((1#64 : BitVec 64) = 0) by decide] at hnone
        exfalso
        exact noFallthrough_dec _ _ _ _ s (fun s1 =>
          noFallthrough_dec _ _ _ _ s1 (fun s2 =>
            noFallthrough_seq_right _ _ s2 (fun s3 =>
              noFallthrough_seq_right _ _ s3 (fun s4 =>
                noFallthrough_seq_right _ _ s4 (fun s5 =>
                  noFallthrough_return _ s5))))) hnone
      · simp only [h1, Bool.false_eq_true, ↓reduceIte] at hnone ⊢
        rw [evaluateHOLFiniteState_skip]
        refine ⟨hg, wm, wn, hm, hn, ?_, hnm, hm16⟩
        intro heq1; apply h1
        simp [BitVec.eq_of_toNat_eq (show wn.toNat = (1#64 : BitVec 64).toNat by simpa using heq1)]
    · apply dec_avoids_on glo_divMnuPostIte _ (by decide)
      apply dec_avoids_on glo_divMnuPostIte _ (by decide)
      apply decCall_avoids_on glo_divMnuPostIte fb_nlz32 _ (by decide)
      apply seq_step_on
        (Q := fun s => DivMnuPostIte s ∧ ∃ wn : BitVec 64,
          s.locals.lookup (ofString "n") = some (.val (.word wn)) ∧
          s.locals.lookup (ofString "i") = some (.val (.word (wn - 1#64))))
      · exact fun s hc hP => straightOn _ rfl s hc hP.1
      · intro F s _ ⟨hg, wm, wn, hm, hn, hn1, hnm, hm16⟩ hnone
        have he : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
            (.op .sub [.var .local (ofString "n"), .const 1#64]) = some (.val (.word (wn - 1#64))) := by
          simp [evalHOLExact, evalListHOLExact, hn, wordOpHOL, wordOp, valueIsWord, valueWord]
        rw [assign_local_word_none s (ofString "i") _ (wn - 1#64) he hnone]
        refine ⟨glo_divMnuPostIte.congr s _ (guestInv_setVar _ _ s hg) ?_ ⟨hg, wm, wn, hm, hn, hn1, hnm, hm16⟩,
          wn, ?_, ?_⟩
        · intro k hk
          rcases List.mem_cons.mp hk with rfl | hk2
          · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "i" ≠ ofString "m" by decide]
          · simp at hk2; subst hk2
            simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "i" ≠ ofString "n" by decide]
        · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "i" ≠ ofString "n" by decide, hn]
        · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      · apply seq_step_on (Q := DivMnuGe2)
        · exact fun s hc hP => hLoop1.1 s hc hP.1.1
        · intro F s _ ⟨⟨hg, wm, wn, hm, hn, hn1, hnm, hm16⟩, wn', hn', hi'⟩ hnone
          have hwn_eq : wn' = wn := by have := hn'.symm.trans hn; cases this; rfl
          subst wn'
          have hwn_nz : wn.toNat ≠ 0 := by
            intro hz0
            have hw0 : wn = 0#64 := BitVec.eq_of_toNat_eq (by simpa using hz0)
            subst wn
            have hbig : domainBytes + 8 < localWordNat (ofString "i") s := by
              rw [domainBytes_eq]
              simp only [localWordNat, hi']
              decide
            exact hLoop1.2 s hg hbig hnone
          have hge2 : 2 ≤ wn.toNat := by omega
          have hkeep_m := evaluate_avoidsLocal_flowing (ofString "m") _ (by decide) s (Or.inl hnone)
          have hkeep_n := evaluate_avoidsLocal_flowing (ofString "n") _ (by decide) s (Or.inl hnone)
          exact ⟨guestInv_evaluate s _ hg, wm, wn, hkeep_m.trans hm, hkeep_n.trans hn, hge2, hnm, hm16⟩
        · apply seq_avoids_on glo_divMnuGe2 (straightOn _ rfl) (by decide)
          apply seq_avoids_on glo_divMnuGe2 (straightOn _ rfl) (by decide)
          apply seq_avoids_on glo_divMnuGe2 (straightOn _ rfl) (by decide)
          apply seq_avoids_on glo_divMnuGe2
            (while_down_unsigned_guestInv _ (straightOn _ rfl) (by counter_step)) (by decide)
          apply seq_avoids_on glo_divMnuGe2 (straightOn _ rfl) (by decide)
          apply dec_avoids_on glo_divMnuGe2 _ (by decide)
          apply dec_avoids_on glo_divMnuGe2 _ (by decide)
          apply seq_step_on (Q := locCapInv "j" 15)
          · exact fun s hc hP => straightOn _ rfl s hc hP.1
          · intro F s _ ⟨hg, wm, wn, hm, hn, hge2, hnm, hm16⟩ hnone
            have he : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
                (.op .add [.op .sub [.var .local (ofString "m"), .var .local (ofString "n")], .const 1#64]) =
                some (.val (.word (wm - wn + 1#64))) := by
              simp [evalHOLExact, evalListHOLExact, hm, hn, wordOpHOL, wordOp, valueIsWord, valueWord]
            rw [assign_local_word_none s (ofString "j") _ (wm - wn + 1#64) he hnone]
            refine ⟨guestInv_setVar _ _ s hg, ?_⟩
            rw [locN_setVar_self]
            have hval : (wm - wn + 1#64).toNat = wm.toNat - wn.toNat + 1 := by
              have hsub : (wm - wn).toNat = wm.toNat - wn.toNat := by
                rw [BitVec.toNat_sub]
                have := wm.isLt; have := wn.isLt
                omega
              rw [BitVec.toNat_add, hsub]
              change (wm.toNat - wn.toNat + 1) % 18446744073709551616 = wm.toNat - wn.toNat + 1
              omega
            omega
          · apply seq_to_guestInv (fun _ h => h.1)
            · apply while_down_first_capped_on .lower (Or.inr rfl) "j"
              · apply dec_guestInv
                apply dec_guestInv
                apply dec_guestInv
                apply dec_guestInv
                apply dec_guestInv
                apply TerminatingProgBoundedOn.seq_guestInv
                · fb_auto
                · apply dec_guestInv
                  apply TerminatingProgBoundedOn.seq_guestInv
                  · exact divisionCorrection_bound_guestInv
                  · fb_auto
              · decide
            · fb_auto
  · rw [domainBytes_eq]
    unfold K.«divmnu» K.«div64by32» K.«nlz32»
    simp only [nat_max_eq]
    decide

/-! ### 7. Guarded bound on `digits_divmod` (`m ≤ 16`) and unconditional `fb_u256_divmod` / `fb_u256_mod` -/

def DigitsDivModGuard : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => GuestInv s ∧ locN s "m" ≤ 16

theorem glo_digitsDivModGuard : GuestLocalsOnly ["m"] DigitsDivModGuard where
  toGuest := fun _ h => h.1
  congr := fun _ _ hg hkeep ⟨_, hm16⟩ => by
    refine ⟨hg, ?_⟩
    have hk := hkeep "m" (by simp)
    simpa [locN, hk] using hm16

def DigitsDivModAfterN : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => GuestInv s ∧ locN s "m" ≤ 16 ∧
    ∃ wn : BitVec 64, s.locals.lookup (ofString "n") = some (.val (.word wn)) ∧ wn.toNat ≤ 8

theorem glo_digitsDivModAfterN : GuestLocalsOnly ["m", "n"] DigitsDivModAfterN where
  toGuest := fun _ h => h.1
  congr := fun _ _ hg hkeep ⟨_, hm16, wn, hn, hn8⟩ => by
    refine ⟨hg, ?_, wn, (hkeep "n" (by simp)).trans hn, hn8⟩
    have hk := hkeep "m" (by simp)
    simpa [locN, hk] using hm16

def DigitsDivModAfterMM : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => GuestInv s ∧
    ∃ wmm wn : BitVec 64,
      s.locals.lookup (ofString "mm") = some (.val (.word wmm)) ∧
      s.locals.lookup (ofString "n") = some (.val (.word wn)) ∧
      wmm.toNat ≤ 16 ∧ wn.toNat ≤ 8

theorem glo_digitsDivModAfterMM : GuestLocalsOnly ["mm", "n"] DigitsDivModAfterMM where
  toGuest := fun _ h => h.1
  congr := fun _ _ hg hkeep ⟨_, wmm, wn, hmm, hn, hmm16, hn8⟩ =>
    ⟨hg, wmm, wn, (hkeep "mm" (by simp)).trans hmm, (hkeep "n" (by simp)).trans hn, hmm16, hn8⟩

def DigitsDivModReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => GuestInv s ∧
    ∃ wmm wn : BitVec 64,
      s.locals.lookup (ofString "mm") = some (.val (.word wmm)) ∧
      s.locals.lookup (ofString "n") = some (.val (.word wn)) ∧
      wn.toNat ≤ wmm.toNat ∧ wmm.toNat ≤ 16

theorem glo_digitsDivModReady : GuestLocalsOnly ["mm", "n"] DigitsDivModReady where
  toGuest := fun _ h => h.1
  congr := fun _ _ hg hkeep ⟨_, wmm, wn, hmm, hn, hle, hmm16⟩ =>
    ⟨hg, wmm, wn, (hkeep "mm" (by simp)).trans hmm, (hkeep "n" (by simp)).trans hn, hle, hmm16⟩

private theorem lookup_digits_len_spec :
    originalRuntimeCode.lookup (ofString "digits_len") =
      some ([(ofString "p", .one), (ofString "n", .one)], digitsLenBody, .one) :=
  lookup_of_guestAst_getElem 66 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_digits_len) rfl

private theorem pan_two_arg_lookup' {width : Nat} [NeZero width]
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (name first second : MlS) (ps1 ps2 rs : ShapeHOL) (body : ProgHOL width) (v1 v2 : ValueHOL width)
    (different : first ≠ second)
    (hshape1 : shapeEqHOL ps1 (shapeOfHOLExact v1) = true)
    (hshape2 : shapeEqHOL ps2 (shapeOfHOLExact v2) = true)
    (lookup : code name = some ([(first, ps1), (second, ps2)], body, rs)) :
    PanSemStateFiniteExact.lookupCodeHOLFinite code name [v1, v2] =
      some (body, (HolFiniteMapExact.empty.update (first, v1)).update (second, v2), rs) := by
  have raw : lookupCodeHOLExact code name [v1, v2] =
      some (body, (fun key => if key = second then some v2 else if key = first then some v1 else none), rs) := by
    simp [lookupCodeHOLExact, lookup, hshape1, hshape2, different]
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite
  split
  · rename_i missing; rw [raw] at missing; cases missing
  · rename_i foundBody foundLocals foundShape found
    have equal := Option.some.inj (found.symm.trans raw)
    obtain ⟨rfl, rest⟩ := Prod.mk.inj equal
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj rest
    apply congrArg (fun locals => some (foundBody, locals, foundShape))
    apply HolFiniteMapExact.ext
    funext key
    by_cases two : key = second
    · subst two; simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty]
    · have backTwo : second ≠ key := Ne.symm two
      by_cases one : key = first
      · subst one; simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, different, Ne.symm different]
      · have backOne : first ≠ key := Ne.symm one
        simp [one, two, backOne, backTwo, HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty]

private theorem two_arg_lookup_digits_len
    {v1 v2 : ValueHOL 64} {body' : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {ret' : ShapeHOL}
    (hl : PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup
      (ofString "digits_len") [v1, v2] = some (body', callee, ret')) :
    body' = digitsLenBody ∧
      callee.lookup (ofString "n") = some v2 := by
  have hdiff : ofString "p" ≠ ofString "n" := by decide
  have hshapes : shapeEqHOL .one (shapeOfHOLExact v1) = true ∧ shapeEqHOL .one (shapeOfHOLExact v2) = true := by
    unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hl
    split at hl
    · cases hl
    · rename_i _ _ _ raw
      simp [lookupCodeHOLExact, lookup_digits_len_spec, hdiff] at raw
      exact ⟨raw.1.1, raw.1.2⟩
  rw [pan_two_arg_lookup' originalRuntimeCode.lookup (ofString "digits_len")
    (ofString "p") (ofString "n") .one .one .one digitsLenBody v1 v2 hdiff
    hshapes.1 hshapes.2 lookup_digits_len_spec] at hl
  cases hl
  refine ⟨rfl, ?_⟩
  simp [HolFiniteMapExact.lookup_update, FUPDATE]

private theorem two_args_eval_eq {F : Type} (s : PanSemStateFiniteExact 64 F)
    (a b : ExpHOL 64) (vals : List (ValueHOL 64))
    (h : evalListHOLFinite s (h := fun x => Classical.propDecidable (s.memaddrs x)) [a, b] = some vals) :
    ∃ va vb, evalAt s a = some va ∧ evalAt s b = some vb ∧ vals = [va, vb] := by
  cases ha : evalAt s a with
  | none => simp [evalListHOLFinite, evalListHOLExact, ha] at h
  | some va =>
    cases hb : evalAt s b with
    | none => simp [evalListHOLFinite, evalListHOLExact, ha, hb] at h
    | some vb =>
      refine ⟨va, vb, rfl, rfl, ?_⟩
      simpa [evalListHOLFinite, evalListHOLExact, ha, hb] using h.symm

private theorem lookup_divmnu_spec :
    originalRuntimeCode.lookup (ofString "divmnu") =
      some ([(ofString "q", .one), (ofString "r", .one), (ofString "u", .one),
             (ofString "m", .one), (ofString "v", .one), (ofString "n", .one)],
            InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
              (extractFn Guest.Software.guestFn_divmnu).body, .one) :=
  lookup_of_guestAst_getElem 67 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_divmnu) rfl

private theorem six_arg_lookup_divmnu
    {vq vr vu vm vv vn : ValueHOL 64} {body' : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {ret' : ShapeHOL}
    (hl : PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup
      (ofString "divmnu") [vq, vr, vu, vm, vv, vn] = some (body', callee, ret')) :
    callee.lookup (ofString "m") = some vm ∧
    callee.lookup (ofString "n") = some vn := by
  have hraw := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some _ _ _ _ _ _ hl
  simp only [lookupCodeHOLExact, lookup_divmnu_spec] at hraw
  split at hraw
  · have hfn : callee.lookup = _ := (Prod.mk.inj (Prod.mk.inj (Option.some.inj hraw)).2).1.symm
    have hm := congrFun hfn (ofString "m")
    have hn := congrFun hfn (ofString "n")
    refine ⟨?_, ?_⟩
    · simpa [FUPDATE_LIST, FUPDATE,
        show ofString "m" ≠ ofString "n" by decide,
        show ofString "m" ≠ ofString "v" by decide] using hm
    · simpa [FUPDATE_LIST, FUPDATE] using hn
  · cases hraw

private theorem six_args_eval_eq {F : Type} (s : PanSemStateFiniteExact 64 F)
    (e1 e2 e3 e4 e5 e6 : ExpHOL 64) (vals : List (ValueHOL 64))
    (h : evalListHOLFinite s (h := fun x => Classical.propDecidable (s.memaddrs x))
      [e1, e2, e3, e4, e5, e6] = some vals) :
    ∃ v1 v2 v3 v4 v5 v6,
      evalAt s e4 = some v4 ∧ evalAt s e6 = some v6 ∧
      vals = [v1, v2, v3, v4, v5, v6] := by
  rcases h1 : evalAt s e1 with _ | v1; · simp [evalListHOLFinite, evalListHOLExact, h1] at h
  rcases h2 : evalAt s e2 with _ | v2; · simp [evalListHOLFinite, evalListHOLExact, h1, h2] at h
  rcases h3 : evalAt s e3 with _ | v3; · simp [evalListHOLFinite, evalListHOLExact, h1, h2, h3] at h
  rcases h4 : evalAt s e4 with _ | v4; · simp [evalListHOLFinite, evalListHOLExact, h1, h2, h3, h4] at h
  rcases h5 : evalAt s e5 with _ | v5; · simp [evalListHOLFinite, evalListHOLExact, h1, h2, h3, h4, h5] at h
  rcases h6 : evalAt s e6 with _ | v6; · simp [evalListHOLFinite, evalListHOLExact, h1, h2, h3, h4, h5, h6] at h
  refine ⟨v1, v2, v3, v4, v5, v6, rfl, rfl, ?_⟩
  simpa [evalListHOLFinite, evalListHOLExact, h1, h2, h3, h4, h5, h6] using h.symm

private theorem three_args_eval_eq {F : Type} (s : PanSemStateFiniteExact 64 F)
    (e1 e2 e3 : ExpHOL 64) (vals : List (ValueHOL 64))
    (h : evalListHOLFinite s (h := fun x => Classical.propDecidable (s.memaddrs x))
      [e1, e2, e3] = some vals) :
    ∃ v1 v2 v3, evalAt s e2 = some v2 ∧ vals = [v1, v2, v3] := by
  rcases h1 : evalAt s e1 with _ | v1; · simp [evalListHOLFinite, evalListHOLExact, h1] at h
  rcases h2 : evalAt s e2 with _ | v2; · simp [evalListHOLFinite, evalListHOLExact, h1, h2] at h
  rcases h3 : evalAt s e3 with _ | v3; · simp [evalListHOLFinite, evalListHOLExact, h1, h2, h3] at h
  refine ⟨v1, v2, v3, rfl, ?_⟩
  simpa [evalListHOLFinite, evalListHOLExact, h1, h2, h3] using h.symm

theorem fb_digits_divmod_guarded :
    TerminatingFunBoundedOn DigitsDivModGuard (ofString "digits_divmod") K.«digits_divmod» := by
  have _ := fb_u256_to_digits
  have _ := fb_digits_len
  have _ := fb_digits_to_u256
  refine ⟨_, _, _, lookup_of_guestAst_getElem 68 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_digits_divmod) rfl, ?_⟩
  dsimp only [extractFn, Guest.Software.guestFn_digits_divmod,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  apply TerminatingProgBoundedOn.weaken'
  · apply dec_avoids_on glo_digitsDivModGuard _ (by decide)
    apply dec_avoids_on glo_digitsDivModGuard _ (by decide)
    apply dec_avoids_on glo_digitsDivModGuard _ (by decide)
    apply seq_avoids_on glo_digitsDivModGuard (call_guestInv' fb_u256_to_digits) (by decide)
    apply TerminatingProgBoundedOn.decCall_on (Q := DigitsDivModAfterN) fb_digits_len
    · exact fun s _ _ callee _ _ hP _ _ => guestInv_callEntry s callee hP.1
    · intro F s values body' callee _ value post hcode ⟨hg, hm16⟩ hargs hl hrun
      obtain ⟨vp, vn_arg, _, hvn, rfl⟩ := two_args_eval_eq s _ _ values hargs
      have hvn_eq : vn_arg = .val (.word 8#64) := by simpa [evalAt, evalHOLExact] using hvn.symm
      subst hvn_eq
      rw [hcode] at hl
      obtain ⟨rfl, hcn⟩ := two_arg_lookup_digits_len hl
      have hle8 : locN (callEntryStateHOLFinite s callee) "n" ≤ 8 := by
        simp [locN, callEntryStateHOLFinite, hcn]
      obtain ⟨wn, rfl, hwn8⟩ := digits_len_ret_le (callEntryStateHOLFinite s callee) post 8 value hle8 hrun
      have hpostG : GuestInv post := by
        have := guestInv_evaluate (callEntryStateHOLFinite s callee) digitsLenBody (guestInv_callEntry s callee hg)
        rw [hrun] at this; exact this
      refine ⟨guestInv_setVar _ _ _ (guestInv_with_locals_clock post s.locals post.clock hpostG), ?_, wn, ?_, hwn8⟩
      · have hne : (ofString "n" == ofString "m") = false := by decide
        simpa [locN, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne] using hm16
      · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    · apply TerminatingProgBoundedOn.decCall_on (Q := DigitsDivModAfterMM) fb_digits_len
      · exact fun s _ _ callee _ _ hP _ _ => guestInv_callEntry s callee hP.1
      · intro F s values body' callee _ value post hcode ⟨hg, hm16, wn, hn, hn8⟩ hargs hl hrun
        obtain ⟨vu, vm_arg, _, hvm, rfl⟩ := two_args_eval_eq s _ _ values hargs
        rw [hcode] at hl
        obtain ⟨rfl, hcm⟩ := two_arg_lookup_digits_len hl
        have hle16 : locN (callEntryStateHOLFinite s callee) "n" ≤ 16 := by
          simp only [locN, callEntryStateHOLFinite, hcm]
          cases hlm : s.locals.lookup (ofString "m") with
          | none => simp [evalAt, evalHOLExact, hlm] at hvm
          | some valm =>
            have eqv : valm = vm_arg := by simpa [evalAt, evalHOLExact, hlm] using hvm
            subst eqv
            simpa [locN, hlm] using hm16
        obtain ⟨wmm, rfl, hwmm16⟩ := digits_len_ret_le (callEntryStateHOLFinite s callee) post 16 value hle16 hrun
        have hpostG : GuestInv post := by
          have := guestInv_evaluate (callEntryStateHOLFinite s callee) digitsLenBody (guestInv_callEntry s callee hg)
          rw [hrun] at this; exact this
        refine ⟨guestInv_setVar _ _ _ (guestInv_with_locals_clock post s.locals post.clock hpostG), wmm, wn, ?_, ?_, hwmm16, hn8⟩
        · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        · have hne : (ofString "mm" == ofString "n") = false := by decide
          simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hn]
      · apply dec_avoids_on glo_digitsDivModAfterMM _ (by decide)
        apply seq_avoids_on glo_digitsDivModAfterMM
          (while_up_unsigned_const_guestInv _ 16 (straightOn _ rfl) (by counter_step)) (by decide)
        apply seq_step_on (Q := DigitsDivModReady)
        · exact TerminatingProgBoundedOn.ite_on
            (fun s hc hP => TerminatingProgBoundedOn.tailCall_guestInv fb_digits_to_u256 _ s hc hP.1)
            (fun s hc hP => straightOn _ rfl s hc hP.1)
        · intro F s _ ⟨hg, wmm, wn, hmm, hn, hmm16, _⟩ hnone
          rw [evaluateHOLFiniteState_ite] at hnone ⊢
          have hcond : @evalHOLExact 64 _ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
              (.cmp .lower (.var .local (ofString "mm")) (.var .local (ofString "n"))) =
              some (.val (.word (if decide (wmm < wn) then 1#64 else 0#64))) := by
            simp [evalHOLExact, hmm, hn, wordCmpHOL]
          rw [hcond] at hnone ⊢
          by_cases hlt : wmm < wn
          · simp only [decide_eq_true hlt, ↓reduceIte, show ¬ ((1#64 : BitVec 64) = 0) by decide] at hnone
            exact absurd hnone (noFallthrough_tailCall _ _ s)
          · simp only [decide_eq_false hlt, Bool.false_eq_true, ↓reduceIte] at hnone ⊢
            rw [evaluateHOLFiniteState_skip]
            have hge : wn.toNat ≤ wmm.toNat := by
              rw [BitVec.lt_def] at hlt; omega
            exact ⟨hg, wmm, wn, hmm, hn, hge, hmm16⟩
        · apply seq_avoids_on glo_digitsDivModReady (straightOn _ rfl) (by decide)
          apply seq_avoids_on glo_digitsDivModReady
            (while_up_unsigned_const_guestInv _ 8 (straightOn _ rfl) (by counter_step)) (by decide)
          apply seq_to_guestInv (fun _ h => h.1)
          · apply TerminatingProgBoundedOn.call_on fb_divmnu_guarded
            intro F s values _ callee _ hcode ⟨hg, wmm, wn, hmm, hn, hle, hmm16⟩ hargs hl
            obtain ⟨_, _, _, v4, _, v6, hv4, hv6, rfl⟩ := six_args_eval_eq s _ _ _ _ _ _ values hargs
            have hv4_eq : v4 = .val (.word wmm) := by simpa [evalAt, evalHOLExact, hmm] using hv4.symm
            have hv6_eq : v6 = .val (.word wn) := by simpa [evalAt, evalHOLExact, hn] using hv6.symm
            subst hv4_eq; subst hv6_eq
            rw [hcode] at hl
            obtain ⟨hcm, hcn⟩ := six_arg_lookup_divmnu hl
            exact ⟨guestInv_callEntry s callee hg, wmm, wn, hcm, hcn, hle, hmm16⟩
          · exact TerminatingProgBoundedOn.tailCall_guestInv fb_digits_to_u256 _
  · have h16 : (16 : BitVec 64).toNat = 16 := by decide
    have h8 : (8 : BitVec 64).toNat = 8 := by decide
    rw [h16, h8]
    unfold K.«digits_divmod»
    generalize_K
    simp only [nat_max_eq]
    omega

private theorem lookup_digits_divmod_spec :
    originalRuntimeCode.lookup (ofString "digits_divmod") =
      some ([(ofString "u", .one), (ofString "m", .one), (ofString "d", .comb [.one, .one, .one, .one])],
            InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
              (extractFn Guest.Software.guestFn_digits_divmod).body,
            .comb [.one, .one, .one, .one]) :=
  lookup_of_guestAst_getElem 68 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_digits_divmod) rfl

private theorem three_arg_lookup_digits_divmod
    {vu vm vd : ValueHOL 64} {body' : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {ret' : ShapeHOL}
    (hl : PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup
      (ofString "digits_divmod") [vu, vm, vd] = some (body', callee, ret')) :
    callee.lookup (ofString "m") = some vm := by
  have hraw := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some _ _ _ _ _ _ hl
  simp only [lookupCodeHOLExact, lookup_digits_divmod_spec] at hraw
  split at hraw
  · have hfn : callee.lookup = _ := (Prod.mk.inj (Prod.mk.inj (Option.some.inj hraw)).2).1.symm
    have hm := congrFun hfn (ofString "m")
    simpa [FUPDATE_LIST, FUPDATE,
      show ofString "m" ≠ ofString "d" by decide] using hm
  · cases hraw

theorem fb_u256_divmod : TerminatingFunBoundedOn GuestInv (ofString "u256_divmod") K.«u256_divmod» := by
  have _ := fb_u256_lt
  have _ := fb_udivmod
  have _ := fb_u256_to_digits
  have _ := fb_digits_to_u256
  fb_unfold 69 Guest.Software.guestFn_u256_divmod
  apply TerminatingProgBoundedOn.weaken'
  · apply TerminatingProgBoundedOn.seq_guestInv
    · exact TerminatingProgBoundedOn.ite_on (straightOn _ rfl) (straightOn _ rfl)
    · apply decCall_guestInv' fb_u256_lt
      apply TerminatingProgBoundedOn.seq_guestInv
      · exact TerminatingProgBoundedOn.ite_on (straightOn _ rfl) (straightOn _ rfl)
      · apply TerminatingProgBoundedOn.seq_guestInv
        · exact TerminatingProgBoundedOn.ite_on
            (decCall_guestInv' fb_udivmod (straightOn _ rfl))
            (straightOn _ rfl)
        · apply dec_guestInv
          apply TerminatingProgBoundedOn.seq_guestInv
          · exact call_guestInv' fb_u256_to_digits
          · apply TerminatingProgBoundedOn.decCall_on (Q := GuestInv) fb_digits_divmod_guarded
            · intro F s values _ callee _ hcode hg hargs hl
              obtain ⟨_, v2, _, hv2, rfl⟩ := three_args_eval_eq s _ _ _ values hargs
              have hv2_eq : v2 = .val (.word 8#64) := by simpa [evalAt, evalHOLExact] using hv2.symm
              subst hv2_eq
              rw [hcode] at hl
              have hcm := three_arg_lookup_digits_divmod hl
              refine ⟨guestInv_callEntry s callee hg, ?_⟩
              simp [locN, callEntryStateHOLFinite, hcm]
            · intro F s _ body' callee _ value post _ hg _ _ hrun
              have hpostG : GuestInv post := by
                have := guestInv_evaluate (callEntryStateHOLFinite s callee) body' (guestInv_callEntry s callee hg)
                rw [hrun] at this; exact this
              exact guestInv_setVar _ value _ (guestInv_with_locals_clock post s.locals post.clock hpostG)
            · exact decCall_guestInv' fb_digits_to_u256 (straightOn _ rfl)
  · fb_arith K.«u256_divmod»

theorem fb_u256_mod : TerminatingFunBoundedOn GuestInv (ofString "u256_mod") K.«u256_mod» := by
  have _ := fb_u256_divmod
  fb_prove 71 Guest.Software.guestFn_u256_mod K.«u256_mod»

end InitECandidate.Solver.Wave8GuestInv.P13.DivMod
