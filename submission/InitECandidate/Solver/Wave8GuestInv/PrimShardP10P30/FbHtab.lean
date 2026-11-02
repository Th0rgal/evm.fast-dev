import InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30.FbCore

/-! Hash-table and storage `fb_*` bounds for `PrimShardP10P30` on R11 (`GuestInv`), including
`fb_htab_set`, `fb_warm_storage_key`, and `fb_destroy_storage`. -/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup

/-! ### Local frames & `while_noRepeat` (`htab_find_leaf`) -/

def LocFrame {F : Type} (s t : PanSemStateFiniteExact 64 F) : Prop :=
  t = { s with locals := t.locals, clock := t.clock }

theorem LocFrame.refl {F : Type} (s : PanSemStateFiniteExact 64 F) : LocFrame s s := by
  cases s; rfl

theorem LocFrame.trans {F : Type} {s t u : PanSemStateFiniteExact 64 F}
    (h1 : LocFrame s t) (h2 : LocFrame t u) : LocFrame s u := by
  unfold LocFrame at *; rw [h2]; rw [h1]

def locOnly : ProgHOL 64 → Bool
  | .dec _ _ _ body => locOnly body
  | .seq first second => locOnly first && locOnly second
  | .ite _ yes no => locOnly yes && locOnly no
  | .assign .local _ _ => true
  | .skip | .break | .continue | .annot _ _ | .raise _ _ | .return _ => true
  | _ => false

theorem locFrame_eval {F : Type} : ∀ (p : ProgHOL 64), locOnly p = true →
    ∀ (s : PanSemStateFiniteExact 64 F), LocFrame s (evaluateHOLFiniteState s p).2
  | .skip, _, s => by rw [evaluateHOLFiniteState_skip]; exact LocFrame.refl s
  | .break, _, s => by rw [evaluateHOLFiniteState_break]; exact LocFrame.refl s
  | .continue, _, s => by rw [evaluateHOLFiniteState_continue]; exact LocFrame.refl s
  | .annot _ _, _, s => by rw [evaluateHOLFiniteState_annot]; exact LocFrame.refl s
  | .raise _ _, _, s => by
    rw [evaluateHOLFiniteState_raise]; split
    · dsimp only; split
      · rfl
      · exact LocFrame.refl s
    · exact LocFrame.refl s
  | .return _, _, s => by
    rw [evaluateHOLFiniteState_return]; split
    · exact LocFrame.refl s
    · split
      · rfl
      · exact LocFrame.refl s
  | .assign kind name e, h, s => by
    cases kind with
    | global => simp [locOnly] at h
    | «local» =>
      rw [evaluateHOLFiniteState_assign]; split
      · exact LocFrame.refl s
      · split
        · rfl
        · exact LocFrame.refl s
  | .dec name sh init body, h, s => by
    have hb : locOnly body = true := by simpa [locOnly] using h
    rw [evaluateHOLFiniteState_dec_total]; dsimp only; split
    · exact LocFrame.refl s
    · rename_i val _; split
      · have ih := locFrame_eval body hb (setVarHOLFinite name val s)
        unfold LocFrame at ih ⊢; dsimp only; rw [ih]; rfl
      · exact LocFrame.refl s
  | .seq first second, h, s => by
    have h12 : locOnly first = true ∧ locOnly second = true := by
      simpa [locOnly, Bool.and_eq_true] using h
    rw [evaluateHOLFiniteState_seq_line780]
    have ih1 := locFrame_eval first h12.1 s
    rcases hr1 : evaluateHOLFiniteState s first with ⟨r1, mid⟩
    rw [hr1] at ih1; dsimp only at ih1 ⊢
    cases r1 with
    | none => exact ih1.trans (locFrame_eval second h12.2 mid)
    | some _ => exact ih1
  | .ite cond yes no, h, s => by
    have h12 : locOnly yes = true ∧ locOnly no = true := by
      simpa [locOnly, Bool.and_eq_true] using h
    rw [evaluateHOLFiniteState_ite]; split
    · split
      · exact locFrame_eval no h12.2 s
      · exact locFrame_eval yes h12.1 s
    · exact LocFrame.refl s
  | .while _ _, h, _ => by simp [locOnly] at h
  | .call _ _ _, h, _ => by simp [locOnly] at h
  | .decCall _ _ _ _ _, h, _ => by simp [locOnly] at h
  | .store _ _, h, _ => by simp [locOnly] at h
  | .storeByte _ _, h, _ => by simp [locOnly] at h
  | .store32 _ _, h, _ => by simp [locOnly] at h
  | .tick, h, _ => by simp [locOnly] at h
  | .primitive _ _ _, h, _ => by simp [locOnly] at h
  | .extCall _ _ _ _ _, h, _ => by simp [locOnly] at h
  | .shMemLoad _ _ _ _, h, _ => by simp [locOnly] at h
  | .shMemStore _ _ _, h, _ => by simp [locOnly] at h

theorem locals_ext {m1 m2 : HolFiniteMapExact MlS (ValueHOL 64)}
    (h : ∀ k, m1.lookup k = m2.lookup k) : m1 = m2 := by
  cases m1; cases m2
  simp only [HolFiniteMapExact.mk.injEq]
  exact funext h

theorem beq_false_of_ne {a b : MlS} (h : b ≠ a) : (a == b) = false := by
  simp only [beq_eq_false_iff_ne]; exact fun e => h e.symm

section NoRepeat

variable (P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
  (R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F → Prop)
  {N : Nat} (κ : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Fin N)
  (condition : ExpHOL 64) (body : ProgHOL 64) (B : Nat)

structure NoRepeatLoop : Prop where
  body_bound : TerminatingProgBoundedOn Q body B
  entry : ∀ {F : Type} (state : PanSemStateFiniteExact 64 F) (word : BitVec 64),
    state.code = originalRuntimeCode → P state →
    evalHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      condition = some (.val (.word word)) →
    word ≠ 0 → state.clock ≠ 0 → Q (decClockHOLFinite state)
  step : ∀ {F : Type} (state : PanSemStateFiniteExact 64 F) (word : BitVec 64),
    state.code = originalRuntimeCode → P state →
    evalHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      condition = some (.val (.word word)) →
    word ≠ 0 → state.clock ≠ 0 →
    let output := evaluateHOLFiniteState (decClockHOLFinite state) body
    output.1 ≠ some .timeOut → (output.1 = none ∨ output.1 = some .continue) →
      P output.2 ∧ R state output.2
  trans : ∀ {F : Type} (a b c : PanSemStateFiniteExact 64 F), R a b → R b c → R a c
  key : ∀ {F : Type} (a b : PanSemStateFiniteExact 64 F), R a b →
    LoopActive condition a → LoopActive condition b → κ a = κ b →
    b = { a with clock := b.clock }

variable {P Q R κ condition body B}

def VisitedHeads (R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F → Prop)
    (κ : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Fin N) (condition : ExpHOL 64)
    (body : ProgHOL 64) {F : Type} (state : PanSemStateFiniteExact 64 F)
    (visited : Finset (Fin N)) : Prop :=
  ∀ k ∈ visited, ∃ earlier : PanSemStateFiniteExact 64 F, κ earlier = k ∧ R earlier state ∧
    LoopActive condition earlier ∧ state.clock < earlier.clock ∧
    evaluateHOLFiniteState earlier (.while condition body) =
      evaluateHOLFiniteState state (.while condition body)

theorem key_fresh (hloop : NoRepeatLoop P Q R κ condition body B)
    {F : Type} (state : PanSemStateFiniteExact 64 F) (visited : Finset (Fin N))
    (hact : LoopActive condition state) (hvis : VisitedHeads R κ condition body state visited)
    (hnt : (evaluateHOLFiniteState state (.while condition body)).1 ≠ some .timeOut) :
    κ state ∉ visited := by
  intro hmem
  obtain ⟨earlier, hk, hR, hactE, hlt, hsame⟩ := hvis _ hmem
  have heq := hloop.key earlier state hR hactE hact hk
  exact evaluate_ne_of_clock_lt _ state earlier (by rw [heq]) hlt hsame hnt

theorem card_insert_key_le {F : Type} (κ : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Fin N)
    (state : PanSemStateFiniteExact 64 F) (visited : Finset (Fin N)) (hfresh : κ state ∉ visited) :
    visited.card + 1 ≤ N := by
  have hle : (insert (κ state) visited).card ≤ N := by
    simpa using Finset.card_le_univ (insert (κ state) visited)
  rwa [Finset.card_insert_of_notMem hfresh] at hle

theorem while_noRepeat_aux (hloop : NoRepeatLoop P Q R κ condition body B) :
    ∀ (n : Nat) {F : Type} (state : PanSemStateFiniteExact 64 F) (visited : Finset (Fin N)),
      state.code = originalRuntimeCode → P state → N ≤ visited.card + n →
      VisitedHeads R κ condition body state visited →
      TerminatingRunBounded state (.while condition body) (n * (B + 1)) := by
  intro n
  induction n with
  | zero =>
    intro F state visited hcode hP hcard hvis hnt
    have hnt0 := hnt
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnt ⊢
    split
    · rename_i word hword
      simp only [hword] at hnt
      by_cases hzero : word = 0
      · rw [if_neg (by simp [hzero])]; exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
      · have hfresh := key_fresh hloop state visited ⟨word, hword, hzero⟩ hvis hnt0
        have := card_insert_key_le κ state visited hfresh
        omega
    · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
  | succ n ih =>
    intro F state visited hcode hP hcard hvis hnt
    have hnt0 := hnt
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnt ⊢
    split
    · rename_i word hword
      simp only [hword] at hnt
      by_cases hzero : word = 0
      · rw [if_neg (by simp [hzero])]; exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
      · rw [if_pos hzero] at hnt ⊢
        by_cases hclock : state.clock = 0
        · rw [if_pos hclock] at hnt; exact absurd rfl hnt
        · rw [if_neg hclock] at hnt ⊢
          have hact : LoopActive condition state := ⟨word, hword, hzero⟩
          have hfresh := key_fresh hloop state visited hact hvis hnt0
          have hQ := hloop.entry state word hcode hP hword hzero hclock
          have hb := hloop.body_bound (decClockHOLFinite state) hcode hQ
          have hstep := hloop.step state word hcode hP hword hzero hclock
          have hunfold := while_unfold_continue condition body state word hword hzero hclock
          have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata
            (decClockHOLFinite state) body).1
          unfold TerminatingRunBounded at hb
          rcases hrun : evaluateHOLFiniteState (decClockHOLFinite state) body with ⟨result, post⟩
          simp only [hrun] at hnt hb hstep hunfold hmeta
          dsimp only at hb hstep hunfold hmeta hnt ⊢
          change post.code = state.code at hmeta
          have hcont (hflow : result = none ∨ result = some .continue) :
              state.clock ≤ (evaluateHOLFiniteState post (.while condition body)).2.clock +
                (n + 1) * (B + 1) ∧
              (evaluateHOLFiniteState post (.while condition body)).2.clock ≤ state.clock := by
            have hsafe : result ≠ some .timeOut := by
              rcases hflow with h | h <;> simp [h]
            obtain ⟨hspent, hkept⟩ := hb hsafe
            change state.clock - 1 ≤ post.clock + B at hspent
            change post.clock ≤ state.clock - 1 at hkept
            obtain ⟨hPpost, hRpost⟩ := hstep hsafe hflow
            have hsame := hunfold hflow
            have hntPost : (evaluateHOLFiniteState post (.while condition body)).1 ≠
                some .timeOut := by
              rw [← hsame]; exact hnt0
            obtain ⟨htail, htailKept⟩ := ih post (insert (κ state) visited)
              (hmeta.trans hcode) hPpost
              (by rw [Finset.card_insert_of_notMem hfresh]; omega)
              (by
                intro k hk
                rcases Finset.mem_insert.mp hk with rfl | hk
                · exact ⟨state, rfl, hRpost, hact, by omega, hsame⟩
                · obtain ⟨earlier, hke, hRe, hactE, hlt, hsameE⟩ := hvis k hk
                  exact ⟨earlier, hke, hloop.trans _ _ _ hRe hRpost, hactE, by omega,
                    hsameE.trans hsame⟩)
              hntPost
            have hmul : n * (B + 1) + (B + 1) = (n + 1) * (B + 1) := by rw [Nat.succ_mul]
            exact ⟨by omega, by omega⟩
          cases result with
          | none => exact hcont (Or.inl rfl)
          | some r =>
            cases r with
            | «continue» => exact hcont (Or.inr rfl)
            | timeOut => exact absurd rfl hnt
            | _ =>
              obtain ⟨hspent, hkept⟩ := hb (by simp)
              change state.clock - 1 ≤ post.clock + B at hspent
              change post.clock ≤ state.clock - 1 at hkept
              simp only
              have hge : B + 1 ≤ (n + 1) * (B + 1) := Nat.le_mul_of_pos_left _ (Nat.succ_pos n)
              exact ⟨by omega, by omega⟩
    · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩

theorem while_noRepeat (hloop : NoRepeatLoop P Q R κ condition body B) :
    TerminatingProgBoundedOn P (.while condition body) ((N + 1) * (B + 1)) :=
  fun state hcode hP =>
    (while_noRepeat_aux hloop N state ∅ hcode hP (by simp) (by simp [VisitedHeads])).weaken
      (Nat.mul_le_mul_right _ (Nat.le_succ N))

end NoRepeat

def wordKey (x : MlS) {F : Type} (s : PanSemStateFiniteExact 64 F) : Fin (2 ^ 64) :=
  match s.locals.lookup x with
  | some (.val (.word w)) => ⟨w.toNat, w.isLt⟩
  | _ => ⟨0, by decide⟩

def OneWordFrame (x : MlS) {F : Type} (s t : PanSemStateFiniteExact 64 F) : Prop :=
  LocFrame s t ∧ ∀ y, y ≠ x → t.locals.lookup y = s.locals.lookup y

theorem active_cmp_var {F : Type} (op : Cmp) (x : MlS) (e : ExpHOL 64)
    (s : PanSemStateFiniteExact 64 F) (h : LoopActive (.cmp op (.var .local x) e) s) :
    ∃ w, s.locals.lookup x = some (.val (.word w)) := by
  obtain ⟨word, hw, _⟩ := h
  change evalAt s _ = _ at hw
  obtain ⟨a, _, ha, _, _⟩ := evalAt_cmp s op _ e word hw
  simp only [evalAt, evalHOLExact] at ha
  exact ⟨a, by simpa using ha⟩

theorem while_oneWord_guestInv (x : MlS) {condition : ExpHOL 64} {body : ProgHOL 64} {B : Nat}
    (hbody : TerminatingProgBoundedOn GuestInv body B)
    (hloc : locOnly body = true)
    (havoid : ∀ y, y ≠ x → avoidsLocal y body = true)
    (hact : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), LoopActive condition s →
      ∃ w, s.locals.lookup x = some (.val (.word w))) :
    TerminatingProgBoundedOn GuestInv (.while condition body) ((2 ^ 64 + 1) * (B + 1)) := by
  have hloop : NoRepeatLoop GuestInv GuestInv (OneWordFrame x) (wordKey x) condition body B :=
    { body_bound := hbody
      entry := fun s _ _ hPs _ _ _ => guestInv_with_locals_clock s s.locals _ hPs
      step := by
        intro F s _ _ hPs _ _ _ _ _ hflow
        have hfr0 := locFrame_eval body hloc (decClockHOLFinite s)
        have hfr : LocFrame s (evaluateHOLFiniteState (decClockHOLFinite s) body).2 := by
          unfold LocFrame at hfr0 ⊢; rw [hfr0]; rfl
        have hkeep : ∀ y, y ≠ x →
            (evaluateHOLFiniteState (decClockHOLFinite s) body).2.locals.lookup y =
            s.locals.lookup y := fun y hy =>
          evaluate_avoidsLocal_flowing y body (havoid y hy) (decClockHOLFinite s)
            (hflow.elim Or.inl (fun h => Or.inr (Or.inr h)))
        exact ⟨by unfold LocFrame at hfr; rw [hfr]; exact guestInv_with_locals_clock s _ _ hPs,
          hfr, hkeep⟩
      trans := fun a b c hab hbc =>
        ⟨hab.1.trans hbc.1, fun y hy => (hbc.2 y hy).trans (hab.2 y hy)⟩
      key := by
        intro F a b hab hacta hactb hk
        obtain ⟨wa, ha⟩ := hact a hacta
        obtain ⟨wb, hb⟩ := hact b hactb
        simp only [wordKey, ha, hb, Fin.mk.injEq] at hk
        have hl : b.locals = a.locals := locals_ext fun y => by
          by_cases hy : y = x
          · subst hy; rw [ha, hb, BitVec.eq_of_toNat_eq hk]
          · exact hab.2 y hy
        have hfr := hab.1; unfold LocFrame at hfr; rw [hl] at hfr; exact hfr }
  intro F s hc hPs
  exact while_noRepeat hloop s hc hPs

theorem fb_htab_find_leaf :
    TerminatingFunBoundedOn GuestInv (ofString "htab_find_leaf") K.«htab_find_leaf» := by
  fb_unfold 131 Guest.Software.guestFn_htab_find_leaf
  apply TerminatingProgBoundedOn.weaken'
  · apply dec_guestInv; apply dec_guestInv; apply dec_guestInv
    apply TerminatingProgBoundedOn.seq_guestInv
    · refine while_oneWord_guestInv (ofString "n") (straightOn _ rfl) rfl ?_
        (fun s h => active_cmp_var _ _ _ s h)
      intro y hy
      simp [avoidsLocal, Ne.symm hy]
    · exact straightOn _ rfl
  · unfold K.«htab_find_leaf»; omega

theorem fb_htab_get : TerminatingFunBoundedOn GuestInv (ofString "htab_get") K.«htab_get» := by
  fb_prove 132 Guest.Software.guestFn_htab_get K.«htab_get»

theorem fb_htab_has : TerminatingFunBoundedOn GuestInv (ofString "htab_has") K.«htab_has» := by
  fb_prove 133 Guest.Software.guestFn_htab_has K.«htab_has»

theorem fb_htab_del : TerminatingFunBoundedOn GuestInv (ofString "htab_del") K.«htab_del» := by
  fb_prove 139 Guest.Software.guestFn_htab_del K.«htab_del»

theorem fb_jdel : TerminatingFunBoundedOn GuestInv (ofString "jdel") K.«jdel» := by
  fb_prove 357 Guest.Software.guestFn_jdel K.«jdel»

/-! ### `fb_htab_set` (`guestAst[138]`, Target #7): 2-step `ordinaryDomain` cell pigeonhole -/

section HtabSetLoop

def htabSetCond : ExpHOL 64 :=
  .cmp .notEqual (.var .local (ofString "n")) (.const (BitVec.ofNat 64 0))

def htabSetBody : ProgHOL 64 :=
  InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
    (Prog.dec "b" Shape.one (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "nodes"), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "n"), (Exp.const (BitVec.ofNat 64 32))]), (Exp.const (BitVec.ofNat 64 24))]))
      (Prog.seq
        (Prog.ite (Exp.cmp Cmp.notLower (Exp.var VarKind.local "b") (Exp.var VarKind.local "d"))
          Prog.break
          Prog.skip)
        (Prog.seq
          (Prog.assign VarKind.local "p" (Exp.var VarKind.local "n"))
          (Prog.ite (Exp.cmp Cmp.equal (Exp.op BinOp.and [(Exp.shift Shift.lsr (Exp.loadByte (Exp.op BinOp.add [(Exp.var VarKind.local "key"), (Exp.shift Shift.lsr (Exp.var VarKind.local "b") (Exp.const (BitVec.ofNat 64 3)))])) (Exp.op BinOp.sub [(Exp.const (BitVec.ofNat 64 7)), (Exp.op BinOp.and [(Exp.var VarKind.local "b"), (Exp.const (BitVec.ofNat 64 7))])])), (Exp.const (BitVec.ofNat 64 1))]) (Exp.const (BitVec.ofNat 64 0)))
            (Prog.assign VarKind.local "n" (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "nodes"), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "n"), (Exp.const (BitVec.ofNat 64 32))]), (Exp.const (BitVec.ofNat 64 8))])))
            (Prog.assign VarKind.local "n" (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "nodes"), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "n"), (Exp.const (BitVec.ofNat 64 32))]), (Exp.const (BitVec.ofNat 64 16))])))))))

abbrev domainCells : Nat := 3888119741

def htabSetKey {F : Type} (s : PanSemStateFiniteExact 64 F) : Fin domainCells :=
  match s.locals.lookup (ofString "nodes"), s.locals.lookup (ofString "n") with
  | some (.val (.word wnodes)), some (.val (.word wn)) =>
    let addr := wnodes + wn * (BitVec.ofNat 64 32) + (BitVec.ofNat 64 24)
    if h : sourceBase ≤ addr.toNat ∧ addr.toNat + 8 ≤ heapEnd then
      ⟨(addr.toNat - sourceBase) / 8, by
        have e1 : sourceBase = 2701131776 := by decide
        have e2 : heapEnd = 2701131776 + 8 * 3888119741 := by decide
        have e3 : domainCells = 3888119741 := rfl
        omega⟩
    else ⟨0, by decide⟩
  | _, _ => ⟨0, by decide⟩

def BaseFrame {F : Type} (s0 s : PanSemStateFiniteExact 64 F) : Prop :=
  LocFrame s0 s ∧ ∀ z, z ≠ ofString "n" → z ≠ ofString "p" → s.locals.lookup z = s0.locals.lookup z

theorem baseFrame_refl {F : Type} (s0 : PanSemStateFiniteExact 64 F) : BaseFrame s0 s0 :=
  ⟨LocFrame.refl s0, fun _ _ _ => rfl⟩

theorem baseFrame_step {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    (hb : BaseFrame s0 s)
    (hnone : (evaluateHOLFiniteState (decClockHOLFinite s) htabSetBody).1 = none) :
    BaseFrame s0 (evaluateHOLFiniteState (decClockHOLFinite s) htabSetBody).2 := by
  have hfr0 := locFrame_eval htabSetBody rfl (decClockHOLFinite s)
  have hfr : LocFrame s (evaluateHOLFiniteState (decClockHOLFinite s) htabSetBody).2 := by
    unfold LocFrame at hfr0 ⊢; rw [hfr0]; rfl
  refine ⟨hb.1.trans hfr, fun z hzn hzp => ?_⟩
  have hav : avoidsLocal z htabSetBody = true := by
    simp [htabSetBody, InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
      avoidsLocal, beq_false_of_ne hzn, beq_false_of_ne hzp]
  exact (evaluate_avoidsLocal_flowing z htabSetBody hav (decClockHOLFinite s) (Or.inl hnone)).trans
    (hb.2 z hzn hzp)

/-- One flowing step from `a` and `b` with the same `htabSetKey` produces the exact same `n`! -/
theorem htabSet_oneStep_same_n {F : Type} {s0 a b : PanSemStateFiniteExact 64 F}
    (hP0 : GuestInv s0)
    (ha : BaseFrame s0 a) (hb : BaseFrame s0 b)
    (hk : htabSetKey a = htabSetKey b)
    (hna : (evaluateHOLFiniteState (decClockHOLFinite a) htabSetBody).1 = none)
    (hnb : (evaluateHOLFiniteState (decClockHOLFinite b) htabSetBody).1 = none) :
    (evaluateHOLFiniteState (decClockHOLFinite a) htabSetBody).2.locals.lookup (ofString "n") =
    (evaluateHOLFiniteState (decClockHOLFinite b) htabSetBody).2.locals.lookup (ofString "n") := by
  -- Extract `wnodes`, `wna`, `wnb`, and `addr_a ∈ ordinaryDomain`, `addr_b ∈ ordinaryDomain`:
  have hnodes_eq : a.locals.lookup (ofString "nodes") = b.locals.lookup (ofString "nodes") :=
    (ha.2 _ (by decide) (by decide)).trans (hb.2 _ (by decide) (by decide)).symm
  have hd_eq : a.locals.lookup (ofString "d") = b.locals.lookup (ofString "d") :=
    (ha.2 _ (by decide) (by decide)).trans (hb.2 _ (by decide) (by decide)).symm
  have hkey_eq : a.locals.lookup (ofString "key") = b.locals.lookup (ofString "key") :=
    (ha.2 _ (by decide) (by decide)).trans (hb.2 _ (by decide) (by decide)).symm
  -- Unpack `dec "b"` in both `hna` and `hnb`:
  rcases hrun_a : evaluateHOLFiniteState (decClockHOLFinite a) htabSetBody with ⟨ra, pa⟩
  rw [hrun_a] at hna; dsimp only at hna; subst hna
  rcases hrun_b : evaluateHOLFiniteState (decClockHOLFinite b) htabSetBody with ⟨rb, pb⟩
  rw [hrun_b] at hnb; dsimp only at hnb; subst hnb
  unfold htabSetBody at hrun_a hrun_b
  dsimp only [InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map] at hrun_a hrun_b
  rw [evaluateHOLFiniteState_dec_total] at hrun_a hrun_b
  dsimp only at hrun_a hrun_b
  rcases heva : @evalHOLExact 64 F _ (decClockHOLFinite a).toExact
      (fun x => Classical.propDecidable ((decClockHOLFinite a).memaddrs x))
      (.load .one (.op .add [.var .local (ofString "nodes"),
        .panop .mul [.var .local (ofString "n"), .const (BitVec.ofNat 64 32)],
        .const (BitVec.ofNat 64 24)])) with _ | vba
  · rw [heva] at hrun_a; cases hrun_a
  rcases hevb : @evalHOLExact 64 F _ (decClockHOLFinite b).toExact
      (fun x => Classical.propDecidable ((decClockHOLFinite b).memaddrs x))
      (.load .one (.op .add [.var .local (ofString "nodes"),
        .panop .mul [.var .local (ofString "n"), .const (BitVec.ofNat 64 32)],
        .const (BitVec.ofNat 64 24)])) with _ | vbb
  · rw [hevb] at hrun_b; cases hrun_b
  rw [heva] at hrun_a; rw [hevb] at hrun_b; dsimp only at hrun_a hrun_b
  obtain ⟨addra, haddra, hdoma, _⟩ := eval_load_one (decClockHOLFinite a)
    (h := fun x => Classical.propDecidable ((decClockHOLFinite a).memaddrs x)) _ vba heva
  obtain ⟨addrb, haddrb, hdomb, _⟩ := eval_load_one (decClockHOLFinite b)
    (h := fun x => Classical.propDecidable ((decClockHOLFinite b).memaddrs x)) _ vbb hevb
  -- Unpack `nodes` and `n` in `haddra` and `haddrb`:
  have hunpack : ∀ (st : PanSemStateFiniteExact 64 F) (addr : BitVec 64),
      @evalHOLExact 64 F _ (decClockHOLFinite st).toExact
        (fun x => Classical.propDecidable ((decClockHOLFinite st).memaddrs x))
        (.op .add [.var .local (ofString "nodes"),
          .panop .mul [.var .local (ofString "n"), .const (BitVec.ofNat 64 32)],
          .const (BitVec.ofNat 64 24)]) = some (.val (.word addr)) →
      ∃ wnodes wn : BitVec 64,
        st.locals.lookup (ofString "nodes") = some (.val (.word wnodes)) ∧
        st.locals.lookup (ofString "n") = some (.val (.word wn)) ∧
        addr = wnodes + wn * (BitVec.ofNat 64 32) + (BitVec.ofNat 64 24) := by
    intro st addr he
    simp only [evalHOLExact, evalListHOLExact] at he
    rcases h1 : (decClockHOLFinite st).locals.lookup (ofString "nodes") with _ | vn
    · simp [h1] at he
    rcases h2 : (decClockHOLFinite st).locals.lookup (ofString "n") with _ | vm
    · simp [h1, h2] at he
    rcases vn with ⟨⟨wnodes⟩⟩ | _ | _ <;> rcases vm with ⟨⟨wn⟩⟩ | _ | _ <;>
      simp [h1, h2, valueIsWord, panOpHOL] at he
    refine ⟨wnodes, wn, h1, h2, ?_⟩
    simp only [wordOpHOL, wordOp, valueWord, List.foldr, add_zero] at he
    have heq := (Option.some.inj he).symm
    rw [heq, ← BitVec.add_assoc]
  obtain ⟨wnodes, wna, hna_nodes, hna_n, rfl⟩ := hunpack a addra haddra
  obtain ⟨wnodes_b, wnb, hnb_nodes, hnb_n, rfl⟩ := hunpack b addrb haddrb
  have hwn_eq : wnodes_b = wnodes := by
    rw [hnodes_eq] at hna_nodes
    rw [hnb_nodes] at hna_nodes
    injection hna_nodes with h1; injection h1 with h1; injection h1
  subst wnodes_b
  -- Both `addra` and `addrb` are in `ordinaryDomain`!
  have hma_a : (decClockHOLFinite a).memaddrs = ordinaryDomain := by
    have h1 := ha.1; unfold LocFrame at h1
    change a.memaddrs = ordinaryDomain; rw [h1]; exact hP0.memaddrs
  have hma_b : (decClockHOLFinite b).memaddrs = ordinaryDomain := by
    have h1 := hb.1; unfold LocFrame at h1
    change b.memaddrs = ordinaryDomain; rw [h1]; exact hP0.memaddrs
  rw [hma_a] at hdoma; rw [hma_b] at hdomb
  have hbnda := ordinaryDomain_bounds _ hdoma
  have hbndb := ordinaryDomain_bounds _ hdomb
  have hala := ordinaryDomain_aligned _ hdoma
  have halb := ordinaryDomain_aligned _ hdomb
  -- From `htabSetKey a = htabSetKey b`, deduce `addra = addrb` and hence `wna * 32 = wnb * 32`!
  have hk_val := congrArg Fin.val hk
  simp only [htabSetKey, hna_nodes, hna_n, hnb_nodes, hnb_n,
    dif_pos hbnda, dif_pos hbndb] at hk_val
  have heS : sourceBase % 8 = 0 := by decide
  have haddr_eq : wnodes + wna * (BitVec.ofNat 64 32) + (BitVec.ofNat 64 24) =
      wnodes + wnb * (BitVec.ofNat 64 32) + (BitVec.ofNat 64 24) :=
    BitVec.eq_of_toNat_eq (by omega)
  have hmul_eq : wna * (BitVec.ofNat 64 32) = wnb * (BitVec.ofNat 64 32) := by
    have hsub := congrArg (fun x => x - (BitVec.ofNat 64 24)) haddr_eq
    simp only [BitVec.add_sub_cancel] at hsub
    have hsub2 := congrArg (fun x => -wnodes + x) hsub
    simpa [← BitVec.add_assoc] using hsub2
  -- Also `vba = vbb` because `a` and `b` have identical `memory`, `structs`, `memaddrs` as `s0`!
  have ha0 := ha.1; unfold LocFrame at ha0
  have hb0 := hb.1; unfold LocFrame at hb0
  have hv_eq : vba = vbb := by
    have heva' := heva; have hevb' := hevb
    rw [evalHOLExact, haddra] at heva'
    rw [evalHOLExact, haddrb] at hevb'
    rw [haddr_eq] at heva'
    have hmem_eq : (decClockHOLFinite a).toExact.memory = (decClockHOLFinite b).toExact.memory := by
      change a.memory = b.memory; rw [ha0, hb0]
    have hstr_eq : (decClockHOLFinite a).toExact.structs = (decClockHOLFinite b).toExact.structs := by
      change a.structs = b.structs; rw [ha0, hb0]
    have hmad_eq : (decClockHOLFinite a).toExact.memaddrs = (decClockHOLFinite b).toExact.memaddrs := by
      change (decClockHOLFinite a).memaddrs = (decClockHOLFinite b).memaddrs
      rw [hma_a, hma_b]
    rw [hmem_eq, hstr_eq] at heva'
    dsimp only at heva' hevb'
    split at heva'
    · rename_i hwf
      rw [if_pos hwf] at hevb'
      simp only [memLoadHOLExact] at heva' hevb'
      have hda : (decClockHOLFinite a).memaddrs (wnodes + wnb * (BitVec.ofNat 64 32) + (BitVec.ofNat 64 24)) := by
        rw [hma_a]; exact hdomb
      have hdb : (decClockHOLFinite b).memaddrs (wnodes + wnb * (BitVec.ofNat 64 32) + (BitVec.ofNat 64 24)) := by
        rw [hma_b]; exact hdomb
      rw [if_pos hda] at heva'
      rw [if_pos hdb] at hevb'
      exact Option.some.inj (heva'.symm.trans hevb')
    · simp at heva'
  subst hv_eq
  split at hrun_a
  · rename_i hsh
    rw [if_pos hsh] at hrun_b
    -- Extract the inner `(none, ina)` and `(none, inb)` from `hrun_a` and `hrun_b`:
    set sa1 := setVarHOLFinite (ofString "b") vba (decClockHOLFinite a)
    set sb1 := setVarHOLFinite (ofString "b") vba (decClockHOLFinite b)
    rcases hin_a : evaluateHOLFiniteState sa1 _ with ⟨ra1, ina⟩
    rw [hin_a] at hrun_a
    have hra1 : ra1 = none := congrArg Prod.fst hrun_a
    subst hra1
    have hpa : pa.locals = ina.locals.resVarEq (ofString "b", a.locals.lookup (ofString "b")) := by
      have hp := congrArg (fun x => x.2.locals) hrun_a
      exact hp.symm
    rcases hin_b : evaluateHOLFiniteState sb1 _ with ⟨rb1, inb⟩
    rw [hin_b] at hrun_b
    have hrb1 : rb1 = none := congrArg Prod.fst hrun_b
    subst hrb1
    have hpb : pb.locals = inb.locals.resVarEq (ofString "b", b.locals.lookup (ofString "b")) := by
      have hp := congrArg (fun x => x.2.locals) hrun_b
      exact hp.symm
    rw [hpa, hpb, PanRunBounded.resVarEq_lookup, PanRunBounded.resVarEq_lookup,
      if_neg (by decide : ofString "n" ≠ ofString "b"),
      if_neg (by decide : ofString "n" ≠ ofString "b")]
    -- Step through `seq (ite (b >= d) break skip) ...` inside `hin_a` and `hin_b`:
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hin_a hin_b
    split at hin_a; swap; · simp at hin_a
    split at hin_a; swap; · rw [evaluateHOLFiniteState_break] at hin_a; simp at hin_a
    rw [evaluateHOLFiniteState_skip] at hin_a; dsimp only at hin_a
    split at hin_b; swap; · simp at hin_b
    split at hin_b; swap; · rw [evaluateHOLFiniteState_break] at hin_b; simp at hin_b
    rw [evaluateHOLFiniteState_skip] at hin_b; dsimp only at hin_b
    -- Next `p := n` succeeds on both `sa1` and `sb1`, setting `p` to `wna` and `wnb` respectively, while keeping `b`, `key`, `nodes`, and `n * 32` equal!
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign] at hin_a hin_b
    have hsa1_n : @evalHOLExact 64 F _ sa1.toExact (fun x => Classical.propDecidable (sa1.memaddrs x))
        (.var .local (ofString "n")) = some (.val (.word wna)) := by
      simp only [evalHOLExact, PanSemStateFiniteExact.toExact, sa1, setVarHOLFinite,
        HolFiniteMapExact.lookup_update, FUPDATE, show ofString "b" ≠ ofString "n" by decide, ↓reduceIte]
      exact hna_n
    have hsb1_n : @evalHOLExact 64 F _ sb1.toExact (fun x => Classical.propDecidable (sb1.memaddrs x))
        (.var .local (ofString "n")) = some (.val (.word wnb)) := by
      simp only [evalHOLExact, PanSemStateFiniteExact.toExact, sb1, setVarHOLFinite,
        HolFiniteMapExact.lookup_update, FUPDATE, show ofString "b" ≠ ofString "n" by decide, ↓reduceIte]
      exact hnb_n
    rw [hsa1_n] at hin_a; rw [hsb1_n] at hin_b; dsimp only at hin_a hin_b
    by_cases hvlda : isValidValueHOLFinite sa1 .local (ofString "p") (.val (.word wna)) = true
    swap; · rw [if_neg hvlda] at hin_a; simp at hin_a
    by_cases hvldb : isValidValueHOLFinite sb1 .local (ofString "p") (.val (.word wnb)) = true
    swap; · rw [if_neg hvldb] at hin_b; simp at hin_b
    rw [if_pos hvlda] at hin_a; rw [if_pos hvldb] at hin_b; dsimp only at hin_a hin_b
    set sa2 := setKvarHOLFinite .local (ofString "p") (.val (.word wna)) sa1
    set sb2 := setKvarHOLFinite .local (ofString "p") (.val (.word wnb)) sb1
    have ha_rest := hin_a
    have hb_rest := hin_b
    -- Now `ha_rest : eval sa2 (ite bitCond (n := load +8) (n := load +16)) = (none, ina)`
    -- and `hb_rest : eval sb2 (ite bitCond (n := load +8) (n := load +16)) = (none, inb)`!
    -- Show `bitCond` evaluates to the SAME value on `sa2` and `sb2`, and BOTH load expressions evaluate to the SAME value on `sa2` and `sb2`!
    have hsa2_mem : sa2.memory = sb2.memory := by change a.memory = b.memory; rw [ha0, hb0]
    have hsa2_mad : sa2.memaddrs = sb2.memaddrs := by change a.memaddrs = b.memaddrs; rw [ha0, hb0]
    have hsa2_be : sa2.be = sb2.be := by change a.be = b.be; rw [ha0, hb0]
    have hsa2_str : sa2.structs = sb2.structs := by change a.structs = b.structs; rw [ha0, hb0]
    have hsa2_key : sa2.locals.lookup (ofString "key") = sb2.locals.lookup (ofString "key") := by
      simp only [sa2, sb2, sa1, sb1, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "p" ≠ ofString "key" by decide, show ofString "b" ≠ ofString "key" by decide, ↓reduceIte]
      exact hkey_eq
    have hsa2_b : sa2.locals.lookup (ofString "b") = sb2.locals.lookup (ofString "b") := by
      simp [sa2, sb2, sa1, sb1, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "p" ≠ ofString "b" by decide]
    have hsa2_nodes_a : sa2.locals.lookup (ofString "nodes") = some (.val (.word wnodes)) := by
      simp only [sa2, sa1, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "p" ≠ ofString "nodes" by decide, show ofString "b" ≠ ofString "nodes" by decide, ↓reduceIte]
      exact hna_nodes
    have hsb2_nodes_b : sb2.locals.lookup (ofString "nodes") = some (.val (.word wnodes)) := by
      simp only [sb2, sb1, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "p" ≠ ofString "nodes" by decide, show ofString "b" ≠ ofString "nodes" by decide, ↓reduceIte]
      exact hnb_nodes
    have hsa2_na : sa2.locals.lookup (ofString "n") = some (.val (.word wna)) := by
      simp only [sa2, sa1, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "p" ≠ ofString "n" by decide, show ofString "b" ≠ ofString "n" by decide, ↓reduceIte]
      exact hna_n
    have hsb2_nb : sb2.locals.lookup (ofString "n") = some (.val (.word wnb)) := by
      simp only [sb2, sb1, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "p" ≠ ofString "n" by decide, show ofString "b" ≠ ofString "n" by decide, ↓reduceIte]
      exact hnb_n
    have hbit_eq : @evalHOLExact 64 F _ sa2.toExact (fun x => Classical.propDecidable (sa2.memaddrs x))
        (.cmp .equal (.op .and [.shift .lsr (.loadByte (.op .add [.var .local (ofString "key"),
          .shift .lsr (.var .local (ofString "b")) (.const (BitVec.ofNat 64 3))]))
          (.op .sub [.const (BitVec.ofNat 64 7), .op .and [.var .local (ofString "b"), .const (BitVec.ofNat 64 7)]]),
          .const (BitVec.ofNat 64 1)]) (.const (BitVec.ofNat 64 0))) =
        @evalHOLExact 64 F _ sb2.toExact (fun x => Classical.propDecidable (sb2.memaddrs x))
        (.cmp .equal (.op .and [.shift .lsr (.loadByte (.op .add [.var .local (ofString "key"),
          .shift .lsr (.var .local (ofString "b")) (.const (BitVec.ofNat 64 3))]))
          (.op .sub [.const (BitVec.ofNat 64 7), .op .and [.var .local (ofString "b"), .const (BitVec.ofNat 64 7)]]),
          .const (BitVec.ofNat 64 1)]) (.const (BitVec.ofNat 64 0))) := by
      have hlb : @evalHOLExact 64 F _ sa2.toExact (fun x => Classical.propDecidable (sa2.memaddrs x))
          (.loadByte (.op .add [.var .local (ofString "key"),
            .shift .lsr (.var .local (ofString "b")) (.const (BitVec.ofNat 64 3))])) =
          @evalHOLExact 64 F _ sb2.toExact (fun x => Classical.propDecidable (sb2.memaddrs x))
          (.loadByte (.op .add [.var .local (ofString "key"),
            .shift .lsr (.var .local (ofString "b")) (.const (BitVec.ofNat 64 3))])) := by
        have haddr_lb : @evalHOLExact 64 F _ sa2.toExact (fun x => Classical.propDecidable (sa2.memaddrs x))
            (.op .add [.var .local (ofString "key"),
              .shift .lsr (.var .local (ofString "b")) (.const (BitVec.ofNat 64 3))]) =
            @evalHOLExact 64 F _ sb2.toExact (fun x => Classical.propDecidable (sb2.memaddrs x))
            (.op .add [.var .local (ofString "key"),
              .shift .lsr (.var .local (ofString "b")) (.const (BitVec.ofNat 64 3))]) := by
          simp only [evalHOLExact, evalListHOLExact, PanSemStateFiniteExact.toExact, hsa2_key, hsa2_b]
        rw [evalHOLExact, haddr_lb, evalHOLExact]
        rcases @evalHOLExact 64 F _ sb2.toExact (fun x => Classical.propDecidable (sb2.memaddrs x))
            (.op .add [.var .local (ofString "key"),
              .shift .lsr (.var .local (ofString "b")) (.const (BitVec.ofNat 64 3))]) with _ | vv
        · rfl
        rcases vv with ⟨⟨w⟩⟩ | _ | _ <;> try rfl
        dsimp only [panMemLoadByteHOL]
        by_cases hm : sb2.memaddrs (panByteAlignHOL (width := 64) w)
        · have hma : sa2.memaddrs (panByteAlignHOL (width := 64) w) := hsa2_mad ▸ hm
          simp [PanSemStateFiniteExact.toExact, hm, hma, hsa2_mem, hsa2_be]
        · have hma : ¬ sa2.memaddrs (panByteAlignHOL (width := 64) w) := hsa2_mad ▸ hm
          simp [PanSemStateFiniteExact.toExact, hm, hma]
      have hsh_amt : @evalHOLExact 64 F _ sa2.toExact (fun x => Classical.propDecidable (sa2.memaddrs x))
          (.op .sub [.const (BitVec.ofNat 64 7), .op .and [.var .local (ofString "b"), .const (BitVec.ofNat 64 7)]]) =
          @evalHOLExact 64 F _ sb2.toExact (fun x => Classical.propDecidable (sb2.memaddrs x))
          (.op .sub [.const (BitVec.ofNat 64 7), .op .and [.var .local (ofString "b"), .const (BitVec.ofNat 64 7)]]) := by
        simp only [evalHOLExact, evalListHOLExact, PanSemStateFiniteExact.toExact, hsa2_b]
      have hlsr : @evalHOLExact 64 F _ sa2.toExact (fun x => Classical.propDecidable (sa2.memaddrs x))
          (.shift .lsr (.loadByte (.op .add [.var .local (ofString "key"),
            .shift .lsr (.var .local (ofString "b")) (.const (BitVec.ofNat 64 3))]))
            (.op .sub [.const (BitVec.ofNat 64 7), .op .and [.var .local (ofString "b"), .const (BitVec.ofNat 64 7)]])) =
          @evalHOLExact 64 F _ sb2.toExact (fun x => Classical.propDecidable (sb2.memaddrs x))
          (.shift .lsr (.loadByte (.op .add [.var .local (ofString "key"),
            .shift .lsr (.var .local (ofString "b")) (.const (BitVec.ofNat 64 3))]))
            (.op .sub [.const (BitVec.ofNat 64 7), .op .and [.var .local (ofString "b"), .const (BitVec.ofNat 64 7)]])) := by
        conv_lhs => rw [evalHOLExact]
        conv_rhs => rw [evalHOLExact]
        rw [hlb, hsh_amt]
      have hand : @evalHOLExact 64 F _ sa2.toExact (fun x => Classical.propDecidable (sa2.memaddrs x))
          (.op .and [.shift .lsr (.loadByte (.op .add [.var .local (ofString "key"),
            .shift .lsr (.var .local (ofString "b")) (.const (BitVec.ofNat 64 3))]))
            (.op .sub [.const (BitVec.ofNat 64 7), .op .and [.var .local (ofString "b"), .const (BitVec.ofNat 64 7)]]),
            .const (BitVec.ofNat 64 1)]) =
          @evalHOLExact 64 F _ sb2.toExact (fun x => Classical.propDecidable (sb2.memaddrs x))
          (.op .and [.shift .lsr (.loadByte (.op .add [.var .local (ofString "key"),
            .shift .lsr (.var .local (ofString "b")) (.const (BitVec.ofNat 64 3))]))
            (.op .sub [.const (BitVec.ofNat 64 7), .op .and [.var .local (ofString "b"), .const (BitVec.ofNat 64 7)]]),
            .const (BitVec.ofNat 64 1)]) := by
        conv_lhs => rw [evalHOLExact, evalListHOLExact]
        conv_rhs => rw [evalHOLExact, evalListHOLExact]
        rw [hlsr]
        rfl
      conv_lhs => rw [evalHOLExact]
      conv_rhs => rw [evalHOLExact]
      rw [hand]; rfl
    have hchild_eq : ∀ (off : BitVec 64),
        @evalHOLExact 64 F _ sa2.toExact (fun x => Classical.propDecidable (sa2.memaddrs x))
          (.load .one (.op .add [.var .local (ofString "nodes"),
            .panop .mul [.var .local (ofString "n"), .const (BitVec.ofNat 64 32)], .const off])) =
        @evalHOLExact 64 F _ sb2.toExact (fun x => Classical.propDecidable (sb2.memaddrs x))
          (.load .one (.op .add [.var .local (ofString "nodes"),
            .panop .mul [.var .local (ofString "n"), .const (BitVec.ofNat 64 32)], .const off])) := by
      intro off
      have had1 : @evalHOLExact 64 F _ sa2.toExact (fun x => Classical.propDecidable (sa2.memaddrs x))
          (.op .add [.var .local (ofString "nodes"),
            .panop .mul [.var .local (ofString "n"), .const (BitVec.ofNat 64 32)], .const off]) =
          some (.val (.word (wnodes + wna * (BitVec.ofNat 64 32) + off))) := by
        simp [evalHOLExact, evalListHOLExact, hsa2_nodes_a, hsa2_na, panOpHOL, wordOpHOL, wordOp,
          valueIsWord, valueWord, List.foldr, add_zero, BitVec.add_assoc]
      have had2 : @evalHOLExact 64 F _ sb2.toExact (fun x => Classical.propDecidable (sb2.memaddrs x))
          (.op .add [.var .local (ofString "nodes"),
            .panop .mul [.var .local (ofString "n"), .const (BitVec.ofNat 64 32)], .const off]) =
          some (.val (.word (wnodes + wnb * (BitVec.ofNat 64 32) + off))) := by
        simp [evalHOLExact, evalListHOLExact, hsb2_nodes_b, hsb2_nb, panOpHOL, wordOpHOL, wordOp,
          valueIsWord, valueWord, List.foldr, add_zero, BitVec.add_assoc]
      rw [evalHOLExact, had1, evalHOLExact, had2]
      have hsa2_str' : sa2.toExact.structs = sb2.toExact.structs := hsa2_str
      have hsa2_mem' : sa2.toExact.memory = sb2.toExact.memory := hsa2_mem
      rw [hsa2_str', hmul_eq]
      dsimp only
      split
      · simp only [memLoadHOLExact, hsa2_mem']
        by_cases hm : sb2.memaddrs (wnodes + wnb * (BitVec.ofNat 64 32) + off)
        · have hma : sa2.memaddrs (wnodes + wnb * (BitVec.ofNat 64 32) + off) := hsa2_mad ▸ hm
          simp [PanSemStateFiniteExact.toExact, hm, hma, hsa2_mem]
        · have hma : ¬ sa2.memaddrs (wnodes + wnb * (BitVec.ofNat 64 32) + off) := hsa2_mad ▸ hm
          simp [PanSemStateFiniteExact.toExact, hm, hma]
      · rfl
    rw [evaluateHOLFiniteState_ite] at ha_rest hb_rest
    rw [hbit_eq] at ha_rest
    split at ha_rest
    · rename_i _ bw hbw
      rw [hbw] at hb_rest; dsimp only at hb_rest
      by_cases hbw0 : bw = 0
      · rw [if_pos hbw0] at ha_rest hb_rest
        rw [evaluateHOLFiniteState_assign] at ha_rest hb_rest
        rw [hchild_eq (BitVec.ofNat 64 16)] at ha_rest
        rcases hch : @evalHOLExact 64 F _ sb2.toExact (fun x => Classical.propDecidable (sb2.memaddrs x))
            (.load .one (.op .add [.var .local (ofString "nodes"),
              .panop .mul [.var .local (ofString "n"), .const (BitVec.ofNat 64 32)], .const (BitVec.ofNat 64 16)])) with _ | vc
        · rw [hch] at ha_rest; simp at ha_rest
        · rw [hch] at ha_rest hb_rest; dsimp only at ha_rest hb_rest
          by_cases hvca : isValidValueHOLFinite sa2 .local (ofString "n") vc = true
          swap; · rw [if_neg hvca] at ha_rest; simp at ha_rest
          by_cases hvcb : isValidValueHOLFinite sb2 .local (ofString "n") vc = true
          swap; · rw [if_neg hvcb] at hb_rest; simp at hb_rest
          rw [if_pos hvca] at ha_rest; rw [if_pos hvcb] at hb_rest
          injection ha_rest with _ hina; injection hb_rest with _ hinb
          rw [← hina, ← hinb]
          simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      · rw [if_neg hbw0] at ha_rest hb_rest
        rw [evaluateHOLFiniteState_assign] at ha_rest hb_rest
        rw [hchild_eq (BitVec.ofNat 64 8)] at ha_rest
        rcases hch : @evalHOLExact 64 F _ sb2.toExact (fun x => Classical.propDecidable (sb2.memaddrs x))
            (.load .one (.op .add [.var .local (ofString "nodes"),
              .panop .mul [.var .local (ofString "n"), .const (BitVec.ofNat 64 32)], .const (BitVec.ofNat 64 8)])) with _ | vc
        · rw [hch] at ha_rest; simp at ha_rest
        · rw [hch] at ha_rest hb_rest; dsimp only at ha_rest hb_rest
          by_cases hvca : isValidValueHOLFinite sa2 .local (ofString "n") vc = true
          swap; · rw [if_neg hvca] at ha_rest; simp at ha_rest
          by_cases hvcb : isValidValueHOLFinite sb2 .local (ofString "n") vc = true
          swap; · rw [if_neg hvcb] at hb_rest; simp at hb_rest
          rw [if_pos hvca] at ha_rest; rw [if_pos hvcb] at hb_rest
          injection ha_rest with _ hina; injection hb_rest with _ hinb
          rw [← hina, ← hinb]
          simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    · simp at ha_rest
  · simp at hrun_a

/-- If `a1` and `b1` satisfy `BaseFrame s0` and have the same `n`, one flowing step makes ALL state
fields except `clock` identical (`p` becomes `n`, `n` becomes `child(n)`)! -/
theorem htabSet_secondStep_same_state {F : Type} {s0 a1 b1 : PanSemStateFiniteExact 64 F}
    (hP0 : GuestInv s0)
    (ha1 : BaseFrame s0 a1) (hb1 : BaseFrame s0 b1)
    (hn_eq : a1.locals.lookup (ofString "n") = b1.locals.lookup (ofString "n"))
    (hna1 : (evaluateHOLFiniteState (decClockHOLFinite a1) htabSetBody).1 = none)
    (hnb1 : (evaluateHOLFiniteState (decClockHOLFinite b1) htabSetBody).1 = none) :
    let a2 := (evaluateHOLFiniteState (decClockHOLFinite a1) htabSetBody).2
    let b2 := (evaluateHOLFiniteState (decClockHOLFinite b1) htabSetBody).2
    b2 = { a2 with clock := b2.clock } := by
  intro a2 b2
  have ha2 := baseFrame_step ha1 hna1
  have hb2 := baseFrame_step hb1 hnb1
  have hk_eq : htabSetKey a1 = htabSetKey b1 := by
    have hnodes_eq : a1.locals.lookup (ofString "nodes") = b1.locals.lookup (ofString "nodes") :=
      (ha1.2 _ (by decide) (by decide)).trans (hb1.2 _ (by decide) (by decide)).symm
    simp only [htabSetKey, hnodes_eq, hn_eq]
  have hn2_eq : a2.locals.lookup (ofString "n") = b2.locals.lookup (ofString "n") :=
    htabSet_oneStep_same_n hP0 ha1 hb1 hk_eq hna1 hnb1
  -- Show `a2.locals.lookup "p" = a1.locals.lookup "n"` (and same for `b2` and `b1`)!
  have hp_after : ∀ (st : PanSemStateFiniteExact 64 F),
      (evaluateHOLFiniteState (decClockHOLFinite st) htabSetBody).1 = none →
      (evaluateHOLFiniteState (decClockHOLFinite st) htabSetBody).2.locals.lookup (ofString "p") =
      st.locals.lookup (ofString "n") := by
    intro st hnone
    rcases hrun : evaluateHOLFiniteState (decClockHOLFinite st) htabSetBody with ⟨r, post⟩
    rw [hrun] at hnone; dsimp only at hnone; subst hnone
    dsimp only
    unfold htabSetBody at hrun
    dsimp only [InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map] at hrun
    obtain ⟨vb, inner, hin, hpost⟩ := dec_flowing (Or.inl rfl) hrun
    rw [hpost, PanRunBounded.resVarEq_lookup, if_neg (by decide : ofString "p" ≠ ofString "b")]
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hin
    split at hin; swap; · simp at hin
    split at hin; swap; · rw [evaluateHOLFiniteState_break] at hin; simp at hin
    rw [evaluateHOLFiniteState_skip] at hin; dsimp only at hin
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign] at hin
    rcases hn_lk : (setVarHOLFinite (ofString "b") vb (decClockHOLFinite st)).locals.lookup (ofString "n") with _ | vn
    · simp [evalHOLExact, hn_lk] at hin
    have hev_n : @evalHOLExact 64 F _ (setVarHOLFinite (ofString "b") vb (decClockHOLFinite st)).toExact
        (fun x => Classical.propDecidable ((setVarHOLFinite (ofString "b") vb (decClockHOLFinite st)).memaddrs x))
        (.var .local (ofString "n")) = some vn := hn_lk
    rw [hev_n] at hin; dsimp only at hin
    by_cases hvld : isValidValueHOLFinite (setVarHOLFinite (ofString "b") vb (decClockHOLFinite st)) .local (ofString "p") vn = true
    · rw [if_pos hvld] at hin; dsimp only at hin
      have havoid_p : avoidsLocal (ofString "p")
          (.ite (.cmp .equal (.op .and [.shift .lsr (.loadByte (.op .add [.var .local (ofString "key"),
              .shift .lsr (.var .local (ofString "b")) (.const (BitVec.ofNat 64 3))]))
              (.op .sub [.const (BitVec.ofNat 64 7), .op .and [.var .local (ofString "b"), .const (BitVec.ofNat 64 7)]]),
              .const (BitVec.ofNat 64 1)]) (.const (BitVec.ofNat 64 0)))
            (.assign .local (ofString "n") (.load .one (.op .add [.var .local (ofString "nodes"),
              .panop .mul [.var .local (ofString "n"), .const (BitVec.ofNat 64 32)], .const (BitVec.ofNat 64 8)])))
            (.assign .local (ofString "n") (.load .one (.op .add [.var .local (ofString "nodes"),
              .panop .mul [.var .local (ofString "n"), .const (BitVec.ofNat 64 32)], .const (BitVec.ofNat 64 16)])))) = true := by
        decide
      have hkp := evaluate_avoidsLocal_flowing (ofString "p") _ havoid_p _
        (by rw [hin]; exact Or.inl rfl)
      rw [hin] at hkp; dsimp only at hkp
      rw [hkp]
      simp only [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ↓reduceIte]
      simp only [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "b" ≠ ofString "n" by decide, ↓reduceIte] at hn_lk
      exact hn_lk.symm
    · rw [if_neg hvld] at hin; simp at hin
  have hp2_eq : a2.locals.lookup (ofString "p") = b2.locals.lookup (ofString "p") := by
    exact (hp_after a1 hna1).trans (hn_eq.trans (hp_after b1 hnb1).symm)
  have hloc_eq : b2.locals = a2.locals := locals_ext fun z => by
    by_cases hzn : z = ofString "n"
    · subst hzn; exact hn2_eq.symm
    · by_cases hzp : z = ofString "p"
      · subst hzp; exact hp2_eq.symm
      · exact (hb2.2 z hzn hzp).trans (ha2.2 z hzn hzp).symm
  have hfa2 := ha2.1; unfold LocFrame at hfa2
  have hfb2 := hb2.1; unfold LocFrame at hfb2
  change (evaluateHOLFiniteState (decClockHOLFinite b1) htabSetBody).2 = _
  dsimp only [a2, b2] at hloc_eq ⊢
  rw [hfb2, hfa2, hloc_eq]

def OneStepFrom {F : Type} (s0 : PanSemStateFiniteExact 64 F) (k : Fin domainCells)
    (s1 : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ g : PanSemStateFiniteExact 64 F, BaseFrame s0 g ∧ htabSetKey g = k ∧
    (evaluateHOLFiniteState (decClockHOLFinite g) htabSetBody).1 = none ∧
    s1 = (evaluateHOLFiniteState (decClockHOLFinite g) htabSetBody).2

def TwoStepFrom {F : Type} (s0 : PanSemStateFiniteExact 64 F) (k : Fin domainCells)
    (s2 : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ s1 : PanSemStateFiniteExact 64 F, OneStepFrom s0 k s1 ∧
    (evaluateHOLFiniteState (decClockHOLFinite s1) htabSetBody).1 = none ∧
    s2 = (evaluateHOLFiniteState (decClockHOLFinite s1) htabSetBody).2

theorem twoStep_same_state {F : Type} {s0 e2 post : PanSemStateFiniteExact 64 F}
    {k : Fin domainCells} (hP0 : GuestInv s0)
    (he2 : TwoStepFrom s0 k e2) (hpost : TwoStepFrom s0 k post) :
    post = { e2 with clock := post.clock } := by
  obtain ⟨a1, ⟨a0, ha0, hka, hna0, rfl⟩, hna1, rfl⟩ := he2
  obtain ⟨b1, ⟨b0, hb0, hkb, hnb0, rfl⟩, hnb1, rfl⟩ := hpost
  have hn1 := htabSet_oneStep_same_n hP0 ha0 hb0 (hka.trans hkb.symm) hna0 hnb0
  exact htabSet_secondStep_same_state hP0 (baseFrame_step ha0 hna0) (baseFrame_step hb0 hnb0)
    hn1 hna1 hnb1

def VisitedTwoStep {F : Type} (s0 state : PanSemStateFiniteExact 64 F)
    (visited : Finset (Fin domainCells)) : Prop :=
  ∀ k ∈ visited, ∃ e2 : PanSemStateFiniteExact 64 F, TwoStepFrom s0 k e2 ∧
    state.clock ≤ e2.clock ∧
    evaluateHOLFiniteState e2 (.while htabSetCond htabSetBody) =
      evaluateHOLFiniteState state (.while htabSetCond htabSetBody)

theorem htabSet_while_aux {F : Type} (s0 : PanSemStateFiniteExact 64 F)
    (hcode0 : s0.code = originalRuntimeCode) (hP0 : GuestInv s0) :
    ∀ (m : Nat) (state : PanSemStateFiniteExact 64 F) (prev : Option (Fin domainCells))
      (visited : Finset (Fin domainCells)),
      BaseFrame s0 state →
      (∀ k1, prev = some k1 → OneStepFrom s0 k1 state) →
      VisitedTwoStep s0 state visited →
      domainCells + 1 + (if prev.isNone then 1 else 0) ≤ visited.card + m →
      TerminatingRunBounded state (.while htabSetCond htabSetBody) (m * (0 + 1)) := by
  intro m
  induction m with
  | zero =>
    intro state prev visited _ _ _ hcard _
    exfalso
    have hle : visited.card ≤ domainCells := by simpa using Finset.card_le_univ visited
    cases hpr : prev <;> simp [hpr] at hcard <;> omega
  | succ m ih =>
    intro state prev visited hbf hprev hvis hcard hnt
    have hnt0 := hnt
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnt ⊢
    split
    · rename_i word hword
      simp only [hword] at hnt
      by_cases hzero : word = 0
      · rw [if_neg (by simp [hzero])]; exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
      · rw [if_pos hzero] at hnt ⊢
        by_cases hclock : state.clock = 0
        · rw [if_pos hclock] at hnt; exact absurd rfl hnt
        · rw [if_neg hclock] at hnt ⊢
          have hunfold := while_unfold_continue htabSetCond htabSetBody state word hword hzero hclock
          have hclk_body := TerminatingProgBounded.straight htabSetBody rfl
            (decClockHOLFinite state) (by have h := hbf.1; unfold LocFrame at h; rw [h]; exact hcode0)
          have hnc := evaluate_noTopContinue htabSetBody rfl (decClockHOLFinite state)
          unfold TerminatingRunBounded at hclk_body
          rcases hrun : evaluateHOLFiniteState (decClockHOLFinite state) htabSetBody with ⟨res, post⟩
          simp only [hrun] at hnt hclk_body hnc hunfold
          cases res with
          | none =>
            dsimp only at hnt hunfold ⊢
            obtain ⟨hspent, hkept⟩ := hclk_body (by simp)
            change state.clock - 1 ≤ post.clock + 0 at hspent
            change post.clock ≤ state.clock - 1 at hkept
            have hnone_run : (evaluateHOLFiniteState (decClockHOLFinite state) htabSetBody).1 = none := by
              rw [hrun]
            have hpost_eq : post = (evaluateHOLFiniteState (decClockHOLFinite state) htabSetBody).2 := by
              rw [hrun]
            have hbf_post : BaseFrame s0 post := by rw [hpost_eq]; exact baseFrame_step hbf hnone_run
            have hone_post : OneStepFrom s0 (htabSetKey state) post :=
              ⟨state, hbf, rfl, hnone_run, hpost_eq⟩
            have hsame := hunfold (Or.inl rfl)
            have hnt_post : (evaluateHOLFiniteState post (.while htabSetCond htabSetBody)).1 ≠ some .timeOut := by
              rw [← hsame]; exact hnt0
            cases hpr : prev with
            | none =>
              rw [hpr] at hcard
              obtain ⟨htail, htailKept⟩ := ih post (some (htabSetKey state)) visited
                hbf_post
                (fun k1 hk1 => by injection hk1 with hk1; subst hk1; exact hone_post)
                (fun k hk => by
                  obtain ⟨e2, he2, hclk_e2, hsame_e2⟩ := hvis k hk
                  exact ⟨e2, he2, by omega, hsame_e2.trans hsame⟩)
                (by simp at hcard ⊢; omega)
                hnt_post
              exact ⟨by omega, by omega⟩
            | some k1 =>
              rw [hpr] at hcard
              have htwo_post : TwoStepFrom s0 k1 post :=
                ⟨state, hprev k1 hpr, hnone_run, hpost_eq⟩
              have hfresh : k1 ∉ visited := by
                intro hmem
                obtain ⟨e2, he2, hclk_e2, hsame_e2⟩ := hvis k1 hmem
                have heq := twoStep_same_state hP0 he2 htwo_post
                exact evaluate_ne_of_clock_lt _ post e2 (by rw [heq]) (by omega)
                  (hsame_e2.trans hsame) hnt_post
              obtain ⟨htail, htailKept⟩ := ih post (some (htabSetKey state)) (insert k1 visited)
                hbf_post
                (fun k' hk' => by injection hk' with hk'; subst hk'; exact hone_post)
                (fun k hk => by
                  rcases Finset.mem_insert.mp hk with rfl | hk
                  · exact ⟨post, htwo_post, Nat.le_refl _, rfl⟩
                  · obtain ⟨e2, he2, hclk_e2, hsame_e2⟩ := hvis k hk
                    exact ⟨e2, he2, by omega, hsame_e2.trans hsame⟩)
                (by rw [Finset.card_insert_of_notMem hfresh]; simp at hcard ⊢; omega)
                hnt_post
              exact ⟨by omega, by omega⟩
          | some r =>
            cases r with
            | «continue» => exact absurd rfl hnc
            | timeOut => exact absurd rfl hnt
            | _ =>
              obtain ⟨hspent, hkept⟩ := hclk_body (by simp)
              change state.clock - 1 ≤ post.clock + 0 at hspent
              change post.clock ≤ state.clock - 1 at hkept
              simp only
              exact ⟨by omega, by omega⟩
    · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩

theorem htabSet_while_bound :
    TerminatingProgBoundedOn GuestInv (.while htabSetCond htabSetBody)
      ((7776239486 + 1) * (0 + 1)) := by
  intro F s0 hcode0 hP0
  refine (htabSet_while_aux s0 hcode0 hP0 (domainCells + 2) s0 none ∅
    (baseFrame_refl s0) (fun _ h => by cases h) (fun _ h => by simp at h) (by decide)).weaken ?_
  decide

end HtabSetLoop

theorem fb_htab_set : TerminatingFunBoundedOn GuestInv (ofString "htab_set") K.«htab_set» := by
  fb_unfold 138 Guest.Software.guestFn_htab_set
  apply TerminatingProgBoundedOn.weaken'
  · apply dec_guestInv; apply dec_guestInv
    apply decCall_guestInv' fb_htab_find_leaf
    apply dec_guestInv
    apply TerminatingProgBoundedOn.seq_guestInv
    · fb_auto
    · apply decCall_guestInv' fb_memeq
      apply TerminatingProgBoundedOn.seq_guestInv
      · fb_auto
      · apply decCall_guestInv' fb_htab_first_diff
        apply dec_guestInv; apply dec_guestInv; apply dec_guestInv
        apply TerminatingProgBoundedOn.seq_guestInv
        · exact htabSet_while_bound
        · fb_auto
  · unfold K.«htab_set»
    generalize_K
    simp only [Nat.add_zero, Nat.zero_add, Nat.max_def, max_def]
    split_ifs <;> omega

theorem fb_warm_storage_key :
    TerminatingFunBoundedOn GuestInv (ofString "warm_storage_key") K.«warm_storage_key» := by
  fb_prove 526 Guest.Software.guestFn_warm_storage_key K.«warm_storage_key»

theorem fb_jset : TerminatingFunBoundedOn GuestInv (ofString "jset") K.«jset» := by
  fb_prove 356 Guest.Software.guestFn_jset K.«jset»

theorem fb_record_pre_state_read :
    TerminatingFunBoundedOn GuestInv (ofString "record_pre_state_read") K.«record_pre_state_read» := by
  fb_prove 364 Guest.Software.guestFn_record_pre_state_read K.«record_pre_state_read»

/-! ### `fb_destroy_storage` (`guestAst[389]`, Target #8): signed counter `i <s cap` from `0` -/

section DestroyStorage

def dsGuard : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => GuestInv s ∧ ∃ w : BitVec 64,
    s.locals.lookup (ofString "i") = some (.val (.word w)) ∧ w.toNat < 2 ^ 63

def dsMu : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Nat := fun s =>
  match s.locals.lookup (ofString "i"), s.locals.lookup (ofString "cap") with
  | some (.val (.word w)), some (.val (.word c)) =>
    if c.toNat < 2 ^ 63 then c.toNat - w.toNat else 0
  | _, _ => 0

theorem dsMu_le {F : Type} (s : PanSemStateFiniteExact 64 F) : dsMu s ≤ 2 ^ 63 := by
  unfold dsMu
  split
  · split <;> omega
  · exact Nat.zero_le _

theorem dec_zero_dsGuard (initBody : ProgHOL 64) {K : Nat}
    (hb : TerminatingProgBoundedOn dsGuard initBody K) :
    TerminatingProgBoundedOn GuestInv (.dec (ofString "i") .one (.const (BitVec.ofNat 64 0)) initBody) K := by
  intro F state hcode hP hnt
  rw [evaluateHOLFiniteState_dec_total] at hnt ⊢
  dsimp only at hnt ⊢
  have hev0 : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a))
      (.const (BitVec.ofNat 64 0)) = some (.val (.word 0)) := rfl
  have hsh0 : shapeEqHOL .one (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  rw [hev0] at hnt ⊢; dsimp only at hnt ⊢; rw [if_pos hsh0] at hnt ⊢; dsimp only at hnt ⊢
  have hds : dsGuard (setVarHOLFinite (ofString "i") (.val (.word 0)) state) :=
    ⟨guestInv_setVar _ _ state hP, 0,
      by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE], by decide⟩
  exact hb (setVarHOLFinite (ofString "i") (.val (.word 0)) state) hcode hds hnt

theorem seq_dsGuard_guestInv {first second : ProgHOL 64} {a b : Nat}
    (h1 : TerminatingProgBoundedOn dsGuard first a)
    (h2 : TerminatingProgBoundedOn GuestInv second b) :
    TerminatingProgBoundedOn dsGuard (.seq first second) (a + b) := by
  intro F state hcode hP hnt
  have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata state first
  have hmid := guestInv_evaluate state first hP.1
  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
  rcases hr1 : evaluateHOLFiniteState state first with ⟨r1, mid⟩
  simp only [hr1] at hmeta hnt hmid ⊢
  cases r1 with
  | none =>
    dsimp only at hnt ⊢
    obtain ⟨s1, k1⟩ := h1 state hcode hP (by simp [hr1])
    rw [hr1] at s1 k1; dsimp only at s1 k1
    obtain ⟨s2, k2⟩ := h2 mid (hmeta.1.trans hcode) hmid hnt
    exact ⟨by omega, by omega⟩
  | some _ =>
    dsimp only at hnt ⊢
    obtain ⟨s1, k1⟩ := h1 state hcode hP (by simpa [hr1] using hnt)
    rw [hr1] at s1 k1; dsimp only at s1 k1
    exact ⟨by omega, k1⟩

theorem decCall_incr_i {c : MlS} {step : BitVec 64} {name : MlS} {sh : ShapeHOL}
    {fn : MlS} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (hne : c ≠ name) (hrest : IncrStep c step cont) :
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (y : BitVec 64),
      s.locals.lookup c = some (.val (.word y)) →
      (evaluateHOLFiniteState s (.decCall name sh fn args cont)).1 = none →
      (evaluateHOLFiniteState s (.decCall name sh fn args cont)).2.locals.lookup c =
        some (.val (.word (y + step))) := by
  intro F s y hy hnone
  revert hnone
  rw [evaluateHOLFiniteState_decCall_total]
  split
  · simp
  split
  · simp
  split
  · simp
  rename_i _ vals _ _ body callee rs _ _
  rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨r1, st⟩
  simp only [hrun]
  cases r1 with
  | none => simp
  | some rr =>
    cases rr with
    | returned v =>
      dsimp only
      split
      · intro hnone
        simp only [PanRunBounded.resVarEq_lookup, if_neg hne]
        refine hrest.run _ y ?_ hnone
        simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hne, hy]
      · simp
    | _ => simp

end DestroyStorage

theorem fb_destroy_storage :
    TerminatingFunBoundedOn GuestInv (ofString "destroy_storage") K.«destroy_storage» := by
  fb_unfold 389 Guest.Software.guestFn_destroy_storage
  apply TerminatingProgBoundedOn.weaken'
  · apply dec_guestInv
    apply decCall_guestInv' fb_htab_get
    apply TerminatingProgBoundedOn.seq_guestInv
    · fb_auto
    · apply dec_guestInv; apply dec_guestInv
      apply dec_zero_dsGuard
      apply seq_dsGuard_guestInv
      · have hbody_guest : TerminatingProgBoundedOn GuestInv
            (.decCall (ofString "s") (.comb [.one, .one, .one]) (ofString "htab_item")
              [.var .local (ofString "inner"), .var .local (ofString "i")]
              (.seq
                (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "s"))) (.const (BitVec.ofNat 64 0)))
                  (.decCall (ofString "k") .one (ofString "sk_make")
                    [.var .local (ofString "addr"), .rfield 1 (.var .local (ofString "s"))]
                    (.call (some (none, none)) (ofString "htab_set")
                      [.load .one (.op .add [.var .global (ofString "ts"), .const (BitVec.ofNat 64 24)]),
                       .var .local (ofString "k"), .const (BitVec.ofNat 64 1)]))
                  .skip)
                (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 1)]))))
            (K.«htab_item» + (max ((K.«sk_make» + ((K.«htab_set» + 1) + 1))) 0 + 0) + 1) := by
          fb_auto
        intro F
        exact TerminatingProgBoundedOn.while_rank (P := dsGuard) (N := 2 ^ 63)
          (condition := .cmp .less (.var .local (ofString "i")) (.var .local (ofString "cap")))
          dsMu
          (fun s hP => ⟨guestInv_congr (s := s) rfl rfl rfl rfl hP.1, hP.2⟩)
          (fun s hc h => hbody_guest s hc h.1)
          (fun s _ _ _ => dsMu_le s) (fun s hcode hP hact hflow => by
          obtain ⟨hG, wi, hwi, hwi_lt⟩ := hP
          obtain ⟨word, hword, hnz⟩ := hact
          rw [evalHOLFinite_eq_toExact] at hword
          simp only [evalHOLExact, hwi] at hword
          rcases hcap : s.locals.lookup (ofString "cap") with _ | vcap
          · simp [hcap] at hword
          rcases vcap with ⟨⟨wcap⟩⟩ | _ | _ <;> try (simp [hcap] at hword; done)
          have hlt_cap : wi.toNat < wcap.toNat ∧ wcap.toNat < 2 ^ 63 := by
            simp only [hcap, Compiler.Encoders.Asm.wordCmpHOL, Compiler.Encoders.Asm.holAsmSignedLess] at hword
            have hwi' : wi.toNat < 9223372036854775808 := hwi_lt
            by_cases hc : wcap.toNat < 9223372036854775808
            · simp only [hwi', hc, ↓reduceIte] at hword
              by_cases hlt : wi.toNat < wcap.toNat
              · exact ⟨hlt, hc⟩
              · simp [hlt] at hword; exact absurd hword.symm hnz
            · simp [hwi', hc] at hword; exact absurd hword.symm hnz
          let lbody : ProgHOL 64 :=
            .decCall (ofString "s") (.comb [.one, .one, .one]) (ofString "htab_item")
              [.var .local (ofString "inner"), .var .local (ofString "i")]
              (.seq
                (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "s"))) (.const (BitVec.ofNat 64 0)))
                  (.decCall (ofString "k") .one (ofString "sk_make")
                    [.var .local (ofString "addr"), .rfield 1 (.var .local (ofString "s"))]
                    (.call (some (none, none)) (ofString "htab_set")
                      [.load .one (.op .add [.var .global (ofString "ts"), .const (BitVec.ofNat 64 24)]),
                       .var .local (ofString "k"), .const (BitVec.ofNat 64 1)]))
                  .skip)
                (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 1)])))
          have hnone : (evaluateHOLFiniteState (decClockHOLFinite s) lbody).1 = none :=
            hflow.resolve_right (evaluate_noTopContinue lbody (by decide) (decClockHOLFinite s))
          have hip := decCall_incr_i (c := ofString "i") (step := BitVec.ofNat 64 1) (by decide)
            (IncrStep.seq _ (by decide) IncrStep.incr) (decClockHOLFinite s) wi hwi hnone
          have hcap_keep := evaluate_avoidsLocal_flowing (ofString "cap") lbody (by decide)
            (decClockHOLFinite s) (Or.inl hnone)
          have hadd1 : (wi + BitVec.ofNat 64 1).toNat = wi.toNat + 1 := by
            rw [BitVec.toNat_add_of_lt] <;> simp <;> omega
          refine ⟨⟨guestInv_evaluate _ _ (guestInv_congr (s := s) rfl rfl rfl rfl hG),
            wi + BitVec.ofNat 64 1, hip, by omega⟩, ?_⟩
          have hcap_post : (evaluateHOLFiniteState (decClockHOLFinite s) lbody).2.locals.lookup (ofString "cap") =
              some (.val (.word wcap)) := hcap_keep.trans hcap
          unfold dsMu
          rw [hip, hcap_post, hwi, hcap]
          simp only [if_pos hlt_cap.2, hadd1]
          omega)
      · fb_auto
  · unfold K.«destroy_storage»
    generalize_K
    simp only [Nat.add_zero, Nat.zero_add, Nat.max_def, max_def]
    split_ifs <;> omega

end InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30
