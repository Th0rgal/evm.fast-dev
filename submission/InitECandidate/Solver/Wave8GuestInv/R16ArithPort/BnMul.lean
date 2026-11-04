import InitECandidate.Solver.GuestBoundBlockTxBal
import InitECandidate.Solver.Wave8GuestInv.R10Shards.P13Callees
import InitECandidate.Solver.Wave8GuestInv.R10Shards.P13DivMod

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.R16ArithPort

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup InitECandidate.Solver.GuestUniformClockBound
open InitECandidate.Solver.GuestBoundBlockTxBal
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.P13.Common
open InitECandidate.Solver.Wave8GuestInv.P13.Callees
open InitECandidate.Solver.Wave8GuestInv.P13.DivMod

/-! ### 1. Domain-touch upward rank (`b + i * 8`) for `GuestInv` loops -/

def scaled8UpRank (a : BitVec 64) : Nat :=
  if sourceBase ≤ a.toNat ∧ a.toNat < heapEnd then heapEnd - a.toNat + 15 else 0

theorem scaled8UpRank_bound (a : BitVec 64) : scaled8UpRank a ≤ domainBytes + 16 := by
  unfold scaled8UpRank domainBytes
  split_ifs <;> omega

theorem scaled8UpRank_add8_lt (a : BitVec 64) (ha : sourceBase ≤ a.toNat ∧ a.toNat < heapEnd) :
    scaled8UpRank (a + BitVec.ofNat 64 8) < scaled8UpRank a := by
  have hend : heapEnd + 8 < 2 ^ 64 := by decide
  have hadd : (a + BitVec.ofNat 64 8).toNat = a.toNat + 8 := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  unfold scaled8UpRank
  rw [if_pos ha, hadd]
  split_ifs <;> omega

def scaled8UpMu (base counter : MlS) {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat :=
  match s.locals.lookup base, s.locals.lookup counter with
  | some (.val (.word b)), some (.val (.word i)) => scaled8UpRank (b + i * 8)
  | _, _ => 0

theorem scaled8UpMu_le (base counter : MlS) {F : Type} (s : PanSemStateFiniteExact 64 F) :
    scaled8UpMu base counter s ≤ domainBytes + 16 := by
  unfold scaled8UpMu
  split
  · exact scaled8UpRank_bound _
  · omega

theorem scaled8_locals_inv_up {F : Type} (s : PanSemStateFiniteExact 64 F)
    (base counter : MlS) (address : BitVec 64)
    (h : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .local base, .panop .mul [.var .local counter, .const 8#64]]) =
      some (.val (.word address))) :
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

theorem eval_load_one_domain {F : Type} (s : PanSemStateFiniteExact 64 F)
    (addrExp : ExpHOL 64) (val : ValueHOL 64)
    (h : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.load .one addrExp) = some val) :
    ∃ addr : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        addrExp = some (.val (.word addr)) ∧
      s.memaddrs addr := by
  simp only [evalHOLExact, isWfShapeExactHOL, ↓reduceIte] at h
  split at h
  · rename_i addr haddr
    refine ⟨addr, haddr, ?_⟩
    by_contra hnd
    simp [memLoadHOLExact, hnd] at h
  · cases h

theorem DomainTouch.dec_load_one (name : MlS) (addrExp : ExpHOL 64) (inner : ProgHOL 64) :
    DomainTouch addrExp (.dec name .one (.load .one addrExp) inner) := by
  intro F s hguest hflow
  rw [evaluateHOLFiniteState_dec_total] at hflow
  dsimp only at hflow
  split at hflow
  · simp at hflow
  · rename_i val hval
    obtain ⟨addr, haddr, hdom⟩ := eval_load_one_domain s addrExp val hval
    rw [hguest.memaddrs] at hdom
    have hi := ordinaryDomain_interval addr hdom
    exact ⟨addr, haddr, hi.1, by omega⟩

theorem DomainTouch.dec_inner (address : ExpHOL 64) (name : MlS) (shape : ShapeHOL)
    (init : ExpHOL 64) (inner : ProgHOL 64)
    (havoid : expLocalsAvoided address (.assign .local name (.const 0)) = true)
    (ht : DomainTouch address inner) :
    DomainTouch address (.dec name shape init inner) := by
  intro F s hguest hflow
  rcases hrun : evaluateHOLFiniteState s (.dec name shape init inner) with ⟨res, post⟩
  rw [hrun] at hflow
  obtain ⟨val, mid, hinner, _⟩ := dec_flowing (hflow.elim Or.inl (fun h => Or.inr (Or.inr h))) hrun
  have hflow_in : (evaluateHOLFiniteState (setVarHOLFinite name val s) inner).1 = none ∨
      (evaluateHOLFiniteState (setVarHOLFinite name val s) inner).1 = some .continue := by
    rw [hinner]
    exact hflow
  obtain ⟨addr, haddr, hlo, hhi⟩ := ht (setVarHOLFinite name val s) (guestInv_setVar name val s hguest) hflow_in
  have heq : evalHOLFinite (setVarHOLFinite name val s)
      (h := fun a => Classical.propDecidable ((setVarHOLFinite name val s).memaddrs a)) address =
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) address := by
    apply evalHOLFinite_eq_of_expLocalsAvoided _ _ (.assign .local name (.const 0)) _ address havoid
    intro k hk
    have hne : k ≠ name := by
      intro he; subst he; simp [avoidsLocal] at hk
    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hne]
  rw [evalHOLFinite_eq_toExact, evalHOLFinite_eq_toExact] at heq
  rw [heq] at haddr
  exact ⟨addr, haddr, hlo, hhi⟩

theorem WordExpression.shift (sh : Shift) (a b : ExpHOL 64) : WordExpression (.shift sh a b) := by
  intro F s v h
  simp only [evalHOLExact] at h
  split at h
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨w, _, hw⟩ := h
    exact ⟨w, hw.symm⟩
  · cases h

theorem while_scaled8_up_guestInv (base counter : MlS) (condition : ExpHOL 64)
    {body : ProgHOL 64} {B : Nat}
    (hbody : TerminatingProgBoundedOn GuestInv body B)
    (htouch : DomainTouch (.op .add [.var .local base, .panop .mul [.var .local counter, .const 8#64]]) body)
    (hadd : CounterStep counter 1#64 body)
    (hbase : avoidsLocal base body = true) :
    TerminatingProgBoundedOn GuestInv (.while condition body) ((domainBytes + 16 + 1) * (B + 1)) := by
  refine @TerminatingProgBoundedOn.while_rank GuestInv condition body B (domainBytes + 16)
    (scaled8UpMu base counter)
    (fun s hs => guestInv_decClock s hs) hbody
    (fun s _ _ _ => scaled8UpMu_le base counter s) ?_
  intro F s _ hguest _ hflow
  have hguest' := guestInv_decClock s hguest
  obtain ⟨addr, haddr, hlow, hhigh⟩ := htouch (decClockHOLFinite s) hguest' hflow
  obtain ⟨b, i, hb, hi, rfl⟩ := scaled8_locals_inv_up (decClockHOLFinite s) base counter addr haddr
  have hipost := hadd (decClockHOLFinite s) i hi hflow
  have hbpost := evaluate_avoidsLocal_flowing base body hbase (decClockHOLFinite s)
    (hflow.elim Or.inl (fun h => Or.inr (Or.inr h)))
  change s.locals.lookup base = some (.val (.word b)) at hb
  change s.locals.lookup counter = some (.val (.word i)) at hi
  have hbpost' := hbpost.trans hb
  refine ⟨guestInv_evaluate (decClockHOLFinite s) body hguest', ?_⟩
  have heq : b + (i + 1#64) * 8 = (b + i * 8) + BitVec.ofNat 64 8 := by bv_omega
  simpa only [scaled8UpMu, hipost, hbpost', hb, hi, heq]
    using scaled8UpRank_add8_lt (b + i * 8) ⟨hlow, hhigh⟩

/-! ### 2. `fb_bn_mul` -/

theorem fb_bn_mul : TerminatingFunBoundedOn GuestInv (ofString "bn_mul") K.«bn_mul» := by
  fb_unfold 626 Guest.Software.guestFn_bn_mul
  apply TerminatingProgBoundedOn.weaken'
  · apply dec_guestInv
    apply TerminatingProgBoundedOn.seq_guestInv
    · refine while_scaled8_up_guestInv (ofString "out") (ofString "i") _
        (straightOn _ rfl) ?_ ?_ rfl
      · exact DomainTouch.seq _ _ _ (DomainTouch.store _ _ (WordExpression.const _))
      · exact CounterStep.seq _ _ _ rfl rfl (CounterStep.assign _ 1#64)
    · apply TerminatingProgBoundedOn.seq_guestInv (straightOn _ rfl)
      apply TerminatingProgBoundedOn.seq_guestInv
      · refine while_scaled8_up_guestInv (ofString "a") (ofString "i") _
          (B := (domainBytes + 16 + 1) * (0 + 1) + 0) ?_ ?_ ?_ rfl
        · apply dec_guestInv
          apply dec_guestInv
          apply dec_guestInv
          apply dec_guestInv
          apply TerminatingProgBoundedOn.seq_guestInv
          · refine while_scaled8_up_guestInv (ofString "o") (ofString "j") _
              (dec_guestInv _ _ _ (straightOn _ rfl)) ?_ ?_ rfl
            · exact DomainTouch.dec_inner _ _ _ _ _ rfl
                (DomainTouch.seq _ _ _ (DomainTouch.store _ _ (WordExpression.op _ _)))
            · refine CounterStep.dec _ _ _ _ _ (by decide) ?_
              refine CounterStep.seq _ _ _ rfl rfl ?_
              refine CounterStep.seq _ _ _ rfl rfl ?_
              exact CounterStep.assign _ 1#64
          · exact straightOn _ rfl
        · exact DomainTouch.dec_load_one _ _ _
        · refine CounterStep.dec _ _ _ _ _ (by decide) ?_
          refine CounterStep.dec _ _ _ _ _ (by decide) ?_
          refine CounterStep.dec _ _ _ _ _ (by decide) ?_
          refine CounterStep.dec _ _ _ _ _ (by decide) ?_
          refine CounterStep.seq _ _ _ rfl rfl ?_
          refine CounterStep.seq _ _ _ rfl rfl ?_
          exact CounterStep.assign _ 1#64
      · exact straightOn _ rfl
  · rw [domainBytes_eq]
    unfold K.«bn_mul»
    decide

/-! ### 3. Generic `MemBelow` word-cell preservation combinators and `bn_mul` frame -/

def MemBelow (bound : Nat) {F : Type} (s0 s : PanSemStateFiniteExact 64 F) : Prop :=
  ∀ x : BitVec 64, x.toNat < bound → s.memory x = s0.memory x

theorem memBelow_refl (bound : Nat) {F : Type} (s : PanSemStateFiniteExact 64 F) :
    MemBelow bound s s := fun _ _ => rfl

theorem memBelow_trans {bound : Nat} {F : Type} {s0 s1 s2 : PanSemStateFiniteExact 64 F}
    (h1 : MemBelow bound s0 s1) (h2 : MemBelow bound s1 s2) : MemBelow bound s0 s2 :=
  fun x hx => (h2 x hx).trans (h1 x hx)

theorem memBelow_congr_mem {bound : Nat} {F : Type} {s0 s1 s2 : PanSemStateFiniteExact 64 F}
    (hmem : s2.memory = s1.memory) (h : MemBelow bound s0 s1) : MemBelow bound s0 s2 :=
  fun x hx => (congrFun hmem x).trans (h x hx)

theorem shapeEq_one_iff_word (v : ValueHOL 64) :
    shapeEqHOL ShapeHOL.one (shapeOfHOLExact v) = true ↔ ∃ w : BitVec 64, v = .val (.word w) := by
  constructor
  · intro h
    cases v with
    | val vw => cases vw with | word w => exact ⟨w, rfl⟩
    | rStruct _ => simp [shapeOfHOLExact, shapeEqHOL] at h
    | nStruct _ _ => simp [shapeOfHOLExact, shapeEqHOL] at h
  · rintro ⟨w, rfl⟩
    simp [shapeOfHOLExact, shapeEqHOL]

theorem dec_one_flowing_word {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {name : MlS} {init : ExpHOL 64} {body : ProgHOL 64} {r : Option (PanSemResultExact 64)}
    (flow : Flowing r)
    (run : evaluateHOLFiniteState s (.dec name .one init body) = (r, post)) :
    ∃ (w : BitVec 64) (inner : PanSemStateFiniteExact 64 F),
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) init =
        some (.val (.word w)) ∧
      evaluateHOLFiniteState (setVarHOLFinite name (.val (.word w)) s) body = (r, inner) ∧
      post.memory = inner.memory ∧
      post.globals = inner.globals ∧
      post.locals = HolFiniteMapExact.resVarEq inner.locals (name, s.locals.lookup name) := by
  rw [evaluateHOLFiniteState_dec_total] at run
  dsimp only at run
  split at run
  · simp at run; obtain ⟨rfl, _⟩ := run; rcases flow with h | h | h <;> simp at h
  · rename_i value hval
    split at run
    · rename_i hsh
      obtain ⟨w, rfl⟩ := (shapeEq_one_iff_word value).mp hsh
      cases h : evaluateHOLFiniteState (setVarHOLFinite name (.val (.word w)) s) body with
      | mk r' inner =>
        rw [h] at run
        simp only [Prod.mk.injEq] at run
        obtain ⟨e, p⟩ := run
        subst e
        exact ⟨w, inner, hval, h, by rw [← p], by rw [← p], by rw [← p]⟩
    · simp at run; obtain ⟨rfl, _⟩ := run; rcases flow with h | h | h <;> simp at h

theorem store_one_word_memBelow {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    {bound : Nat} (hm : MemBelow bound s0 s)
    (addrExp valExp : ExpHOL 64) (addr : BitVec 64)
    (haddr : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      addrExp = some (.val (.word addr)))
    (hw : (∃ w : BitVec 64, @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      valExp = some (.val (.word w))) ∨ WordExpression valExp)
    (hge : bound ≤ addr.toNat)
    (hnone : (evaluateHOLFiniteState s (.store addrExp valExp)).1 = none) :
    MemBelow bound s0 (evaluateHOLFiniteState s (.store addrExp valExp)).2 := by
  rw [evaluateHOLFiniteState_store, haddr] at hnone ⊢
  dsimp only at hnone ⊢
  split at hnone
  · rename_i val hval
    have hvw : ∃ w : BitVec 64, val = .val (.word w) := by
      rcases hw with ⟨w0, hw0⟩ | hwe
      · rw [hw0] at hval; injection hval with hv; exact ⟨w0, hv.symm⟩
      · exact hwe s val hval
    obtain ⟨w, rfl⟩ := hvw
    simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL] at hnone ⊢
    by_cases hd : s.memaddrs addr
    · simp only [hd, ↓reduceIte]
      intro x hx
      have hne : x ≠ addr := by intro heq; subst heq; omega
      simp [hne, hm x hx]
    · simp [hd] at hnone
  · simp at hnone

theorem storeByte_memBelow {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    {bound : Nat} (hbound8 : bound % 8 = 0) (hm : MemBelow bound s0 s)
    (addrExp valExp : ExpHOL 64) (addr : BitVec 64)
    (haddr : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      addrExp = some (.val (.word addr)))
    (hge : bound ≤ addr.toNat)
    (hnone : (evaluateHOLFiniteState s (.storeByte addrExp valExp)).1 = none) :
    MemBelow bound s0 (evaluateHOLFiniteState s (.storeByte addrExp valExp)).2 := by
  rw [evaluateHOLFiniteState_storeByte, haddr] at hnone ⊢
  dsimp only at hnone ⊢
  split at hnone
  · split at hnone
    · rename_i mem' hmem
      dsimp only
      intro x hx
      have hne : x ≠ panByteAlignHOL addr := by
        intro heq
        have hal := byteAlign_toNat addr
        rw [← heq] at hal
        omega
      unfold panMemStoreByteWord8HOL at hmem
      cases s.memory (panByteAlignHOL addr) with
      | word cell =>
        dsimp only at hmem
        split at hmem
        · injection hmem with hm_eq
          subst hm_eq
          simp [hne, hm x hx]
        · cases hmem
    · simp at hnone
  · simp at hnone

theorem assign_local_mem_eq {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {name : MlS} {e : ExpHOL 64}
    (hrun : evaluateHOLFiniteState s (.assign .local name e) = (none, post)) :
    post.memory = s.memory ∧ post.globals = s.globals := by
  rw [evaluateHOLFiniteState_assign] at hrun
  split at hrun
  · simp at hrun
  · split at hrun
    · simp only [Prod.mk.injEq] at hrun
      rw [← hrun.2]
      exact ⟨rfl, rfl⟩
    · simp at hrun

def noReturnOrRaiseNoCall : ProgHOL 64 → Bool
  | .seq a b => noReturnOrRaiseNoCall a && noReturnOrRaiseNoCall b
  | .ite _ a b => noReturnOrRaiseNoCall a && noReturnOrRaiseNoCall b
  | .while _ a => noReturnOrRaiseNoCall a
  | .dec _ _ _ a => noReturnOrRaiseNoCall a
  | .assign .local _ _ | .store _ _ | .storeByte _ _ | .skip => true
  | _ => false

theorem evaluate_noReturnOrRaiseNoCall {F : Type} (p : ProgHOL 64)
    (hp : noReturnOrRaiseNoCall p = true) (s : PanSemStateFiniteExact 64 F) :
    ∀ v, (evaluateHOLFiniteState s p).1 ≠ some (.returned v) := by
  cases shape : p with
  | skip => rw [evaluateHOLFiniteState_skip]; simp
  | assign k _ _ =>
    cases k with
    | global => simp [shape, noReturnOrRaiseNoCall] at hp
    | «local» =>
      rw [evaluateHOLFiniteState_assign]
      split <;> [simp; (split <;> simp)]
  | store _ _ =>
    rw [evaluateHOLFiniteState_store]
    split <;> [(split <;> [(split <;> simp); simp]); simp]
  | storeByte _ _ =>
    rw [evaluateHOLFiniteState_storeByte]
    split <;> [(split <;> [(split <;> simp); simp]); simp]
  | dec nm sh init inner =>
    have hb : noReturnOrRaiseNoCall inner = true := by simpa [shape, noReturnOrRaiseNoCall] using hp
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · simp
    · rename_i val _
      split
      · have ih := evaluate_noReturnOrRaiseNoCall inner hb (setVarHOLFinite nm val s)
        cases hr : evaluateHOLFiniteState (setVarHOLFinite nm val s) inner with
        | mk r m =>
          rw [hr] at ih
          exact ih
      · simp
  | seq a b =>
    have hab : noReturnOrRaiseNoCall a = true ∧ noReturnOrRaiseNoCall b = true := by
      simpa [shape, noReturnOrRaiseNoCall, Bool.and_eq_true] using hp
    have rem := evaluateHOLFiniteState_clock_le s a
    rw [evaluateHOLFiniteState_seq_line780]
    have ha := evaluate_noReturnOrRaiseNoCall a hab.1 s
    rcases hr : evaluateHOLFiniteState s a with ⟨r, m⟩
    rw [hr] at ha rem
    cases r with
    | none =>
      have mclk : m.clock ≤ s.clock := rem
      exact evaluate_noReturnOrRaiseNoCall b hab.2 m
    | some _ => exact ha
  | ite _ a b =>
    have hab : noReturnOrRaiseNoCall a = true ∧ noReturnOrRaiseNoCall b = true := by
      simpa [shape, noReturnOrRaiseNoCall, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_noReturnOrRaiseNoCall b hab.2 s
      · exact evaluate_noReturnOrRaiseNoCall a hab.1 s
    · simp
  | «while» cond body =>
    have hb : noReturnOrRaiseNoCall body = true := by simpa [shape, noReturnOrRaiseNoCall] using hp
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · simp
        · have dec_lt : (decClockHOLFinite s).clock < s.clock := by
            simp only [decClockHOLFinite]; omega
          dsimp only
          rw [fixClockHOLFinite_evaluateState]
          have ih1 := evaluate_noReturnOrRaiseNoCall body hb (decClockHOLFinite s)
          have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨r1, mid⟩
          rw [hbr] at ih1 rem
          have smaller : mid.clock < s.clock := by
            change mid.clock ≤ s.clock - 1 at rem
            omega
          cases r1 with
          | none =>
            exact evaluate_noReturnOrRaiseNoCall (.while cond body) (by simpa [noReturnOrRaiseNoCall] using hb) mid
          | some r1 =>
            cases r1 with
            | «continue» =>
              exact evaluate_noReturnOrRaiseNoCall (.while cond body) (by simpa [noReturnOrRaiseNoCall] using hb) mid
            | «returned» _ => exact ih1
            | _ => simp
      · simp
    · simp
  | _ => simp [shape, noReturnOrRaiseNoCall] at hp
termination_by (s.clock, sizeOf p)
decreasing_by
  all_goals
    subst shape
    simp_wf
    first
      | exact Prod.Lex.left _ _ dec_lt
      | exact Prod.Lex.left _ _ smaller
      | exact Prod.Lex.right _ (by simp [setVarHOLFinite]; omega)
      | exact Prod.Lex.right _ (by omega)
      | (rcases Nat.lt_or_eq_of_le mclk with h | h
         · exact Prod.Lex.left _ _ h
         · rw [h]; exact Prod.Lex.right _ (by omega))

private theorem bn_mul_loop1_memBelow {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {bound : Nat} {out0 na0 nb0 : BitVec 64}
    (hout : bound ≤ out0.toNat) (hhi : out0.toNat + (na0.toNat + nb0.toNat) * 8 < 2 ^ 64)
    (k : Nat) (s post : PanSemStateFiniteExact 64 F) (hk : s.clock ≤ k)
    (hm : MemBelow bound s0 s)
    (hl_out : s.locals.lookup (ofString "out") = some (.val (.word out0)))
    (hl_na : s.locals.lookup (ofString "na") = some (.val (.word na0)))
    (hl_nb : s.locals.lookup (ofString "nb") = some (.val (.word nb0)))
    (hl_i : ∃ iw : BitVec 64, s.locals.lookup (ofString "i") = some (.val (.word iw)))
    (hrun : evaluateHOLFiniteState s
      (.while (.cmp .lower (.var .local (ofString "i"))
          (.op .add [.var .local (ofString "na"), .var .local (ofString "nb")]))
        (.seq (.store (.op .add [.var .local (ofString "out"), .panop .mul [.var .local (ofString "i"), .const 8#64]]) (.const 0#64))
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1#64])))) = (none, post)) :
    MemBelow bound s0 post ∧ ∃ iw' : BitVec 64, post.locals.lookup (ofString "i") = some (.val (.word iw')) := by
  induction k generalizing s with
  | zero =>
    obtain ⟨iw, hiw⟩ := hl_i
    rw [evaluateHOLFiniteState_while_total] at hrun
    split at hrun
    · split at hrun
      · split at hrun <;> [simp at hrun; omega]
      · simp at hrun; subst hrun; exact ⟨hm, iw, hiw⟩
    · simp at hrun
  | succ k ih =>
    obtain ⟨iw, hiw⟩ := hl_i
    rw [evaluateHOLFiniteState_while_total] at hrun
    split at hrun
    · rename_i cw hcond
      split at hrun
      · split at hrun
        · simp at hrun
        · rename_i hnz hclk0
          dsimp only at hrun
          rw [fixClockHOLFinite_evaluateState] at hrun
          have hsum_lt : na0.toNat + nb0.toNat < 2 ^ 64 := by omega
          have hnanb : (na0 + nb0).toNat = na0.toNat + nb0.toNat := BitVec.toNat_add_of_lt hsum_lt
          have hi_lt : iw.toNat < na0.toNat + nb0.toNat := by
            unfold PanSemStateFiniteExact.evalHOLFinite at hcond
            simp [evalHOLExact, evalListHOLExact, hiw, hl_na, hl_nb, valueIsWord, valueWord,
              wordOpHOL, wordOp, wordCmpHOL, BitVec.lt_def, hnanb] at hcond
            by_contra hge
            simp [hge] at hcond
            exact hnz hcond.symm
          set body := ProgHOL.seq
            (.store (.op .add [.var .local (ofString "out"), .panop .mul [.var .local (ofString "i"), .const 8#64]]) (.const 0#64))
            (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1#64]))
          have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
          have nc := evaluate_noTopContinue body rfl (decClockHOLFinite s)
          have nb := GuestUniformClockBound.evaluate_noTopBreak body rfl (decClockHOLFinite s)
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨r1, mid⟩
          rw [hbr] at hrun rem nc nb
          cases r1 with
          | some r1 => cases r1 <;> simp_all
          | none =>
            dsimp only at hrun
            have hbr' := hbr
            dsimp only [body] at hbr'
            rw [evaluateHOLFiniteState_seq_line780] at hbr'
            have hsf := evaluate_store_control_frame (decClockHOLFinite s)
              (.op .add [.var .local (ofString "out"), .panop .mul [.var .local (ofString "i"), .const 8#64]]) (.const 0#64)
            rcases hst : evaluateHOLFiniteState (decClockHOLFinite s)
              (.store (.op .add [.var .local (ofString "out"), .panop .mul [.var .local (ofString "i"), .const 8#64]]) (.const 0#64)) with ⟨rs, smid⟩
            rw [hst] at hbr' hsf
            cases rs with
            | some _ => simp at hbr'
            | none =>
              dsimp only at hbr' hsf
              have haddr : @evalHOLExact 64 F _ (decClockHOLFinite s).toExact
                  (fun a => Classical.propDecidable ((decClockHOLFinite s).memaddrs a))
                  (.op .add [.var .local (ofString "out"), .panop .mul [.var .local (ofString "i"), .const 8#64]]) =
                  some (.val (.word (out0 + iw * 8#64))) := by
                simp [decClockHOLFinite, evalHOLExact, evalListHOLExact, hl_out, hiw,
                  valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL]
              have hge_addr : bound ≤ (out0 + iw * 8#64).toNat := by
                have hi8 : (iw * 8#64).toNat = iw.toNat * 8 := by
                  rw [BitVec.toNat_mul]
                  change (iw.toNat * 8) % 18446744073709551616 = iw.toNat * 8
                  omega
                have hadd : (out0 + iw * 8#64).toNat = out0.toNat + iw.toNat * 8 := by
                  rw [BitVec.toNat_add, hi8]
                  change (out0.toNat + iw.toNat * 8) % 18446744073709551616 = out0.toNat + iw.toNat * 8
                  omega
                omega
              have hm_smid : MemBelow bound s0 smid := by
                have := store_one_word_memBelow (s0 := s0) (s := decClockHOLFinite s) hm _ _ (out0 + iw * 8#64)
                  haddr (Or.inr (WordExpression.const _)) hge_addr (by rw [hst])
                rw [hst] at this; exact this
              have hl_smid : smid.locals = s.locals := hsf.2.1
              have hiw_smid : smid.locals.lookup (ofString "i") = some (.val (.word iw)) := by
                rw [hl_smid]; exact hiw
              have hass : evaluateHOLFiniteState smid
                  (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1#64])) =
                  (none, setVarHOLFinite (ofString "i") (.val (.word (iw + 1#64))) smid) := by
                simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hiw_smid,
                  wordOpHOL, wordOp, valueIsWord, valueWord, lookupKvarHOLExact,
                  isValidValueHOLExact, setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL]
              rw [hass] at hbr'
              injection hbr' with _ hmid
              subst hmid
              exact ih (setVarHOLFinite (ofString "i") (.val (.word (iw + 1#64))) smid)
                (by change (setVarHOLFinite _ _ smid).clock ≤ s.clock - 1 at rem; simp only [setVarHOLFinite] at rem ⊢; omega)
                hm_smid
                (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hl_smid, hl_out, show ofString "i" ≠ ofString "out" by decide])
                (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hl_smid, hl_na, show ofString "i" ≠ ofString "na" by decide])
                (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hl_smid, hl_nb, show ofString "i" ≠ ofString "nb" by decide])
                ⟨iw + 1#64, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩
                hrun
      · simp at hrun; subst hrun; exact ⟨hm, iw, hiw⟩
    · simp at hrun

private theorem bn_mul_inner_memBelow {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {bound : Nat} {o0 nb0 : BitVec 64}
    (ho : bound ≤ o0.toNat) (hhi : o0.toNat + nb0.toNat * 8 < 2 ^ 64)
    (k : Nat) (s post : PanSemStateFiniteExact 64 F) (hk : s.clock ≤ k)
    (hm : MemBelow bound s0 s)
    (hl_o : s.locals.lookup (ofString "o") = some (.val (.word o0)))
    (hl_nb : s.locals.lookup (ofString "nb") = some (.val (.word nb0)))
    (hl_j : ∃ jw : BitVec 64, s.locals.lookup (ofString "j") = some (.val (.word jw)))
    (hl_c : ∃ cw : BitVec 64, s.locals.lookup (ofString "carry") = some (.val (.word cw)))
    (hrun : evaluateHOLFiniteState s
      (.while (.cmp .lower (.var .local (ofString "j")) (.var .local (ofString "nb")))
        (.dec (ofString "t") .one
          (.op .add [
            .panop .mul [.var .local (ofString "ai"),
              .load .one (.op .add [.var .local (ofString "b"), .panop .mul [.var .local (ofString "j"), .const 8#64]])],
            .load .one (.op .add [.var .local (ofString "o"), .panop .mul [.var .local (ofString "j"), .const 8#64]]),
            .var .local (ofString "carry")])
          (.seq
            (.store (.op .add [.var .local (ofString "o"), .panop .mul [.var .local (ofString "j"), .const 8#64]])
              (.op .and [.var .local (ofString "t"), .const 4294967295#64]))
            (.seq
              (.assign .local (ofString "carry") (.shift .lsr (.var .local (ofString "t")) (.const 32#64)))
              (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"), .const 1#64])))))) = (none, post)) :
    MemBelow bound s0 post ∧ ∃ cw : BitVec 64, post.locals.lookup (ofString "carry") = some (.val (.word cw)) := by
  induction k generalizing s with
  | zero =>
    rw [evaluateHOLFiniteState_while_total] at hrun
    split at hrun
    · split at hrun
      · split at hrun <;> [simp at hrun; omega]
      · simp at hrun; subst hrun; exact ⟨hm, hl_c⟩
    · simp at hrun
  | succ k ih =>
    obtain ⟨jw, hjw⟩ := hl_j
    rw [evaluateHOLFiniteState_while_total] at hrun
    split at hrun
    · rename_i cw hcond
      split at hrun
      · split at hrun
        · simp at hrun
        · rename_i hnz hclk0
          dsimp only at hrun
          rw [fixClockHOLFinite_evaluateState] at hrun
          have hj_lt : jw.toNat < nb0.toNat := by
            unfold PanSemStateFiniteExact.evalHOLFinite at hcond
            simp [evalHOLExact, hjw, hl_nb, wordCmpHOL, BitVec.lt_def] at hcond
            by_contra hge
            simp [hge] at hcond
            exact hnz hcond.symm
          set body : ProgHOL 64 := .dec (ofString "t") .one _ _
          have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
          have nc := evaluate_noTopContinue body rfl (decClockHOLFinite s)
          have nb := GuestUniformClockBound.evaluate_noTopBreak body rfl (decClockHOLFinite s)
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨r1, mid⟩
          rw [hbr] at hrun rem nc nb
          cases r1 with
          | some r1 => cases r1 <;> simp_all
          | none =>
            dsimp only at hrun
            obtain ⟨tw, innerPost, _, hinner, hmem_mid, _, hloc_mid⟩ := dec_one_flowing_word (Or.inl rfl) hbr
            let st := setVarHOLFinite (ofString "t") (.val (.word tw)) (decClockHOLFinite s)
            have hj_st : st.locals.lookup (ofString "j") = some (.val (.word jw)) := by
              simp [st, decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hjw,
                show ofString "t" ≠ ofString "j" by decide]
            have ho_st : st.locals.lookup (ofString "o") = some (.val (.word o0)) := by
              simp [st, decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hl_o,
                show ofString "t" ≠ ofString "o" by decide]
            have ht_st : st.locals.lookup (ofString "t") = some (.val (.word tw)) := by
              simp [st, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
            rw [evaluateHOLFiniteState_seq_line780] at hinner
            have hsf := evaluate_store_control_frame st
              (.op .add [.var .local (ofString "o"), .panop .mul [.var .local (ofString "j"), .const 8#64]])
              (.op .and [.var .local (ofString "t"), .const 4294967295#64])
            rcases hst : evaluateHOLFiniteState st
              (.store (.op .add [.var .local (ofString "o"), .panop .mul [.var .local (ofString "j"), .const 8#64]])
                (.op .and [.var .local (ofString "t"), .const 4294967295#64])) with ⟨rs, sm1⟩
            rw [hst] at hinner hsf
            cases rs with
            | some _ => simp at hinner
            | none =>
              dsimp only at hinner hsf
              have haddr : @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a))
                  (.op .add [.var .local (ofString "o"), .panop .mul [.var .local (ofString "j"), .const 8#64]]) =
                  some (.val (.word (o0 + jw * 8#64))) := by
                simp [evalHOLExact, evalListHOLExact, ho_st, hj_st, valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL]
              have hge_addr : bound ≤ (o0 + jw * 8#64).toNat := by
                have hj8 : (jw * 8#64).toNat = jw.toNat * 8 := by
                  rw [BitVec.toNat_mul]
                  change (jw.toNat * 8) % 18446744073709551616 = jw.toNat * 8
                  omega
                have hadd : (o0 + jw * 8#64).toNat = o0.toNat + jw.toNat * 8 := by
                  rw [BitVec.toNat_add, hj8]
                  change (o0.toNat + jw.toNat * 8) % 18446744073709551616 = o0.toNat + jw.toNat * 8
                  omega
                omega
              have hm_sm1 : MemBelow bound s0 sm1 := by
                have := store_one_word_memBelow (s0 := s0) (s := st) hm _ _ (o0 + jw * 8#64)
                  haddr (Or.inr (WordExpression.op _ _)) hge_addr (by rw [hst])
                rw [hst] at this; exact this
              rw [evaluateHOLFiniteState_seq_line780] at hinner
              have ht_sm1 : sm1.locals.lookup (ofString "t") = some (.val (.word tw)) :=
                hsf.2.1.symm ▸ ht_st
              obtain ⟨cw_prev, hcw_prev⟩ := hl_c
              have hc_sm1 : sm1.locals.lookup (ofString "carry") = some (.val (.word cw_prev)) := by
                rw [hsf.2.1]
                simp [st, decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hcw_prev,
                  show ofString "t" ≠ ofString "carry" by decide]
              have hass_c : evaluateHOLFiniteState sm1
                  (.assign .local (ofString "carry") (.shift .lsr (.var .local (ofString "t")) (.const 32#64))) =
                  (none, setVarHOLFinite (ofString "carry") (.val (.word (tw >>> 32))) sm1) := by
                simp [evaluateHOLFiniteState_assign, evalHOLExact, ht_sm1, hc_sm1, wordShiftHOL,
                  lookupKvarHOLExact, isValidValueHOLExact, setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL]
              rw [hass_c] at hinner
              dsimp only at hinner
              let sm2 := setVarHOLFinite (ofString "carry") (.val (.word (tw >>> 32))) sm1
              have hj_sm2 : sm2.locals.lookup (ofString "j") = some (.val (.word jw)) := by
                simp [sm2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsf.2.1, hj_st,
                  show ofString "carry" ≠ ofString "j" by decide]
              have hass_j : evaluateHOLFiniteState sm2
                  (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"), .const 1#64])) =
                  (none, setVarHOLFinite (ofString "j") (.val (.word (jw + 1#64))) sm2) := by
                simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hj_sm2,
                  wordOpHOL, wordOp, valueIsWord, valueWord, lookupKvarHOLExact,
                  isValidValueHOLExact, setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL]
              rw [hass_j] at hinner
              injection hinner with _ hpost_eq
              have hm_mid : MemBelow bound s0 mid := by
                refine memBelow_congr_mem hmem_mid ?_
                rw [← hpost_eq]
                exact hm_sm1
              have ho_mid : mid.locals.lookup (ofString "o") = some (.val (.word o0)) := by
                have hfr := evaluate_avoidsLocal_flowing (ofString "o") body rfl (decClockHOLFinite s)
                  (by rw [hbr]; exact Or.inl rfl)
                rw [hbr] at hfr; exact hfr.trans hl_o
              have hnb_mid : mid.locals.lookup (ofString "nb") = some (.val (.word nb0)) := by
                have hfr := evaluate_avoidsLocal_flowing (ofString "nb") body rfl (decClockHOLFinite s)
                  (by rw [hbr]; exact Or.inl rfl)
                rw [hbr] at hfr; exact hfr.trans hl_nb
              have hj_mid : mid.locals.lookup (ofString "j") = some (.val (.word (jw + 1#64))) := by
                rw [hloc_mid, PanRunBounded.resVarEq_lookup, if_neg (show ofString "j" ≠ ofString "t" by decide), ← hpost_eq]
                simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
              have hc_mid : mid.locals.lookup (ofString "carry") = some (.val (.word (tw >>> 32))) := by
                rw [hloc_mid, PanRunBounded.resVarEq_lookup, if_neg (show ofString "carry" ≠ ofString "t" by decide), ← hpost_eq]
                simp [sm2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "j" ≠ ofString "carry" by decide]
              exact ih mid (by change mid.clock ≤ s.clock - 1 at rem; omega) hm_mid ho_mid hnb_mid
                ⟨jw + 1#64, hj_mid⟩ ⟨_, hc_mid⟩ hrun
      · simp at hrun; subst hrun; exact ⟨hm, hl_c⟩
    · simp at hrun

private theorem bn_mul_loop2_memBelow {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {bound : Nat} {out0 na0 nb0 : BitVec 64}
    (hout : bound ≤ out0.toNat) (hhi : out0.toNat + (na0.toNat + nb0.toNat) * 8 < 2 ^ 64)
    (k : Nat) (s post : PanSemStateFiniteExact 64 F) (hk : s.clock ≤ k)
    (hm : MemBelow bound s0 s)
    (hl_out : s.locals.lookup (ofString "out") = some (.val (.word out0)))
    (hl_na : s.locals.lookup (ofString "na") = some (.val (.word na0)))
    (hl_nb : s.locals.lookup (ofString "nb") = some (.val (.word nb0)))
    (hl_i : ∃ iw : BitVec 64, s.locals.lookup (ofString "i") = some (.val (.word iw)))
    (hrun : evaluateHOLFiniteState s
      (.while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "na")))
        (.dec (ofString "ai") .one
          (.load .one (.op .add [.var .local (ofString "a"), .panop .mul [.var .local (ofString "i"), .const 8#64]]))
          (.dec (ofString "carry") .one (.const 0#64)
            (.dec (ofString "j") .one (.const 0#64)
              (.dec (ofString "o") .one (.op .add [.var .local (ofString "out"), .panop .mul [.var .local (ofString "i"), .const 8#64]])
                (.seq
                  (.while (.cmp .lower (.var .local (ofString "j")) (.var .local (ofString "nb")))
                    (.dec (ofString "t") .one
                      (.op .add [
                        .panop .mul [.var .local (ofString "ai"),
                          .load .one (.op .add [.var .local (ofString "b"), .panop .mul [.var .local (ofString "j"), .const 8#64]])],
                        .load .one (.op .add [.var .local (ofString "o"), .panop .mul [.var .local (ofString "j"), .const 8#64]]),
                        .var .local (ofString "carry")])
                      (.seq
                        (.store (.op .add [.var .local (ofString "o"), .panop .mul [.var .local (ofString "j"), .const 8#64]])
                          (.op .and [.var .local (ofString "t"), .const 4294967295#64]))
                        (.seq
                          (.assign .local (ofString "carry") (.shift .lsr (.var .local (ofString "t")) (.const 32#64)))
                          (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"), .const 1#64]))))))
                  (.seq
                    (.store (.op .add [.var .local (ofString "o"), .panop .mul [.var .local (ofString "nb"), .const 8#64]])
                      (.var .local (ofString "carry")))
                    (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1#64]))))))))) = (none, post)) :
    MemBelow bound s0 post := by
  induction k generalizing s with
  | zero =>
    rw [evaluateHOLFiniteState_while_total] at hrun
    split at hrun
    · split at hrun
      · split at hrun <;> [simp at hrun; omega]
      · simp at hrun; subst hrun; exact hm
    · simp at hrun
  | succ k ih =>
    obtain ⟨iw, hiw⟩ := hl_i
    rw [evaluateHOLFiniteState_while_total] at hrun
    split at hrun
    · rename_i cw hcond
      split at hrun
      · split at hrun
        · simp at hrun
        · rename_i hnz hclk0
          dsimp only at hrun
          rw [fixClockHOLFinite_evaluateState] at hrun
          have hi_lt : iw.toNat < na0.toNat := by
            unfold PanSemStateFiniteExact.evalHOLFinite at hcond
            simp [evalHOLExact, hiw, hl_na, wordCmpHOL, BitVec.lt_def] at hcond
            by_contra hge; simp [hge] at hcond; exact hnz hcond.symm
          set body : ProgHOL 64 := .dec (ofString "ai") .one _ _
          have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
          have nc := evaluate_noTopContinue body rfl (decClockHOLFinite s)
          have nb := GuestUniformClockBound.evaluate_noTopBreak body rfl (decClockHOLFinite s)
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨r1, mid⟩
          rw [hbr] at hrun rem nc nb
          cases r1 with
          | some r1 => cases r1 <;> simp_all
          | none =>
            dsimp only at hrun
            obtain ⟨aiw, p1, _, hp1, hm1, _, hl1⟩ := dec_one_flowing_word (Or.inl rfl) hbr
            obtain ⟨cw0, p2, _, hp2, hm2, _, hl2⟩ := dec_one_flowing_word (Or.inl rfl) hp1
            obtain ⟨jw0, p3, _, hp3, hm3, _, hl3⟩ := dec_one_flowing_word (Or.inl rfl) hp2
            obtain ⟨ow0, p4, hov, hp4, hm4, _, hl4⟩ := dec_one_flowing_word (Or.inl rfl) hp3
            let s1 := setVarHOLFinite (ofString "ai") (.val (.word aiw)) (decClockHOLFinite s)
            let s2 := setVarHOLFinite (ofString "carry") (.val (.word cw0)) s1
            let s3 := setVarHOLFinite (ofString "j") (.val (.word jw0)) s2
            let s4 := setVarHOLFinite (ofString "o") (.val (.word ow0)) s3
            have how0 : ow0 = out0 + iw * 8#64 := by
              have ho3 : (setVarHOLFinite (ofString "j") (.val (.word jw0))
                  (setVarHOLFinite (ofString "carry") (.val (.word cw0))
                    (setVarHOLFinite (ofString "ai") (.val (.word aiw)) (decClockHOLFinite s)))).locals.lookup
                  (ofString "out") = some (.val (.word out0)) := by
                simp [decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hl_out,
                  show ofString "j" ≠ ofString "out" by decide, show ofString "carry" ≠ ofString "out" by decide,
                  show ofString "ai" ≠ ofString "out" by decide]
              have hi3 : (setVarHOLFinite (ofString "j") (.val (.word jw0))
                  (setVarHOLFinite (ofString "carry") (.val (.word cw0))
                    (setVarHOLFinite (ofString "ai") (.val (.word aiw)) (decClockHOLFinite s)))).locals.lookup
                  (ofString "i") = some (.val (.word iw)) := by
                simp [decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hiw,
                  show ofString "j" ≠ ofString "i" by decide, show ofString "carry" ≠ ofString "i" by decide,
                  show ofString "ai" ≠ ofString "i" by decide]
              simp only [evalHOLExact, evalListHOLExact] at hov
              rw [ho3, hi3] at hov
              simp [valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL] at hov
              exact hov.symm
            subst how0
            have hi8 : (iw * 8#64).toNat = iw.toNat * 8 := by
              rw [BitVec.toNat_mul]
              change (iw.toNat * 8) % 18446744073709551616 = iw.toNat * 8
              omega
            have ho_toNat : (out0 + iw * 8#64).toNat = out0.toNat + iw.toNat * 8 := by
              rw [BitVec.toNat_add, hi8]
              change (out0.toNat + iw.toNat * 8) % 18446744073709551616 = out0.toNat + iw.toNat * 8
              omega
            rw [evaluateHOLFiniteState_seq_line780] at hp4
            rcases hwin : evaluateHOLFiniteState s4 _ with ⟨rin, sin⟩
            rw [hwin] at hp4
            cases rin with
            | some _ => simp at hp4
            | none =>
              dsimp only at hp4
              obtain ⟨hm_sin, cw_sin, hcw_sin⟩ :=
                bn_mul_inner_memBelow (o0 := out0 + iw * 8#64) (nb0 := nb0)
                  (by omega) (by omega) s4.clock s4 sin le_rfl hm
                  (by simp [s4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
                  (by simp [s4, s3, s2, s1, decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hl_nb,
                      show ofString "o" ≠ ofString "nb" by decide, show ofString "j" ≠ ofString "nb" by decide,
                      show ofString "carry" ≠ ofString "nb" by decide, show ofString "ai" ≠ ofString "nb" by decide])
                  ⟨jw0, by simp [s4, s3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                      show ofString "o" ≠ ofString "j" by decide]⟩
                  ⟨cw0, by simp [s4, s3, s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                      show ofString "o" ≠ ofString "carry" by decide, show ofString "j" ≠ ofString "carry" by decide]⟩
                  hwin
              have ho_sin : sin.locals.lookup (ofString "o") = some (.val (.word (out0 + iw * 8#64))) := by
                have hfr := evaluate_avoidsLocal_flowing (ofString "o") _ rfl s4 (by rw [hwin]; exact Or.inl rfl)
                rw [hwin] at hfr
                exact hfr.trans (by simp [s4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
              have hnb_sin : sin.locals.lookup (ofString "nb") = some (.val (.word nb0)) := by
                have hfr := evaluate_avoidsLocal_flowing (ofString "nb") _ rfl s4 (by rw [hwin]; exact Or.inl rfl)
                rw [hwin] at hfr
                exact hfr.trans (by simp [s4, s3, s2, s1, decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hl_nb,
                    show ofString "o" ≠ ofString "nb" by decide, show ofString "j" ≠ ofString "nb" by decide,
                    show ofString "carry" ≠ ofString "nb" by decide, show ofString "ai" ≠ ofString "nb" by decide])
              have hi_sin : sin.locals.lookup (ofString "i") = some (.val (.word iw)) := by
                have hfr := evaluate_avoidsLocal_flowing (ofString "i") _ rfl s4 (by rw [hwin]; exact Or.inl rfl)
                rw [hwin] at hfr
                exact hfr.trans (by simp [s4, s3, s2, s1, decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hiw,
                    show ofString "o" ≠ ofString "i" by decide, show ofString "j" ≠ ofString "i" by decide,
                    show ofString "carry" ≠ ofString "i" by decide, show ofString "ai" ≠ ofString "i" by decide])
              rw [evaluateHOLFiniteState_seq_line780] at hp4
              have hsf := evaluate_store_control_frame sin
                (.op .add [.var .local (ofString "o"), .panop .mul [.var .local (ofString "nb"), .const 8#64]])
                (.var .local (ofString "carry"))
              rcases hst : evaluateHOLFiniteState sin
                (.store (.op .add [.var .local (ofString "o"), .panop .mul [.var .local (ofString "nb"), .const 8#64]])
                  (.var .local (ofString "carry"))) with ⟨rs, sm1⟩
              rw [hst] at hp4 hsf
              cases rs with
              | some _ => simp at hp4
              | none =>
                dsimp only at hp4 hsf
                have haddr : @evalHOLExact 64 F _ sin.toExact (fun a => Classical.propDecidable (sin.memaddrs a))
                    (.op .add [.var .local (ofString "o"), .panop .mul [.var .local (ofString "nb"), .const 8#64]]) =
                    some (.val (.word ((out0 + iw * 8#64) + nb0 * 8#64))) := by
                  simp [evalHOLExact, evalListHOLExact, ho_sin, hnb_sin, valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL]
                have hge_addr : bound ≤ ((out0 + iw * 8#64) + nb0 * 8#64).toNat := by
                  have hnb8 : (nb0 * 8#64).toNat = nb0.toNat * 8 := by
                    rw [BitVec.toNat_mul]
                    change (nb0.toNat * 8) % 18446744073709551616 = nb0.toNat * 8
                    omega
                  have hadd : ((out0 + iw * 8#64) + nb0 * 8#64).toNat = (out0 + iw * 8#64).toNat + nb0.toNat * 8 := by
                    rw [BitVec.toNat_add, hnb8]
                    change ((out0 + iw * 8#64).toNat + nb0.toNat * 8) % 18446744073709551616 = (out0 + iw * 8#64).toNat + nb0.toNat * 8
                    omega
                  omega
                have hval_c : @evalHOLExact 64 F _ sin.toExact (fun a => Classical.propDecidable (sin.memaddrs a))
                    (.var .local (ofString "carry")) = some (.val (.word cw_sin)) := by
                  simpa [evalHOLExact] using hcw_sin
                have hm_sm1 : MemBelow bound s0 sm1 := by
                  have := store_one_word_memBelow (s0 := s0) (s := sin) hm_sin _ _ ((out0 + iw * 8#64) + nb0 * 8#64)
                    haddr (Or.inl ⟨cw_sin, hval_c⟩) hge_addr (by rw [hst])
                  rw [hst] at this; exact this
                have hi_sm1 : sm1.locals.lookup (ofString "i") = some (.val (.word iw)) :=
                  hsf.2.1.symm ▸ hi_sin
                have hass_i : evaluateHOLFiniteState sm1
                    (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1#64])) =
                    (none, setVarHOLFinite (ofString "i") (.val (.word (iw + 1#64))) sm1) := by
                  simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hi_sm1,
                    wordOpHOL, wordOp, valueIsWord, valueWord, lookupKvarHOLExact,
                    isValidValueHOLExact, setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL]
                rw [hass_i] at hp4
                injection hp4 with _ hp4_eq
                have hm_mid : MemBelow bound s0 mid := by
                  refine memBelow_congr_mem (hm1.trans (hm2.trans (hm3.trans hm4))) ?_
                  rw [← hp4_eq]
                  exact hm_sm1
                have hout_mid : mid.locals.lookup (ofString "out") = some (.val (.word out0)) := by
                  have hfr := evaluate_avoidsLocal_flowing (ofString "out") body rfl (decClockHOLFinite s)
                    (by rw [hbr]; exact Or.inl rfl)
                  rw [hbr] at hfr; exact hfr.trans hl_out
                have hna_mid : mid.locals.lookup (ofString "na") = some (.val (.word na0)) := by
                  have hfr := evaluate_avoidsLocal_flowing (ofString "na") body rfl (decClockHOLFinite s)
                    (by rw [hbr]; exact Or.inl rfl)
                  rw [hbr] at hfr; exact hfr.trans hl_na
                have hnb_mid : mid.locals.lookup (ofString "nb") = some (.val (.word nb0)) := by
                  have hfr := evaluate_avoidsLocal_flowing (ofString "nb") body rfl (decClockHOLFinite s)
                    (by rw [hbr]; exact Or.inl rfl)
                  rw [hbr] at hfr; exact hfr.trans hl_nb
                have hi_mid : mid.locals.lookup (ofString "i") = some (.val (.word (iw + 1#64))) := by
                  rw [hl1, PanRunBounded.resVarEq_lookup, if_neg (show ofString "i" ≠ ofString "ai" by decide),
                      hl2, PanRunBounded.resVarEq_lookup, if_neg (show ofString "i" ≠ ofString "carry" by decide),
                      hl3, PanRunBounded.resVarEq_lookup, if_neg (show ofString "i" ≠ ofString "j" by decide),
                      hl4, PanRunBounded.resVarEq_lookup, if_neg (show ofString "i" ≠ ofString "o" by decide),
                      ← hp4_eq]
                  simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                exact ih mid (by change mid.clock ≤ s.clock - 1 at rem; omega) hm_mid hout_mid hna_mid hnb_mid
                  ⟨iw + 1#64, hi_mid⟩ hrun
      · simp at hrun; subst hrun; exact hm
    · simp at hrun

/-- Body-level `MemBelow bound` preservation for `bn_mul(a, na, b, nb, out)` on any normal return
when `bound ≤ out.toNat` and `out.toNat + (na.toNat + nb.toNat) * 8 < 2 ^ 64`. -/
theorem bn_mul_body_memBelow {F : Type} (s : PanSemStateFiniteExact 64 F)
    {bound : Nat} {out0 na0 nb0 : BitVec 64}
    (hl_out : s.locals.lookup (ofString "out") = some (.val (.word out0)))
    (hl_na : s.locals.lookup (ofString "na") = some (.val (.word na0)))
    (hl_nb : s.locals.lookup (ofString "nb") = some (.val (.word nb0)))
    (hout : bound ≤ out0.toNat)
    (hhi : out0.toNat + (na0.toNat + nb0.toNat) * 8 < 2 ^ 64)
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_bn_mul)).1 = some (.returned v)) :
    MemBelow bound s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_bn_mul)).2 := by
  revert hret
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_bn_mul,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only [evalHOLExact]
  rw [if_pos (by simp [shapeOfHOLExact, shapeEqHOL])]
  dsimp only
  set s1 := setVarHOLFinite (ofString "i") (.val (.word 0#64)) s
  rw [evaluateHOLFiniteState_seq_line780]
  set loop1 : ProgHOL 64 := .while _ _
  have hl1_nr := evaluate_noReturnOrRaiseNoCall loop1 rfl s1 v
  rcases hw1 : evaluateHOLFiniteState s1 loop1 with ⟨r1, s2⟩
  cases r1 with
  | some _ =>
    intro hret
    rw [hw1] at hl1_nr
    exact absurd hret hl1_nr
  | none =>
    dsimp only
    have ⟨hm_s2, iw2, hiw2⟩ :=
      bn_mul_loop1_memBelow hout hhi s1.clock s1 s2 le_rfl (memBelow_refl bound s)
        (by simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hl_out, show ofString "i" ≠ ofString "out" by decide])
        (by simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hl_na, show ofString "i" ≠ ofString "na" by decide])
        (by simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hl_nb, show ofString "i" ≠ ofString "nb" by decide])
        ⟨0#64, by simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩
        hw1
    have hout_s2 : s2.locals.lookup (ofString "out") = some (.val (.word out0)) := by
      have hfr := evaluate_avoidsLocal_flowing (ofString "out") loop1 rfl s1 (by rw [hw1]; exact Or.inl rfl)
      rw [hw1] at hfr
      exact hfr.trans (by simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hl_out, show ofString "i" ≠ ofString "out" by decide])
    have hna_s2 : s2.locals.lookup (ofString "na") = some (.val (.word na0)) := by
      have hfr := evaluate_avoidsLocal_flowing (ofString "na") loop1 rfl s1 (by rw [hw1]; exact Or.inl rfl)
      rw [hw1] at hfr
      exact hfr.trans (by simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hl_na, show ofString "i" ≠ ofString "na" by decide])
    have hnb_s2 : s2.locals.lookup (ofString "nb") = some (.val (.word nb0)) := by
      have hfr := evaluate_avoidsLocal_flowing (ofString "nb") loop1 rfl s1 (by rw [hw1]; exact Or.inl rfl)
      rw [hw1] at hfr
      exact hfr.trans (by simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hl_nb, show ofString "i" ≠ ofString "nb" by decide])
    rw [evaluateHOLFiniteState_seq_line780]
    set assProg : ProgHOL 64 := .assign .local (ofString "i") _
    rcases hass : evaluateHOLFiniteState s2 assProg with ⟨ra, s3⟩
    cases ra with
    | some _ =>
      intro hret
      have hnr := evaluate_noReturnOrRaiseNoCall assProg rfl s2 v
      rw [hass] at hnr
      exact absurd hret hnr
    | none =>
      dsimp only
      have hass_eq : s3 = setVarHOLFinite (ofString "i") (.val (.word 0#64)) s2 := by
        have hc_ass : evaluateHOLFiniteState s2 assProg = (none, s3) := hass
        dsimp only [assProg] at hc_ass
        simp [evaluateHOLFiniteState_assign, evalHOLExact, hiw2, lookupKvarHOLExact,
          isValidValueHOLExact, setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL] at hc_ass
        exact hc_ass.symm
      rw [evaluateHOLFiniteState_seq_line780]
      set loop2 : ProgHOL 64 := .while _ _
      have hl2_nr := evaluate_noReturnOrRaiseNoCall loop2 rfl s3 v
      rcases hw2 : evaluateHOLFiniteState s3 loop2 with ⟨r2, s4⟩
      cases r2 with
      | some _ =>
        intro hret
        rw [hw2] at hl2_nr
        exact absurd hret hl2_nr
      | none =>
        dsimp only
        intro _
        have hm_s3 : MemBelow bound s s3 := by rw [hass_eq]; exact hm_s2
        have hout_s3 : s3.locals.lookup (ofString "out") = some (.val (.word out0)) := by
          rw [hass_eq]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hout_s2, show ofString "i" ≠ ofString "out" by decide]
        have hna_s3 : s3.locals.lookup (ofString "na") = some (.val (.word na0)) := by
          rw [hass_eq]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hna_s2, show ofString "i" ≠ ofString "na" by decide]
        have hnb_s3 : s3.locals.lookup (ofString "nb") = some (.val (.word nb0)) := by
          rw [hass_eq]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hnb_s2, show ofString "i" ≠ ofString "nb" by decide]
        have hi_s3 : ∃ iw : BitVec 64, s3.locals.lookup (ofString "i") = some (.val (.word iw)) := by
          rw [hass_eq]; exact ⟨0#64, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩
        have hm_s4 : MemBelow bound s s4 :=
          bn_mul_loop2_memBelow hout hhi s3.clock s3 s4 le_rfl hm_s3 hout_s3 hna_s3 hnb_s3 hi_s3 hw2
        have hret_eval : evaluateHOLFiniteState s4 (.return (.const 0#64)) =
            (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite s4) := by
          simp [evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL]
        rw [hret_eval]
        exact hm_s4

end InitECandidate.Solver.Wave8GuestInv.R16ArithPort
