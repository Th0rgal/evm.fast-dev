import InitECandidate.Solver.Wave8GuestInv.ContractParts.C03
import InitECandidate.Solver.GuestTrapOutcomes
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M08.wk_memcpy
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M08.wk_memzero
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M13.WorldFrame
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M21.dm_memcpy

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R13Shards.Keccak256

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

abbrev sourceBase_val := M13.sourceBase_val
abbrev heapEnd_val := M13.heapEnd_val

theorem ordinaryDomain_iff (x : BitVec 64) :
    ordinaryDomain x ↔ x.toNat % 8 = 0 ∧ sourceBase ≤ x.toNat ∧ x.toNat < heapEnd :=
  Wave8Contracts.M08.ordinaryDomain_iff x

def CellHitsPos (a : Nat) (i : Ivl) : Prop := 0 < i.2 ∧ CellHits a i

theorem resVarEq_lookup_ne (m : HolFiniteMapExact MlS (ValueHOL 64)) (name n : MlS)
    (o : Option (ValueHOL 64)) (h : n ≠ name) :
    (HolFiniteMapExact.resVarEq m (name, o)).lookup n = m.lookup n := by
  rcases o with _ | v
  · simp [HolFiniteMapExact.resVarEq, HolFiniteMapExact.eraseEq, FDOMSUB_HOL, h]
  · simp only [HolFiniteMapExact.resVarEq, HolFiniteMapExact.updateEq, FUPDATE_HOL]
    split
    · rename_i heq; exact absurd heq h
    · rfl

/-! ## 1. `ByteEff` & Store / Call / Loop combinators -/

structure ByteEff {F : Type} (s post : PanSemStateFiniteExact 64 F) (Rl : List Ivl) : Prop where
  code       : post.code = s.code
  memaddrs   : post.memaddrs = s.memaddrs
  shMemaddrs : post.shMemaddrs = s.shMemaddrs
  baseAddr   : post.baseAddr = s.baseAddr
  be         : post.be = s.be
  globals    : post.globals = s.globals
  eshapes    : post.eshapes = s.eshapes
  out_dom    : ∀ a : BitVec 64, post.memory a ≠ s.memory a → s.memaddrs a
  cell_frame : ∀ a : BitVec 64, post.memory a ≠ s.memory a → ∃ i ∈ Rl, CellHitsPos a.toNat i
  byte_frame : ∀ b : Nat, b < 2 ^ 64 → memB post b ≠ memB s b → ∃ i ∈ Rl, InIvl b i

theorem ByteEff.refl {F : Type} (s : PanSemStateFiniteExact 64 F) (Rl : List Ivl) :
    ByteEff s s Rl :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ h => absurd rfl h,
   fun _ h => absurd rfl h, fun _ _ h => absurd rfl h⟩

theorem ByteEff.locals_clock {F : Type} {s post : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (h : ByteEff s post Rl) (L : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    ByteEff s { post with locals := L, clock := k } Rl :=
  ⟨h.code, h.memaddrs, h.shMemaddrs, h.baseAddr, h.be, h.globals, h.eshapes,
   h.out_dom, h.cell_frame, h.byte_frame⟩

theorem ByteEff.trans {F : Type} {a b c : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (h1 : ByteEff a b Rl) (h2 : ByteEff b c Rl) : ByteEff a c Rl := by
  refine ⟨h2.code.trans h1.code, h2.memaddrs.trans h1.memaddrs,
    h2.shMemaddrs.trans h1.shMemaddrs, h2.baseAddr.trans h1.baseAddr,
    h2.be.trans h1.be, h2.globals.trans h1.globals, h2.eshapes.trans h1.eshapes, ?_, ?_, ?_⟩
  · intro x hne
    by_cases hcb : c.memory x = b.memory x
    · rw [hcb] at hne; exact h1.out_dom x hne
    · rw [← h1.memaddrs]; exact h2.out_dom x hcb
  · intro x hne
    by_cases hcb : c.memory x = b.memory x
    · rw [hcb] at hne; exact h1.cell_frame x hne
    · exact h2.cell_frame x hcb
  · intro x hx hne
    by_cases hcb : memB c x = memB b x
    · rw [hcb] at hne; exact h1.byte_frame x hx hne
    · exact h2.byte_frame x hx hcb

theorem ByteEff.mono {F : Type} {s post : PanSemStateFiniteExact 64 F} {R1 R2 : List Ivl}
    (h : ByteEff s post R1)
    (hsub : ∀ i ∈ R1, 0 < i.2 → ∃ j ∈ R2, j.1 ≤ i.1 ∧ i.1 + i.2 ≤ j.1 + j.2) :
    ByteEff s post R2 := by
  refine ⟨h.code, h.memaddrs, h.shMemaddrs, h.baseAddr, h.be, h.globals, h.eshapes, h.out_dom, ?_, ?_⟩
  · intro a hne
    obtain ⟨i, hi, hipos, hc1, hc2⟩ := h.cell_frame a hne
    obtain ⟨j, hj, h1, h2⟩ := hsub i hi hipos
    exact ⟨j, hj, by omega, by omega, by omega⟩
  · intro b hb hne
    obtain ⟨i, hi, hb1, hb2⟩ := h.byte_frame b hb hne
    obtain ⟨j, hj, h1, h2⟩ := hsub i hi (by omega)
    exact ⟨j, hj, by omega, by omega⟩

theorem byteEff_store_one {F : Type} {s : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (hG : GuestInv s) (dstExp valExp : ExpHOL 64)
    (hval_one : ∀ v, @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) valExp =
      some v → ∃ w : BitVec 64, v = .val (.word w))
    (hin : ∀ x : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
        some (.val (.word x)) →
      s.memaddrs x →
      ∃ i ∈ Rl, i.1 ≤ x.toNat ∧ x.toNat + 8 ≤ i.1 + i.2) :
    ByteEff s (evaluateHOLFiniteState s (.store dstExp valExp)).2 Rl ∧
    ((evaluateHOLFiniteState s (.store dstExp valExp)).1 = none →
      ∃ x : BitVec 64,
        @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
          some (.val (.word x)) ∧
        sourceBase ≤ x.toNat ∧ x.toNat + 8 ≤ heapEnd ∧ x.toNat % 8 = 0) := by
  rw [evaluateHOLFiniteState_store]
  split
  · rename_i x hx
    split
    · rename_i val hval
      obtain ⟨w, rfl⟩ := hval_one val hval
      split
      · rename_i mem' hmem
        simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL] at hmem
        by_cases hdom : s.memaddrs x
        · simp only [hdom, ↓reduceIte, Option.some.injEq] at hmem
          subst hmem
          have hdom_ord : x.toNat % 8 = 0 ∧ sourceBase ≤ x.toNat ∧ x.toNat < heapEnd := by
            rw [hG.memaddrs, ordinaryDomain_iff] at hdom; exact hdom
          have hhe8 : heapEnd % 8 = 0 := by decide
          obtain ⟨ivl, hivl, hi1, hi2⟩ := hin x hx hdom
          refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩,
            fun _ => ⟨x, hx, hdom_ord.2.1, by omega, hdom_ord.1⟩⟩
          · intro a hne; by_cases hax : a = x
            · subst hax; exact hdom
            · simp [hax] at hne
          · intro a hne; by_cases hax : a = x
            · subst hax; exact ⟨ivl, hivl, by omega, by omega, by omega⟩
            · simp [hax] at hne
          · intro b hb hne
            by_cases hal : panByteAlignHOL (BitVec.ofNat 64 b) = x
            · have hc_nat := panByteAlign_toNat64 (BitVec.ofNat 64 b)
              rw [hal, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb] at hc_nat
              exact ⟨ivl, hivl, by omega, by omega⟩
            · unfold memB at hne; simp [hal] at hne
        · simp [hdom] at hmem
      · exact ⟨ByteEff.refl s Rl, by simp⟩
    · exact ⟨ByteEff.refl s Rl, by simp⟩
  · exact ⟨ByteEff.refl s Rl, by simp⟩

theorem byteEff_storeByte {F : Type} {s : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (hG : GuestInv s) (dstExp valExp : ExpHOL 64)
    (hin : ∀ x : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
        some (.val (.word x)) →
      s.memaddrs (panByteAlignHOL x) →
      ∃ i ∈ Rl, InIvl x.toNat i) :
    ByteEff s (evaluateHOLFiniteState s (.storeByte dstExp valExp)).2 Rl ∧
    ((evaluateHOLFiniteState s (.storeByte dstExp valExp)).1 = none →
      ∃ x : BitVec 64,
        @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
          some (.val (.word x)) ∧
        sourceBase ≤ x.toNat ∧ x.toNat + 1 ≤ heapEnd) := by
  rw [evaluateHOLFiniteState_storeByte]
  split
  · rename_i x hx
    split
    · rename_i vw hvw
      split
      · rename_i mem' hmem
        have hdom : s.memaddrs (panByteAlignHOL x) := by
          by_contra hc
          unfold panMemStoreByteWord8HOL at hmem
          cases s.memory (panByteAlignHOL x) with
          | word _ => simp [hc] at hmem
        have hdom_ord : (panByteAlignHOL x).toNat % 8 = 0 ∧
            sourceBase ≤ (panByteAlignHOL x).toNat ∧ (panByteAlignHOL x).toNat < heapEnd := by
          rw [hG.memaddrs, ordinaryDomain_iff] at hdom; exact hdom
        have hhe8 : heapEnd % 8 = 0 := by decide
        have hal_nat := panByteAlign_toNat64 x
        obtain ⟨ivl, hivl, hin_x⟩ := hin x hx hdom
        have hmem_cell : ∀ a : BitVec 64, a ≠ panByteAlignHOL x → mem' a = s.memory a := by
          intro a hne
          have hm' := hmem
          unfold panMemStoreByteWord8HOL at hm'
          cases s.memory (panByteAlignHOL x) with
          | word cell =>
            dsimp only at hm'; rw [if_pos hdom] at hm'
            injection hm' with hm_eq; subst hm_eq; simp [hne]
        refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩,
          fun _ => ⟨x, hx, by omega, by omega⟩⟩
        · intro a hne; by_cases hax : a = panByteAlignHOL x
          · subst hax; exact hdom
          · exact False.elim (hne (hmem_cell a hax))
        · intro a hne; by_cases hax : a = panByteAlignHOL x
          · subst hax
            obtain ⟨hx1, hx2⟩ := hin_x
            exact ⟨ivl, hivl, by omega, by rw [hal_nat]; omega, by rw [hal_nat]; omega⟩
          · exact False.elim (hne (hmem_cell a hax))
        · intro b hb hne
          by_cases hbx : BitVec.ofNat 64 b = x
          · have hb_eq : b = x.toNat := by
              have := congrArg BitVec.toNat hbx
              rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb] at this
            rw [hb_eq]; exact ⟨ivl, hivl, hin_x⟩
          · have hob := @Wave8Contracts.M08.panMemStoreByte_other_byte' s.memory s.memaddrs
              (fun addr => Classical.propDecidable (s.memaddrs addr)) s.be x
              (BitVec.ofNat 8 vw.toNat) mem' hmem (BitVec.ofNat 64 b) hbx
            exact False.elim (hne hob)
      · exact ⟨ByteEff.refl s Rl, by simp⟩
    · exact ⟨ByteEff.refl s Rl, by simp⟩
  · exact ⟨ByteEff.refl s Rl, by simp⟩

/-! ## 3. `memzero`, `memcpy`, `st_le32`, `st_le64`, `st_be32`, `st_be64`, `addr_from_words` -/

theorem not_resumes_error : ¬ Resumes (some (.error : PanSemResultExact 64)) := by
  rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> cases h

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
        · have dec_lt : (decClockHOLFinite s).clock < s.clock := by
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
            | «break» => rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
            | returned _ => exact ih1
            | exception _ _ => exact ih1
            | timeOut => rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
            | error => exact not_resumes_error
            | finalFfi _ => rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
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

private def noBreakOrCont : ProgHOL 64 → Bool
  | .seq a b => noBreakOrCont a && noBreakOrCont b
  | .ite _ a b => noBreakOrCont a && noBreakOrCont b
  | .assign .local _ _ | .store _ _ | .storeByte _ _ | .skip => true
  | _ => false

private theorem evaluate_noBreakOrCont {F : Type} (p : ProgHOL 64) (hp : noBreakOrCont p = true)
    (s : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState s p).1 ≠ some .break ∧
    (evaluateHOLFiniteState s p).1 ≠ some .continue := by
  cases shape : p with
  | skip => simp [evaluateHOLFiniteState_skip]
  | assign k _ _ =>
    cases k with
    | global => simp [shape, noBreakOrCont] at hp
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
    have hab : noBreakOrCont a = true ∧ noBreakOrCont b = true := by
      simpa [shape, noBreakOrCont, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_seq_line780]
    have ha := evaluate_noBreakOrCont a hab.1 s
    rcases hr : evaluateHOLFiniteState s a with ⟨r, m⟩
    rw [hr] at ha
    cases r with
    | none => exact evaluate_noBreakOrCont b hab.2 m
    | some _ => exact ha
  | ite _ a b =>
    have hab : noBreakOrCont a = true ∧ noBreakOrCont b = true := by
      simpa [shape, noBreakOrCont, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_noBreakOrCont b hab.2 s
      · exact evaluate_noBreakOrCont a hab.1 s
    · simp
  | _ => simp [shape, noBreakOrCont] at hp

private def CopyInv {F : Type} (s0 : PanSemStateFiniteExact 64 F) (dst0 n0 : BitVec 64)
    (s : PanSemStateFiniteExact 64 F) : Prop :=
  s.code = originalRuntimeCode ∧ GuestInv s ∧
  ByteEff s0 s [(dst0.toNat, n0.toNat)] ∧
  s.locals.lookup (ofString "dst") = some (.val (.word dst0)) ∧
  s.locals.lookup (ofString "n") = some (.val (.word n0)) ∧
  ∃ iw : BitVec 64,
    s.locals.lookup (ofString "i") = some (.val (.word iw)) ∧
    iw.toNat ≤ n0.toNat ∧
    (0 < iw.toNat → sourceBase ≤ dst0.toNat ∧ dst0.toNat + iw.toNat ≤ heapEnd)

theorem eval_add2_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
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

theorem eval_load_one_word {F : Type} (s : PanSemStateFiniteExact 64 F) (e : ExpHOL 64) :
    ∀ v, @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.load .one e) = some v → ∃ w : BitVec 64, v = .val (.word w) := by
  intro v hv
  simp only [evalHOLExact] at hv
  rcases he : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e with _ | ev
  · simp [he] at hv
  · rcases ev with ⟨⟨addr⟩⟩ | _ | _
    · simp only [he, memLoadHOLExact] at hv
      split at hv
      · cases hm : s.memory addr with
        | word w =>
          rw [hm] at hv
          split at hv
          · injection hv with h; exact ⟨w, h.symm⟩
          · cases hv
      · cases hv
    · simp [he] at hv
    · simp [he] at hv

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
  rw [sourceBase_val, heapEnd_val] at hprev hcur ⊢
  have hdlt := dst0.isLt; have hilt := iw.isLt; have hnlt := n0.isLt
  rw [BitVec.lt_def] at hcond
  by_cases hiz : iw.toNat = 0
  · have hi0 : iw = 0 := BitVec.eq_of_toNat_eq hiz
    subst hi0
    have hd0 : dst0 + 0 = dst0 := BitVec.add_zero _
    have hk0 : (0 : BitVec 64) + k = k := BitVec.zero_add _
    rw [hd0] at hcur ⊢; rw [hk0] at hcond ⊢
    have hz0 : (0 : BitVec 64).toNat = 0 := rfl
    rw [hz0]
    exact ⟨by omega, by omega, by omega, hcur.1, hcur.2⟩
  · obtain ⟨hdlo, hdhi⟩ := hprev (by omega)
    have hadd_di : (dst0 + iw).toNat = dst0.toNat + iw.toNat := BitVec.toNat_add_of_lt (by omega)
    rw [hadd_di] at hcur ⊢
    have hik_lt : iw.toNat + k.toNat < 2 ^ 64 := by omega
    have hadd_ik : (iw + k).toNat = iw.toNat + k.toNat := BitVec.toNat_add_of_lt hik_lt
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
    Compiler.Encoders.Asm.wordCmpHOL] at he
  intro hlt
  have hnotle : ¬ (iw + k ≤ n0) := by rw [BitVec.lt_def] at hlt; rw [BitVec.le_def]; omega
  simp [hnotle] at he; exact hw he.symm

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
  by_contra hge; simp [hge] at he; exact hw he.symm

private theorem while_copyInv {F : Type} {s0 : PanSemStateFiniteExact 64 F} {dst0 n0 : BitVec 64}
    (cond : ExpHOL 64) (body : ProgHOL 64)
    (hnbc : noBreakOrCont body = true)
    (hbody : ∀ (s : PanSemStateFiniteExact 64 F) (w : BitVec 64),
      CopyInv s0 dst0 n0 s →
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) cond =
        some (.val (.word w)) → w ≠ 0 →
      (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none →
      CopyInv s0 dst0 n0 (evaluateHOLFiniteState (decClockHOLFinite s) body).2)
    (k : Nat) (s post : PanSemStateFiniteExact 64 F) (hk : s.clock ≤ k)
    (hinv : CopyInv s0 dst0 n0 s)
    (hrun : evaluateHOLFiniteState s (.while cond body) = (none, post)) :
    CopyInv s0 dst0 n0 post ∧
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
      · rename_i hnotnz
        have hcw0 : cw = 0 := Classical.not_not.1 hnotnz
        subst hcw0
        simp at hrun; subst hrun; exact ⟨hinv, hcond⟩
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
          have nbc := evaluate_noBreakOrCont body hnbc (decClockHOLFinite s)
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨r1, mid⟩
          rw [hbr] at hrun rem nbc
          cases r1 with
          | none =>
            have hmid : CopyInv s0 dst0 n0 mid := by
              have hb := hbody s cw hinv hcond hnz (by rw [hbr])
              rw [hbr] at hb; exact hb
            exact ih mid (by change mid.clock ≤ s.clock - 1 at rem; omega) hmid hrun
          | some r1 =>
            cases r1 with
            | «continue» => exact absurd rfl nbc.2
            | «break» => exact absurd rfl nbc.1
            | _ => simp at hrun
      · rename_i hnotnz
        have hcw0 : cw = 0 := Classical.not_not.1 hnotnz
        subst hcw0
        simp at hrun; subst hrun; exact ⟨hinv, hcond⟩
    · simp at hrun

private theorem assign_i_copyInv {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    {dst0 n0 iw k : BitVec 64}
    (hc : s.code = originalRuntimeCode) (hG : GuestInv s)
    (heff : ByteEff s0 s [(dst0.toNat, n0.toNat)])
    (hd : s.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n0)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iw)))
    (hle : (iw + k).toNat ≤ n0.toNat)
    (hdlo : sourceBase ≤ dst0.toNat) (hdhi : dst0.toNat + (iw + k).toNat ≤ heapEnd) :
    CopyInv s0 dst0 n0
      (evaluateHOLFiniteState s (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const k]))).2 := by
  have hrun : evaluateHOLFiniteState s
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const k])) =
      (none, setVarHOLFinite (ofString "i") (.val (.word (iw + k))) s) := by
    simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hi, wordOpHOL, wordOp,
      valueIsWord, valueWord, lookupKvarHOLExact, isValidValueHOLExact, setKvarHOLFinite,
      shapeOfHOLExact, shapeEqHOL]
  rw [hrun]; dsimp only
  refine ⟨hc, guestInv_setVar _ _ s hG, heff.locals_clock _ s.clock, ?_, ?_, iw + k, ?_, hle, fun _ => ⟨hdlo, hdhi⟩⟩
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hd, show ofString "i" ≠ ofString "dst" by decide]
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn, show ofString "i" ≠ ofString "n" by decide]
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]

private theorem seq_store_none {F : Type} (s : PanSemStateFiniteExact 64 F)
    (st b : ProgHOL 64)
    (hloc : (evaluateHOLFiniteState s st).2.locals = s.locals)
    (h : (evaluateHOLFiniteState s (.seq st b)).1 = none) :
    (evaluateHOLFiniteState s st).1 = none ∧
    (evaluateHOLFiniteState (evaluateHOLFiniteState s st).2 b).1 = none ∧
    (evaluateHOLFiniteState s (.seq st b)).2 =
      (evaluateHOLFiniteState (evaluateHOLFiniteState s st).2 b).2 ∧
    (evaluateHOLFiniteState s st).2.locals = s.locals := by
  rw [evaluateHOLFiniteState_seq_line780] at h ⊢
  rcases hr : evaluateHOLFiniteState s st with ⟨r, m⟩
  rw [hr] at h hloc
  cases r with
  | none => exact ⟨rfl, h, rfl, hloc⟩
  | some _ => simp at h

theorem store_one_domain {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hG : GuestInv s) (dstExp valExp : ExpHOL 64)
    (hval_one : ∀ v, @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) valExp =
      some v → ∃ w : BitVec 64, v = .val (.word w))
    (hnone : (evaluateHOLFiniteState s (.store dstExp valExp)).1 = none) :
    ∃ x : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
        some (.val (.word x)) ∧
      sourceBase ≤ x.toNat ∧ x.toNat + 8 ≤ heapEnd ∧ x.toNat % 8 = 0 := by
  rw [evaluateHOLFiniteState_store] at hnone
  split at hnone
  · rename_i x hx
    split at hnone
    · rename_i val hval
      obtain ⟨w, rfl⟩ := hval_one val hval
      split at hnone
      · rename_i mem' hmem
        simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL] at hmem
        by_cases hdom : s.memaddrs x
        · have hdom_ord : x.toNat % 8 = 0 ∧ sourceBase ≤ x.toNat ∧ x.toNat < heapEnd := by
            rw [hG.memaddrs, ordinaryDomain_iff] at hdom; exact hdom
          have hhe8 : heapEnd % 8 = 0 := by decide
          exact ⟨x, hx, hdom_ord.2.1, by omega, hdom_ord.1⟩
        · simp [hdom] at hmem
      · simp at hnone
    · simp at hnone
  · simp at hnone

theorem storeByte_domain {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hG : GuestInv s) (dstExp valExp : ExpHOL 64)
    (hnone : (evaluateHOLFiniteState s (.storeByte dstExp valExp)).1 = none) :
    ∃ x : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
        some (.val (.word x)) ∧
      sourceBase ≤ x.toNat ∧ x.toNat + 1 ≤ heapEnd := by
  rw [evaluateHOLFiniteState_storeByte] at hnone
  split at hnone
  · rename_i x hx
    split at hnone
    · split at hnone
      · rename_i mem' hmem
        have hdom : s.memaddrs (panByteAlignHOL x) := by
          by_contra hc
          unfold panMemStoreByteWord8HOL at hmem
          cases s.memory (panByteAlignHOL x) with
          | word _ => simp [hc] at hmem
        have hdom_ord : (panByteAlignHOL x).toNat % 8 = 0 ∧
            sourceBase ≤ (panByteAlignHOL x).toNat ∧ (panByteAlignHOL x).toNat < heapEnd := by
          rw [hG.memaddrs, ordinaryDomain_iff] at hdom; exact hdom
        have hhe8 : heapEnd % 8 = 0 := by decide
        have hal_nat := panByteAlign_toNat64 x
        exact ⟨x, hx, by omega, by omega⟩
      · simp at hnone
    · simp at hnone
  · simp at hnone

theorem byteEff_store_at {F : Type} {s : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (hG : GuestInv s) (dstExp valExp : ExpHOL 64) (base : BitVec 64) (off len : Nat)
    (hbound : base.toNat + len ≤ heapEnd)
    (hin_Rl : 0 < len → ∃ i ∈ Rl, i.1 ≤ base.toNat ∧ base.toNat + len ≤ i.1 + i.2)
    (hval : ∀ v, @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) valExp =
      some v → ∃ w : BitVec 64, v = .val (.word w))
    (hoff : off + 8 ≤ len)
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
      some (.val (.word (base + BitVec.ofNat 64 off)))) :
    ByteEff s (evaluateHOLFiniteState s (.store dstExp valExp)).2 Rl := by
  have h264 : heapEnd < 2 ^ 64 := by rw [heapEnd_val]; decide
  refine (byteEff_store_one hG dstExp valExp hval (fun x hx _ => ?_)).1
  rw [hdst] at hx; injection hx with hx'; injection hx' with hx''; injection hx'' with hx'''; subst hx'''
  obtain ⟨ivl, hivl, h1, h2⟩ := hin_Rl (by omega)
  have hadd : (base + BitVec.ofNat 64 off).toNat = base.toNat + off := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  exact ⟨ivl, hivl, by omega, by omega⟩

theorem byteEff_storeByte_at {F : Type} {s : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (hG : GuestInv s) (dstExp valExp : ExpHOL 64) (base : BitVec 64) (off len : Nat)
    (hbound : base.toNat + len ≤ heapEnd)
    (hin_Rl : 0 < len → ∃ i ∈ Rl, i.1 ≤ base.toNat ∧ base.toNat + len ≤ i.1 + i.2)
    (hoff : off < len)
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
      some (.val (.word (base + BitVec.ofNat 64 off)))) :
    ByteEff s (evaluateHOLFiniteState s (.storeByte dstExp valExp)).2 Rl := by
  have h264 : heapEnd < 2 ^ 64 := by rw [heapEnd_val]; decide
  refine (byteEff_storeByte hG dstExp valExp (fun x hx _ => ?_)).1
  rw [hdst] at hx; injection hx with hx'; injection hx' with hx''; injection hx'' with hx'''; subst hx'''
  obtain ⟨ivl, hivl, h1, h2⟩ := hin_Rl (by omega)
  have hadd : (base + BitVec.ofNat 64 off).toNat = base.toNat + off := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  exact ⟨ivl, hivl, by omega, by omega⟩

private theorem step_copy_loop32 {F : Type} {s0 : PanSemStateFiniteExact 64 F} {dst0 n0 : BitVec 64}
    (v0 v8 v16 v24 : ExpHOL 64)
    (hv0 : ∀ (t : PanSemStateFiniteExact 64 F) v, @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) v0 = some v → ∃ w, v = .val (.word w))
    (hv8 : ∀ (t : PanSemStateFiniteExact 64 F) v, @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) v8 = some v → ∃ w, v = .val (.word w))
    (hv16 : ∀ (t : PanSemStateFiniteExact 64 F) v, @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) v16 = some v → ∃ w, v = .val (.word w))
    (hv24 : ∀ (t : PanSemStateFiniteExact 64 F) v, @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) v24 = some v → ∃ w, v = .val (.word w))
    (s : PanSemStateFiniteExact 64 F) (w : BitVec 64)
    (hinv : CopyInv s0 dst0 n0 s)
    (hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .notLower (.var .local (ofString "n"))
        (.op .add [.var .local (ofString "i"), .const 32])) = some (.val (.word w)))
    (hw : w ≠ 0) :
    let body := (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) v0)
        (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 8]) v8)
          (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 16]) v16)
            (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 24]) v24)
              (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 32]))))))
    (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none →
      CopyInv s0 dst0 n0 (evaluateHOLFiniteState (decClockHOLFinite s) body).2 := by
  intro body hnone
  have h264 : heapEnd < 2 ^ 64 := by rw [heapEnd_val]; decide
  obtain ⟨hc, hG, heff, hdst, hn, iw, hi, hle, hdom⟩ := hinv
  let sd := decClockHOLFinite s
  have hGd : GuestInv sd := guestInv_congr (s := s) rfl rfl rfl rfl hG
  have heffd : ByteEff s0 sd [(dst0.toNat, n0.toNat)] := heff.locals_clock s.locals (s.clock - 1)
  have hnl := eval_notLower_true s n0 iw 32 w hn hi hcond hw
  obtain ⟨hs0, hr1, heq1, hl1⟩ := seq_store_none sd _ _ (evaluate_store_control_frame sd _ _).2.1 hnone
  let s1 := (evaluateHOLFiniteState sd (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) v0)).2
  have hG1 : GuestInv s1 := guestInv_evaluate sd _ hGd
  obtain ⟨hs8, hr2, heq2, hl2⟩ := seq_store_none s1 _ _ (evaluate_store_control_frame s1 _ _).2.1 hr1
  let s2 := (evaluateHOLFiniteState s1 (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 8]) v8)).2
  have hG2 : GuestInv s2 := guestInv_evaluate s1 _ hG1
  obtain ⟨hs16, hr3, heq3, hl3⟩ := seq_store_none s2 _ _ (evaluate_store_control_frame s2 _ _).2.1 hr2
  let s3 := (evaluateHOLFiniteState s2 (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 16]) v16)).2
  have hG3 : GuestInv s3 := guestInv_evaluate s2 _ hG2
  obtain ⟨hs24, _, heq4, hl4⟩ := seq_store_none s3 _ _ (evaluate_store_control_frame s3 _ _).2.1 hr3
  let s4 := (evaluateHOLFiniteState s3 (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 24]) v24)).2
  have hG4 : GuestInv s4 := guestInv_evaluate s3 _ hG3
  have hd_s1 : s1.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by rw [hl1]; exact hdst
  have hi_s1 : s1.locals.lookup (ofString "i") = some (.val (.word iw)) := by rw [hl1]; exact hi
  have hd_s2 : s2.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by rw [hl2]; exact hd_s1
  have hi_s2 : s2.locals.lookup (ofString "i") = some (.val (.word iw)) := by rw [hl2]; exact hi_s1
  have hd_s3 : s3.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by rw [hl3]; exact hd_s2
  have hi_s3 : s3.locals.lookup (ofString "i") = some (.val (.word iw)) := by rw [hl3]; exact hi_s2
  have hd_s4 : s4.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by rw [hl4]; exact hd_s3
  have hi_s4 : s4.locals.lookup (ofString "i") = some (.val (.word iw)) := by rw [hl4]; exact hi_s3
  have hn_s4 : s4.locals.lookup (ofString "n") = some (.val (.word n0)) := by rw [hl4, hl3, hl2, hl1]; exact hn
  obtain ⟨x0, hx0, hd0_lo, hd0_hi, _⟩ := store_one_domain hGd _ v0 (hv0 sd) hs0
  obtain ⟨x8, hx8, _, hd8_hi, _⟩ := store_one_domain hG1 _ v8 (hv8 s1) hs8
  obtain ⟨x16, hx16, _, hd16_hi, _⟩ := store_one_domain hG2 _ v16 (hv16 s2) hs16
  obtain ⟨x24, hx24, _, hd24_hi, _⟩ := store_one_domain hG3 _ v24 (hv24 s3) hs24
  have ex0 := eval_add2_locals sd _ _ dst0 iw hdst hi
  have ex8 := eval_add3_locals s1 _ _ dst0 iw 8 hd_s1 hi_s1
  have ex16 := eval_add3_locals s2 _ _ dst0 iw 16 hd_s2 hi_s2
  have ex24 := eval_add3_locals s3 _ _ dst0 iw 24 hd_s3 hi_s3
  rw [ex0] at hx0; injection hx0 with hx0; injection hx0 with hx0; injection hx0 with hx0; subst hx0
  rw [ex8] at hx8; injection hx8 with hx8; injection hx8 with hx8; injection hx8 with hx8; subst hx8
  rw [ex16] at hx16; injection hx16 with hx16; injection hx16 with hx16; injection hx16 with hx16; subst hx16
  rw [ex24] at hx24; injection hx24 with hx24; injection hx24 with hx24; injection hx24 with hx24; subst hx24
  have a8 : (dst0 + iw + 8).toNat = (dst0 + iw).toNat + 8 :=
    BitVec.toNat_add_of_lt (by change (dst0 + iw).toNat + 8 < 2 ^ 64; omega)
  have a16 : (dst0 + iw + 16).toNat = (dst0 + iw).toNat + 16 := by
    rw [a8] at hd8_hi; exact BitVec.toNat_add_of_lt (by change (dst0 + iw).toNat + 16 < 2 ^ 64; omega)
  have a24 : (dst0 + iw + 24).toNat = (dst0 + iw).toNat + 24 := by
    rw [a16] at hd16_hi; exact BitVec.toNat_add_of_lt (by change (dst0 + iw).toNat + 24 < 2 ^ 64; omega)
  have hcur32 : sourceBase ≤ (dst0 + iw).toNat ∧ (dst0 + iw).toNat + (32 : BitVec 64).toNat ≤ heapEnd := by
    rw [a24] at hd24_hi; exact ⟨hd0_lo, by change (dst0 + iw).toNat + 32 ≤ heapEnd; omega⟩
  obtain ⟨hdi_eq, hik_eq, hle_ik, hdlo, hdhi⟩ :=
    step_domain_nowrap dst0 iw n0 32 hle hdom hcur32 (by decide) (by decide) hnl
  have hk32_val : (32 : BitVec 64).toNat = 32 := rfl
  have hin32 : 0 < 32 → ∃ i ∈ [(dst0.toNat, n0.toNat)],
      i.1 ≤ (dst0 + iw).toNat ∧ (dst0 + iw).toNat + 32 ≤ i.1 + i.2 :=
    fun _ => ⟨(dst0.toNat, n0.toNat), List.mem_singleton.2 rfl, by omega, by omega⟩
  have eff1 := byteEff_store_at hGd _ v0 (dst0 + iw) 0 32 (by omega) hin32 (hv0 sd) (by omega)
    (by simpa [BitVec.add_zero] using ex0)
  have eff2 := byteEff_store_at hG1 _ v8 (dst0 + iw) 8 32 (by omega) hin32 (hv8 s1) (by omega) ex8
  have eff3 := byteEff_store_at hG2 _ v16 (dst0 + iw) 16 32 (by omega) hin32 (hv16 s2) (by omega) ex16
  have eff4 := byteEff_store_at hG3 _ v24 (dst0 + iw) 24 32 (by omega) hin32 (hv24 s3) (by omega) ex24
  have hmeta4 : s4.code = originalRuntimeCode := hG4.code
  change CopyInv s0 dst0 n0 (evaluateHOLFiniteState sd body).2
  rw [heq1, heq2, heq3, heq4]
  exact assign_i_copyInv hmeta4 hG4 (heffd.trans (eff1.trans (eff2.trans (eff3.trans eff4))))
    hd_s4 hn_s4 hi_s4 hle_ik hdlo hdhi

private theorem step_copy_loop8w {F : Type} {s0 : PanSemStateFiniteExact 64 F} {dst0 n0 : BitVec 64}
    (v0 : ExpHOL 64)
    (hv0 : ∀ (t : PanSemStateFiniteExact 64 F) v, @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) v0 = some v → ∃ w, v = .val (.word w))
    (s : PanSemStateFiniteExact 64 F) (w : BitVec 64)
    (hinv : CopyInv s0 dst0 n0 s)
    (hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .notLower (.var .local (ofString "n"))
        (.op .add [.var .local (ofString "i"), .const 8])) = some (.val (.word w)))
    (hw : w ≠ 0) :
    let body := (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) v0)
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 8])))
    (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none →
      CopyInv s0 dst0 n0 (evaluateHOLFiniteState (decClockHOLFinite s) body).2 := by
  intro body hnone
  obtain ⟨hc, hG, heff, hdst, hn, iw, hi, hle, hdom⟩ := hinv
  let sd := decClockHOLFinite s
  have hGd : GuestInv sd := guestInv_congr (s := s) rfl rfl rfl rfl hG
  have heffd : ByteEff s0 sd [(dst0.toNat, n0.toNat)] := heff.locals_clock s.locals (s.clock - 1)
  have hnl := eval_notLower_true s n0 iw 8 w hn hi hcond hw
  obtain ⟨hs0, _, heq1, hl1⟩ := seq_store_none sd _ _ (evaluate_store_control_frame sd _ _).2.1 hnone
  let s1 := (evaluateHOLFiniteState sd (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) v0)).2
  have hG1 : GuestInv s1 := guestInv_evaluate sd _ hGd
  obtain ⟨x0, hx0, hd0_lo, hd0_hi, _⟩ := store_one_domain hGd _ v0 (hv0 sd) hs0
  have ex0 := eval_add2_locals sd _ _ dst0 iw hdst hi
  rw [ex0] at hx0; injection hx0 with hx0; injection hx0 with hx0; injection hx0 with hx0; subst hx0
  obtain ⟨hdi_eq, hik_eq, hle_ik, hdlo, hdhi⟩ :=
    step_domain_nowrap dst0 iw n0 8 hle hdom ⟨hd0_lo, hd0_hi⟩ (by decide) (by decide) hnl
  have hk8_val : (8 : BitVec 64).toNat = 8 := rfl
  have eff1 := byteEff_store_at hGd _ v0 (dst0 + iw) 0 8 hd0_hi
    (fun _ => ⟨(dst0.toNat, n0.toNat), List.mem_singleton.2 rfl, by omega, by omega⟩)
    (hv0 sd) (by omega) (by simpa [BitVec.add_zero] using ex0)
  change CopyInv s0 dst0 n0 (evaluateHOLFiniteState sd body).2
  rw [heq1]
  exact assign_i_copyInv hG1.code hG1 (heffd.trans eff1)
    (by rw [hl1]; exact hdst) (by rw [hl1]; exact hn) (by rw [hl1]; exact hi) hle_ik hdlo hdhi

private theorem step_copy_loop8b {F : Type} {s0 : PanSemStateFiniteExact 64 F} {dst0 n0 : BitVec 64}
    (b0 b1 b2 b3 b4 b5 b6 b7 : ExpHOL 64)
    (s : PanSemStateFiniteExact 64 F) (w : BitVec 64)
    (hinv : CopyInv s0 dst0 n0 s)
    (hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .notLower (.var .local (ofString "n"))
        (.op .add [.var .local (ofString "i"), .const 8])) = some (.val (.word w)))
    (hw : w ≠ 0) :
    let body :=
      (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) b0)
      (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 1]) b1)
      (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 2]) b2)
      (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 3]) b3)
      (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 4]) b4)
      (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 5]) b5)
      (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 6]) b6)
      (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 7]) b7)
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 8]))))))))))
    (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none →
      CopyInv s0 dst0 n0 (evaluateHOLFiniteState (decClockHOLFinite s) body).2 := by
  intro body hnone
  have h264 : heapEnd < 2 ^ 64 := by rw [heapEnd_val]; decide
  obtain ⟨hc, hG, heff, hdst, hn, iw, hi, hle, hdom⟩ := hinv
  let sd := decClockHOLFinite s
  have hGd : GuestInv sd := guestInv_congr (s := s) rfl rfl rfl rfl hG
  have heffd : ByteEff s0 sd [(dst0.toNat, n0.toNat)] := heff.locals_clock s.locals (s.clock - 1)
  have hnl := eval_notLower_true s n0 iw 8 w hn hi hcond hw
  obtain ⟨hs0, hr1, heq1, hl1⟩ := seq_store_none sd _ _ (evaluate_storeByte_control_frame sd _ _).2.2.1 hnone
  let s1 := (evaluateHOLFiniteState sd (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) b0)).2
  have hG1 : GuestInv s1 := guestInv_evaluate sd _ hGd
  obtain ⟨hs1, hr2, heq2, hl2⟩ := seq_store_none s1 _ _ (evaluate_storeByte_control_frame s1 _ _).2.2.1 hr1
  let s2 := (evaluateHOLFiniteState s1 (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 1]) b1)).2
  have hG2 : GuestInv s2 := guestInv_evaluate s1 _ hG1
  obtain ⟨hs2, hr3, heq3, hl3⟩ := seq_store_none s2 _ _ (evaluate_storeByte_control_frame s2 _ _).2.2.1 hr2
  let s3 := (evaluateHOLFiniteState s2 (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 2]) b2)).2
  have hG3 : GuestInv s3 := guestInv_evaluate s2 _ hG2
  obtain ⟨hs3, hr4, heq4, hl4⟩ := seq_store_none s3 _ _ (evaluate_storeByte_control_frame s3 _ _).2.2.1 hr3
  let s4 := (evaluateHOLFiniteState s3 (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 3]) b3)).2
  have hG4 : GuestInv s4 := guestInv_evaluate s3 _ hG3
  obtain ⟨hs4, hr5, heq5, hl5⟩ := seq_store_none s4 _ _ (evaluate_storeByte_control_frame s4 _ _).2.2.1 hr4
  let s5 := (evaluateHOLFiniteState s4 (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 4]) b4)).2
  have hG5 : GuestInv s5 := guestInv_evaluate s4 _ hG4
  obtain ⟨hs5, hr6, heq6, hl6⟩ := seq_store_none s5 _ _ (evaluate_storeByte_control_frame s5 _ _).2.2.1 hr5
  let s6 := (evaluateHOLFiniteState s5 (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 5]) b5)).2
  have hG6 : GuestInv s6 := guestInv_evaluate s5 _ hG5
  obtain ⟨hs6, hr7, heq7, hl7⟩ := seq_store_none s6 _ _ (evaluate_storeByte_control_frame s6 _ _).2.2.1 hr6
  let s7 := (evaluateHOLFiniteState s6 (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 6]) b6)).2
  have hG7 : GuestInv s7 := guestInv_evaluate s6 _ hG6
  obtain ⟨hs7, _, heq8, hl8⟩ := seq_store_none s7 _ _ (evaluate_storeByte_control_frame s7 _ _).2.2.1 hr7
  let s8 := (evaluateHOLFiniteState s7 (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 7]) b7)).2
  have hG8 : GuestInv s8 := guestInv_evaluate s7 _ hG7
  have hd1 : s1.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by rw [hl1]; exact hdst
  have hi1 : s1.locals.lookup (ofString "i") = some (.val (.word iw)) := by rw [hl1]; exact hi
  have hd2 : s2.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by rw [hl2]; exact hd1
  have hi2 : s2.locals.lookup (ofString "i") = some (.val (.word iw)) := by rw [hl2]; exact hi1
  have hd3 : s3.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by rw [hl3]; exact hd2
  have hi3 : s3.locals.lookup (ofString "i") = some (.val (.word iw)) := by rw [hl3]; exact hi2
  have hd4 : s4.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by rw [hl4]; exact hd3
  have hi4 : s4.locals.lookup (ofString "i") = some (.val (.word iw)) := by rw [hl4]; exact hi3
  have hd5 : s5.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by rw [hl5]; exact hd4
  have hi5 : s5.locals.lookup (ofString "i") = some (.val (.word iw)) := by rw [hl5]; exact hi4
  have hd6 : s6.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by rw [hl6]; exact hd5
  have hi6 : s6.locals.lookup (ofString "i") = some (.val (.word iw)) := by rw [hl6]; exact hi5
  have hd7 : s7.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by rw [hl7]; exact hd6
  have hi7 : s7.locals.lookup (ofString "i") = some (.val (.word iw)) := by rw [hl7]; exact hi6
  have hd8 : s8.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by rw [hl8]; exact hd7
  have hi8 : s8.locals.lookup (ofString "i") = some (.val (.word iw)) := by rw [hl8]; exact hi7
  have hn8 : s8.locals.lookup (ofString "n") = some (.val (.word n0)) := by
    rw [hl8, hl7, hl6, hl5, hl4, hl3, hl2, hl1]; exact hn
  have ex0 := eval_add2_locals sd _ _ dst0 iw hdst hi
  have ex1 := eval_add3_locals s1 _ _ dst0 iw 1 hd1 hi1
  have ex2 := eval_add3_locals s2 _ _ dst0 iw 2 hd2 hi2
  have ex3 := eval_add3_locals s3 _ _ dst0 iw 3 hd3 hi3
  have ex4 := eval_add3_locals s4 _ _ dst0 iw 4 hd4 hi4
  have ex5 := eval_add3_locals s5 _ _ dst0 iw 5 hd5 hi5
  have ex6 := eval_add3_locals s6 _ _ dst0 iw 6 hd6 hi6
  have ex7 := eval_add3_locals s7 _ _ dst0 iw 7 hd7 hi7
  obtain ⟨x0, hx0, hd0_lo, hd0_hi⟩ := storeByte_domain hGd _ b0 hs0
  obtain ⟨x1, hx1, _, hd1_hi⟩ := storeByte_domain hG1 _ b1 hs1
  obtain ⟨x2, hx2, _, hd2_hi⟩ := storeByte_domain hG2 _ b2 hs2
  obtain ⟨x3, hx3, _, hd3_hi⟩ := storeByte_domain hG3 _ b3 hs3
  obtain ⟨x4, hx4, _, hd4_hi⟩ := storeByte_domain hG4 _ b4 hs4
  obtain ⟨x5, hx5, _, hd5_hi⟩ := storeByte_domain hG5 _ b5 hs5
  obtain ⟨x6, hx6, _, hd6_hi⟩ := storeByte_domain hG6 _ b6 hs6
  obtain ⟨x7, hx7, _, hd7_hi⟩ := storeByte_domain hG7 _ b7 hs7
  rw [ex0] at hx0; injection hx0 with hx0; injection hx0 with hx0; injection hx0 with hx0; subst hx0
  rw [ex1] at hx1; injection hx1 with hx1; injection hx1 with hx1; injection hx1 with hx1; subst hx1
  rw [ex2] at hx2; injection hx2 with hx2; injection hx2 with hx2; injection hx2 with hx2; subst hx2
  rw [ex3] at hx3; injection hx3 with hx3; injection hx3 with hx3; injection hx3 with hx3; subst hx3
  rw [ex4] at hx4; injection hx4 with hx4; injection hx4 with hx4; injection hx4 with hx4; subst hx4
  rw [ex5] at hx5; injection hx5 with hx5; injection hx5 with hx5; injection hx5 with hx5; subst hx5
  rw [ex6] at hx6; injection hx6 with hx6; injection hx6 with hx6; injection hx6 with hx6; subst hx6
  rw [ex7] at hx7; injection hx7 with hx7; injection hx7 with hx7; injection hx7 with hx7; subst hx7
  have a1 : (dst0 + iw + 1).toNat = (dst0 + iw).toNat + 1 :=
    BitVec.toNat_add_of_lt (by change (dst0 + iw).toNat + 1 < 2 ^ 64; omega)
  have a2 : (dst0 + iw + 2).toNat = (dst0 + iw).toNat + 2 := by
    rw [a1] at hd1_hi; exact BitVec.toNat_add_of_lt (by change (dst0 + iw).toNat + 2 < 2 ^ 64; omega)
  have a3 : (dst0 + iw + 3).toNat = (dst0 + iw).toNat + 3 := by
    rw [a2] at hd2_hi; exact BitVec.toNat_add_of_lt (by change (dst0 + iw).toNat + 3 < 2 ^ 64; omega)
  have a4 : (dst0 + iw + 4).toNat = (dst0 + iw).toNat + 4 := by
    rw [a3] at hd3_hi; exact BitVec.toNat_add_of_lt (by change (dst0 + iw).toNat + 4 < 2 ^ 64; omega)
  have a5 : (dst0 + iw + 5).toNat = (dst0 + iw).toNat + 5 := by
    rw [a4] at hd4_hi; exact BitVec.toNat_add_of_lt (by change (dst0 + iw).toNat + 5 < 2 ^ 64; omega)
  have a6 : (dst0 + iw + 6).toNat = (dst0 + iw).toNat + 6 := by
    rw [a5] at hd5_hi; exact BitVec.toNat_add_of_lt (by change (dst0 + iw).toNat + 6 < 2 ^ 64; omega)
  have a7 : (dst0 + iw + 7).toNat = (dst0 + iw).toNat + 7 := by
    rw [a6] at hd6_hi; exact BitVec.toNat_add_of_lt (by change (dst0 + iw).toNat + 7 < 2 ^ 64; omega)
  have hcur8 : sourceBase ≤ (dst0 + iw).toNat ∧ (dst0 + iw).toNat + (8 : BitVec 64).toNat ≤ heapEnd := by
    rw [a7] at hd7_hi; exact ⟨hd0_lo, by change (dst0 + iw).toNat + 8 ≤ heapEnd; omega⟩
  obtain ⟨hdi_eq, hik_eq, hle_ik, hdlo, hdhi⟩ :=
    step_domain_nowrap dst0 iw n0 8 hle hdom hcur8 (by decide) (by decide) hnl
  have hk8_val : (8 : BitVec 64).toNat = 8 := rfl
  have hin8 : 0 < 8 → ∃ i ∈ [(dst0.toNat, n0.toNat)],
      i.1 ≤ (dst0 + iw).toNat ∧ (dst0 + iw).toNat + 8 ≤ i.1 + i.2 :=
    fun _ => ⟨(dst0.toNat, n0.toNat), List.mem_singleton.2 rfl, by omega, by omega⟩
  have eff0 := byteEff_storeByte_at hGd _ b0 (dst0 + iw) 0 8 (by omega) hin8 (by omega)
    (by simpa [BitVec.add_zero] using ex0)
  have eff1 := byteEff_storeByte_at hG1 _ b1 (dst0 + iw) 1 8 (by omega) hin8 (by omega) ex1
  have eff2 := byteEff_storeByte_at hG2 _ b2 (dst0 + iw) 2 8 (by omega) hin8 (by omega) ex2
  have eff3 := byteEff_storeByte_at hG3 _ b3 (dst0 + iw) 3 8 (by omega) hin8 (by omega) ex3
  have eff4 := byteEff_storeByte_at hG4 _ b4 (dst0 + iw) 4 8 (by omega) hin8 (by omega) ex4
  have eff5 := byteEff_storeByte_at hG5 _ b5 (dst0 + iw) 5 8 (by omega) hin8 (by omega) ex5
  have eff6 := byteEff_storeByte_at hG6 _ b6 (dst0 + iw) 6 8 (by omega) hin8 (by omega) ex6
  have eff7 := byteEff_storeByte_at hG7 _ b7 (dst0 + iw) 7 8 (by omega) hin8 (by omega) ex7
  change CopyInv s0 dst0 n0 (evaluateHOLFiniteState sd body).2
  rw [heq1, heq2, heq3, heq4, heq5, heq6, heq7, heq8]
  exact assign_i_copyInv hG8.code hG8
    (heffd.trans (eff0.trans (eff1.trans (eff2.trans (eff3.trans (eff4.trans (eff5.trans (eff6.trans eff7))))))))
    hd8 hn8 hi8 hle_ik hdlo hdhi

private theorem step_copy_loop1b {F : Type} {s0 : PanSemStateFiniteExact 64 F} {dst0 n0 : BitVec 64}
    (b0 : ExpHOL 64)
    (s : PanSemStateFiniteExact 64 F) (w : BitVec 64)
    (hinv : CopyInv s0 dst0 n0 s)
    (hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) = some (.val (.word w)))
    (hw : w ≠ 0) :
    let body :=
      (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) b0)
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])))
    (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none →
      CopyInv s0 dst0 n0 (evaluateHOLFiniteState (decClockHOLFinite s) body).2 := by
  intro body hnone
  obtain ⟨hc, hG, heff, hdst, hn, iw, hi, hle, hdom⟩ := hinv
  let sd := decClockHOLFinite s
  have hGd : GuestInv sd := guestInv_congr (s := s) rfl rfl rfl rfl hG
  have heffd : ByteEff s0 sd [(dst0.toNat, n0.toNat)] := heff.locals_clock s.locals (s.clock - 1)
  have hlt := eval_lower_true s n0 iw w hn hi hcond hw
  rw [BitVec.lt_def] at hlt
  have hnl : ¬ (n0 < iw + 1) := by
    rw [BitVec.lt_def]
    have := n0.isLt
    have : (iw + 1).toNat = iw.toNat + 1 := BitVec.toNat_add_of_lt (by change iw.toNat + 1 < 2 ^ 64; omega)
    omega
  obtain ⟨hs0, _, heq1, hl1⟩ := seq_store_none sd _ _ (evaluate_storeByte_control_frame sd _ _).2.2.1 hnone
  let s1 := (evaluateHOLFiniteState sd (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) b0)).2
  have hG1 : GuestInv s1 := guestInv_evaluate sd _ hGd
  have ex0 := eval_add2_locals sd _ _ dst0 iw hdst hi
  obtain ⟨x0, hx0, hd0_lo, hd0_hi⟩ := storeByte_domain hGd _ b0 hs0
  rw [ex0] at hx0; injection hx0 with hx0; injection hx0 with hx0; injection hx0 with hx0; subst hx0
  obtain ⟨hdi_eq, hik_eq, hle_ik, hdlo, hdhi⟩ :=
    step_domain_nowrap dst0 iw n0 1 hle hdom ⟨hd0_lo, hd0_hi⟩ (by decide) (by decide) hnl
  have hk1_val : (1 : BitVec 64).toNat = 1 := rfl
  have eff0 := byteEff_storeByte_at hGd _ b0 (dst0 + iw) 0 1 hd0_hi
    (fun _ => ⟨(dst0.toNat, n0.toNat), List.mem_singleton.2 rfl, by omega, by omega⟩)
    (by omega) (by simpa [BitVec.add_zero] using ex0)
  change CopyInv s0 dst0 n0 (evaluateHOLFiniteState sd body).2
  rw [heq1]
  exact assign_i_copyInv hG1.code hG1 (heffd.trans eff0)
    (by rw [hl1]; exact hdst) (by rw [hl1]; exact hn) (by rw [hl1]; exact hi) hle_ik hdlo hdhi

private theorem copy_body_eff {F : Type}
    (alignCond v0 v8 v16 v24 b0 b1 b2 b3 b4 b5 b6 b7 : ExpHOL 64)
    (hv0 : ∀ (t : PanSemStateFiniteExact 64 F) v, @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) v0 = some v → ∃ w, v = .val (.word w))
    (hv8 : ∀ (t : PanSemStateFiniteExact 64 F) v, @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) v8 = some v → ∃ w, v = .val (.word w))
    (hv16 : ∀ (t : PanSemStateFiniteExact 64 F) v, @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) v16 = some v → ∃ w, v = .val (.word w))
    (hv24 : ∀ (t : PanSemStateFiniteExact 64 F) v, @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) v24 = some v → ∃ w, v = .val (.word w))
    (s0 : PanSemStateFiniteExact 64 F) (dst0 n0 : BitVec 64)
    (hc : s0.code = originalRuntimeCode) (hG : GuestInv s0)
    (hdst : s0.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (hn : s0.locals.lookup (ofString "n") = some (.val (.word n0))) :
    let w32 := ProgHOL.while (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 32]))
      (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) v0)
        (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 8]) v8)
          (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 16]) v16)
            (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 24]) v24)
              (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 32]))))))
    let w8w := ProgHOL.while (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 8]))
      (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) v0)
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 8])))
    let w8b := ProgHOL.while (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 8]))
      (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) b0)
      (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 1]) b1)
      (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 2]) b2)
      (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 3]) b3)
      (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 4]) b4)
      (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 5]) b5)
      (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 6]) b6)
      (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 7]) b7)
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 8]))))))))))
    let w1b := ProgHOL.while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n")))
      (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) b0)
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])))
    let fullBody := ProgHOL.dec (ofString "i") .one (.const 0)
      (.seq (.ite alignCond (.seq w32 w8w) .skip) (.seq w8b (.seq w1b (.return (.const 0)))))
    Resumes (evaluateHOLFiniteState s0 fullBody).1 →
      ByteEff s0 (evaluateHOLFiniteState s0 fullBody).2 [(dst0.toNat, n0.toNat)] ∧
      (0 < n0.toNat → sourceBase ≤ dst0.toNat ∧ dst0.toNat + n0.toNat ≤ heapEnd) := by
  intro w32 w8w w8b w1b fullBody hres
  have hdec : evaluateHOLFiniteState s0 fullBody =
      let si := setVarHOLFinite (ofString "i") (.val (.word 0)) s0
      let r := evaluateHOLFiniteState si (.seq (.ite alignCond (.seq w32 w8w) .skip) (.seq w8b (.seq w1b (.return (.const 0)))))
      (r.1, { r.2 with locals := HolFiniteMapExact.resVarEq r.2.locals (ofString "i", s0.locals.lookup (ofString "i")) }) := by
    rw [evaluateHOLFiniteState_dec_total]
    simp [evalHOLExact, shapeEqHOL, shapeOfHOLExact]
  rw [hdec] at hres ⊢
  dsimp only at hres ⊢
  let si := setVarHOLFinite (ofString "i") (.val (.word 0)) s0
  have hinv_si : CopyInv s0 dst0 n0 si := by
    refine ⟨hc, guestInv_setVar _ _ s0 hG, (ByteEff.refl s0 _).locals_clock _ s0.clock, ?_, ?_, 0, ?_, by simp, fun h => by simp at h⟩
    · simp [si, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hdst, show ofString "i" ≠ ofString "dst" by decide]
    · simp [si, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn, show ofString "i" ≠ ofString "n" by decide]
    · simp [si, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  rw [evaluateHOLFiniteState_seq_line780] at hres ⊢
  rcases h1 : evaluateHOLFiniteState si (.ite alignCond (.seq w32 w8w) .skip) with ⟨r1, m1⟩
  rw [h1] at hres
  cases r1 with
  | some _ =>
    exfalso; exact evaluate_noReturnOrRaise (.ite alignCond (.seq w32 w8w) .skip) rfl si (by rw [h1]; exact hres)
  | none =>
    have hinv_m1 : CopyInv s0 dst0 n0 m1 := by
      rw [evaluateHOLFiniteState_ite] at h1
      split at h1
      · split at h1
        · rw [evaluateHOLFiniteState_skip] at h1; injection h1 with _ hm1; subst hm1; exact hinv_si
        · rw [evaluateHOLFiniteState_seq_line780] at h1
          rcases hw32 : evaluateHOLFiniteState si w32 with ⟨rw32, mw32⟩
          rw [hw32] at h1
          cases rw32 with
          | some _ => simp at h1
          | none =>
            have hinv_32 := (while_copyInv _ _ rfl (step_copy_loop32 v0 v8 v16 v24 hv0 hv8 hv16 hv24)
              si.clock si mw32 le_rfl hinv_si hw32).1
            exact (while_copyInv _ _ rfl (step_copy_loop8w v0 hv0)
              mw32.clock mw32 m1 le_rfl hinv_32 h1).1
      · simp at h1
    dsimp only at hres ⊢
    rw [evaluateHOLFiniteState_seq_line780] at hres ⊢
    rcases h2 : evaluateHOLFiniteState m1 w8b with ⟨r2, m2⟩
    rw [h2] at hres
    cases r2 with
    | some _ =>
      exfalso; exact evaluate_noReturnOrRaise w8b rfl m1 (by rw [h2]; exact hres)
    | none =>
      have hinv_m2 := (while_copyInv _ _ rfl (step_copy_loop8b b0 b1 b2 b3 b4 b5 b6 b7)
        m1.clock m1 m2 le_rfl hinv_m1 h2).1
      dsimp only at hres ⊢
      rw [evaluateHOLFiniteState_seq_line780] at hres ⊢
      rcases h3 : evaluateHOLFiniteState m2 w1b with ⟨r3, m3⟩
      rw [h3] at hres
      cases r3 with
      | some _ =>
        exfalso; exact evaluate_noReturnOrRaise w1b rfl m2 (by rw [h3]; exact hres)
      | none =>
        obtain ⟨hinv_m3, hfalse3⟩ := while_copyInv _ _ rfl (step_copy_loop1b b0)
          m2.clock m2 m3 le_rfl hinv_m2 h3
        dsimp only at hres ⊢
        obtain ⟨_, _, heff3, _, hn3, iw3, hi3, hle3, hdom3⟩ := hinv_m3
        have heq_in : iw3.toNat = n0.toNat := by
          simp only [evalHOLExact, hi3, hn3, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def] at hfalse3
          by_cases hlt3 : iw3.toNat < n0.toNat
          · simp [hlt3] at hfalse3
          · omega
        have hret_eff : ByteEff s0 (evaluateHOLFiniteState m3 (.return (.const 0))).2 [(dst0.toNat, n0.toNat)] := by
          rw [evaluateHOLFiniteState_return]
          dsimp only [evalHOLExact, shapeOfHOLExact]
          split
          · exact heff3.locals_clock _ m3.clock
          · exact heff3
        exact ⟨hret_eff.locals_clock _ _, fun hpos => by rw [← heq_in] at hpos ⊢; exact hdom3 hpos⟩

theorem memzero_body_eff {F : Type} (s0 : PanSemStateFiniteExact 64 F) (dst0 n0 : BitVec 64)
    (hc : s0.code = originalRuntimeCode) (hG : GuestInv s0)
    (hdst : s0.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (hn : s0.locals.lookup (ofString "n") = some (.val (.word n0)))
    (hres : Resumes (evaluateHOLFiniteState s0 (sourceFnBody Guest.Software.guestFn_memzero)).1) :
    ByteEff s0 (evaluateHOLFiniteState s0 (sourceFnBody Guest.Software.guestFn_memzero)).2
      [(dst0.toNat, n0.toNat)] ∧
    (0 < n0.toNat → sourceBase ≤ dst0.toNat ∧ dst0.toNat + n0.toNat ≤ heapEnd) := by
  have hc0 : ∀ (t : PanSemStateFiniteExact 64 F) v,
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) (.const 0) = some v →
      ∃ w : BitVec 64, v = .val (.word w) := fun _ _ h => by injection h with h'; exact ⟨0, h'.symm⟩
  exact copy_body_eff _ _ _ _ _ _ _ _ _ _ _ _ _ hc0 hc0 hc0 hc0 s0 dst0 n0 hc hG hdst hn hres

theorem memcpy_body_eff {F : Type} (s0 : PanSemStateFiniteExact 64 F) (dst0 n0 : BitVec 64)
    (hc : s0.code = originalRuntimeCode) (hG : GuestInv s0)
    (hdst : s0.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (hn : s0.locals.lookup (ofString "n") = some (.val (.word n0)))
    (hres : Resumes (evaluateHOLFiniteState s0 (sourceFnBody Guest.Software.guestFn_memcpy)).1) :
    ByteEff s0 (evaluateHOLFiniteState s0 (sourceFnBody Guest.Software.guestFn_memcpy)).2
      [(dst0.toNat, n0.toNat)] ∧
    (0 < n0.toNat → sourceBase ≤ dst0.toNat ∧ dst0.toNat + n0.toNat ≤ heapEnd) := by
  exact copy_body_eff _ _ _ _ _ _ _ _ _ _ _ _ _
    (fun t => eval_load_one_word t _) (fun t => eval_load_one_word t _)
    (fun t => eval_load_one_word t _) (fun t => eval_load_one_word t _)
    s0 dst0 n0 hc hG hdst hn hres

/-! ## 4. Composable `ByteEff` statement combinators & helper callees -/

theorem byteEff_seq {F : Type} {s : PanSemStateFiniteExact 64 F} {a b : ProgHOL 64} {Rl : List Ivl}
    (ha : ByteEff s (evaluateHOLFiniteState s a).2 Rl)
    (hb : ∀ m, evaluateHOLFiniteState s a = (none, m) → ByteEff m (evaluateHOLFiniteState m b).2 Rl) :
    ByteEff s (evaluateHOLFiniteState s (.seq a b)).2 Rl := by
  rw [evaluateHOLFiniteState_seq_line780]
  rcases hr : evaluateHOLFiniteState s a with ⟨r1, m⟩
  rw [hr] at ha
  cases r1 with
  | none => exact ha.trans (hb m hr)
  | some _ => exact ha

theorem byteEff_ite {F : Type} {s : PanSemStateFiniteExact 64 F} (cond : ExpHOL 64)
    {yes no : ProgHOL 64} {Rl : List Ivl}
    (hy : ByteEff s (evaluateHOLFiniteState s yes).2 Rl)
    (hn : ByteEff s (evaluateHOLFiniteState s no).2 Rl) :
    ByteEff s (evaluateHOLFiniteState s (.ite cond yes no)).2 Rl := by
  rw [evaluateHOLFiniteState_ite]
  split
  · split
    · exact hn
    · exact hy
  · exact ByteEff.refl s Rl

theorem byteEff_dec {F : Type} {s : PanSemStateFiniteExact 64 F}
    (name : MlS) (sh : ShapeHOL) (init : ExpHOL 64) {body : ProgHOL 64} {Rl : List Ivl}
    (hb : ∀ val,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) init = some val →
      ByteEff (setVarHOLFinite name val s) (evaluateHOLFiniteState (setVarHOLFinite name val s) body).2 Rl) :
    ByteEff s (evaluateHOLFiniteState s (.dec name sh init body)).2 Rl := by
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  split
  · exact ByteEff.refl s Rl
  · rename_i val hval
    split
    · exact ((ByteEff.refl s Rl).locals_clock _ s.clock).trans (hb val hval) |>.locals_clock _ _
    · exact ByteEff.refl s Rl

theorem byteEff_assign_local {F : Type} (s : PanSemStateFiniteExact 64 F)
    (name : MlS) (e : ExpHOL 64) (Rl : List Ivl) :
    ByteEff s (evaluateHOLFiniteState s (.assign .local name e)).2 Rl := by
  rw [evaluateHOLFiniteState_assign]
  split
  · exact ByteEff.refl s Rl
  · split
    · exact (ByteEff.refl s Rl).locals_clock _ s.clock
    · exact ByteEff.refl s Rl

theorem byteEff_return {F : Type} (s : PanSemStateFiniteExact 64 F)
    (e : ExpHOL 64) (Rl : List Ivl) :
    ByteEff s (evaluateHOLFiniteState s (.return e)).2 Rl := by
  rw [evaluateHOLFiniteState_return]
  split
  · exact ByteEff.refl s Rl
  · split
    · exact (ByteEff.refl s Rl).locals_clock _ s.clock
    · exact ByteEff.refl s Rl

theorem byteEff_skip {F : Type} (s : PanSemStateFiniteExact 64 F) (Rl : List Ivl) :
    ByteEff s (evaluateHOLFiniteState s .skip).2 Rl := by
  rw [evaluateHOLFiniteState_skip]; exact ByteEff.refl s Rl

theorem byteEff_while {F : Type} (cond : ExpHOL 64) {body : ProgHOL 64} {Rl : List Ivl}
    (hb : ∀ (t : PanSemStateFiniteExact 64 F), t.code = originalRuntimeCode → GuestInv t →
      ByteEff t (evaluateHOLFiniteState t body).2 Rl)
    (s : PanSemStateFiniteExact 64 F) (hc : s.code = originalRuntimeCode) (hG : GuestInv s) :
    ByteEff s (evaluateHOLFiniteState s (.while cond body)).2 Rl := by
  rw [evaluateHOLFiniteState_while_total]
  split
  · split
    · split
      · exact (ByteEff.refl s Rl).locals_clock _ s.clock
      · dsimp only
        rw [fixClockHOLFinite_evaluateState]
        have hGd : GuestInv (decClockHOLFinite s) := guestInv_congr (s := s) rfl rfl rfl rfl hG
        have ih1 := hb (decClockHOLFinite s) hc hGd
        have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
        rcases hbr : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨r1, mid⟩
        rw [hbr] at ih1 rem
        have hlt : mid.clock < s.clock := by change mid.clock ≤ s.clock - 1 at rem; omega
        have heff1 : ByteEff s mid Rl := ((ByteEff.refl s Rl).locals_clock _ _).trans ih1
        have hGm : GuestInv mid := guestInv_congr heff1.code heff1.memaddrs heff1.shMemaddrs heff1.baseAddr hG
        cases r1 with
        | none => exact heff1.trans (byteEff_while cond hb mid (heff1.code.trans hc) hGm)
        | some res =>
          cases res with
          | «continue» => exact heff1.trans (byteEff_while cond hb mid (heff1.code.trans hc) hGm)
          | _ => exact heff1
    · exact ByteEff.refl s Rl
  · exact ByteEff.refl s Rl
termination_by s.clock

/-- Call wrapper for a `ByteEff` callee that only takes effect when `Resumes` holds
(or unconditionally on any non-timeout outcome). -/
def FunByteEff (fname : MlS)
    (argR : List (ValueHOL 64) → HolFiniteMapExact MlS (ValueHOL 64) → List Ivl) : Prop :=
  ∃ (params : List (MlS × ShapeHOL)) (body : ProgHOL 64) (retShape : ShapeHOL),
    originalRuntimeCode.lookup fname = some (params, body, retShape) ∧
    ∀ {F : Type} (entry : PanSemStateFiniteExact 64 F) (vals : List (ValueHOL 64)),
      entry.code = originalRuntimeCode → GuestInv entry →
      lookupCodeHOLFinite originalRuntimeCode.lookup fname vals = some (body, entry.locals, retShape) →
      (evaluateHOLFiniteState entry body).1 ≠ some .timeOut →
      Resumes (evaluateHOLFiniteState entry body).1 →
      ByteEff entry (evaluateHOLFiniteState entry body).2 (argR vals entry.globals)

theorem call0_byteEff {F : Type} {fname : MlS}
    {argR : List (ValueHOL 64) → HolFiniteMapExact MlS (ValueHOL 64) → List Ivl}
    (hf : FunByteEff fname argR)
    (s : PanSemStateFiniteExact 64 F) (args : List (ExpHOL 64)) (Rl : List Ivl)
    (hc : s.code = originalRuntimeCode) (hG : GuestInv s)
    (hsub : ∀ vals,
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some vals →
      ∀ i ∈ argR vals s.globals, 0 < i.2 → ∃ j ∈ Rl, j.1 ≤ i.1 ∧ i.1 + i.2 ≤ j.1 + j.2)
    (hnt : (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).1 ≠ some .timeOut)
    (hor : (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).1 = none ∨
      Resumes (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).1) :
    ByteEff s (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).2 Rl := by
  obtain ⟨params, body, ret, hlook, hspec⟩ := hf
  rw [evaluateHOLFiniteState_call] at hnt hor ⊢
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vals
  · exact ByteEff.refl s Rl
  · simp only [hargs] at hnt hor ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname vals with _ | ⟨body', callee, ret'⟩
    · exact ByteEff.refl s Rl
    · simp only [hl] at hnt hor ⊢
      have hsame := lookupCodeHOLFinite_installed_body s.code.lookup fname params body body'
        ret ret' vals callee (by rw [hc]; exact hlook) hl
      subst hsame
      have hret := lookupCodeHOLFinite_installed_return s fname params body' body'
        ret ret' vals callee (by rw [hc]; exact hlook) hl
      subst hret
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt hor ⊢
        let entry := callEntryStateHOLFinite s callee
        have hGe : GuestInv entry := guestInv_callEntry s callee hG
        have hl_e : lookupCodeHOLFinite originalRuntimeCode.lookup fname vals = some (body', entry.locals, ret') := by
          simpa [hc, entry, callEntryStateHOLFinite] using hl
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with ⟨res, post⟩
        simp only [hrun] at hnt hor ⊢
        have hntb : res ≠ some .timeOut := by intro h; subst h; simp at hnt
        have runSpec (hr : Resumes res) : ByteEff s post Rl := by
          have hb := hspec entry vals hc hGe hl_e (by dsimp only [entry]; rw [hrun]; exact hntb)
            (by dsimp only [entry]; rw [hrun]; exact hr)
          dsimp only [entry] at hb; rw [hrun] at hb
          exact (((ByteEff.refl s _).locals_clock _ _).trans hb).mono (hsub vals hargs)
        cases res with
        | none =>
          exfalso; rcases hor with h | ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
        | some r =>
          cases r with
          | returned v =>
            dsimp only at hor ⊢
            split
            · exact (runSpec (Or.inl ⟨v, rfl⟩)).locals_clock _ _
            · rename_i hbad
              rw [if_neg hbad] at hor
              exfalso; rcases hor with h | ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
          | exception eid ev =>
            have hnot_trap : eid ≠ ofString "TrapErr" := by
              rcases hor with h | ⟨_, h⟩ | ⟨e', v', h, hne⟩
              · simp at h
              · simp at h
              · simp at h; obtain ⟨rfl, _⟩ := h; exact hne
            exact (runSpec (Or.inr ⟨eid, ev, rfl, hnot_trap⟩)).locals_clock _ _
          | _ =>
            exfalso; rcases hor with h | ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h


def valWordNat : ValueHOL 64 → Nat
  | .val (.word w) => w.toNat
  | _ => 0

def globMapN (G : HolFiniteMapExact MlS (ValueHOL 64)) (name : String) : Nat :=
  match G.lookup (ofString name) with
  | some (.val (.word w)) => w.toNat
  | _ => 0

def globBufIvl (G : HolFiniteMapExact MlS (ValueHOL 64)) (name : String) (sz : Nat) : Ivl :=
  (globMapN G name, if globMapN G name = 0 then 0 else sz)

theorem globBufIvl_eq_bufferRegion {F : Type} (s : PanSemStateFiniteExact 64 F) (name : String) (sz : Nat) :
    globBufIvl s.globals name sz = bufferRegion s (name, sz) := rfl

theorem lookupCode_one_word {fname p1 : MlS} {body : ProgHOL 64} {vals : List (ValueHOL 64)}
    {L : HolFiniteMapExact MlS (ValueHOL 64)}
    (hlook : originalRuntimeCode.lookup fname = some ([(p1, .one)], body, .one))
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup fname vals = some (body, L, .one)) :
    ∃ w1 : BitVec 64,
      vals = [.val (.word w1)] ∧
      L.lookup p1 = some (.val (.word w1)) := by
  have hx := lookupCodeHOLFinite_eq_some originalRuntimeCode.lookup fname vals body L .one hl
  simp only [lookupCodeHOLExact, hlook] at hx
  rcases vals with _ | ⟨v1, _ | _⟩
  · simp at hx
  · rcases v1 with ⟨⟨w1⟩⟩ | _ | _ <;> simp [shapeOfHOLExact, shapeEqHOL] at hx
    exact ⟨w1, rfl, by rw [← hx]; simp⟩
  · simp at hx

theorem lookupCode_two_words {fname p1 p2 : MlS} {body : ProgHOL 64} {vals : List (ValueHOL 64)}
    {L : HolFiniteMapExact MlS (ValueHOL 64)}
    (hne : p1 ≠ p2)
    (hlook : originalRuntimeCode.lookup fname = some ([(p1, .one), (p2, .one)], body, .one))
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup fname vals = some (body, L, .one)) :
    ∃ w1 w2 : BitVec 64,
      vals = [.val (.word w1), .val (.word w2)] ∧
      L.lookup p1 = some (.val (.word w1)) ∧
      L.lookup p2 = some (.val (.word w2)) := by
  have hx := lookupCodeHOLFinite_eq_some originalRuntimeCode.lookup fname vals body L .one hl
  simp only [lookupCodeHOLExact, hlook] at hx
  rcases vals with _ | ⟨v1, _ | ⟨v2, _ | _⟩⟩
  · simp at hx
  · simp at hx
  · rcases v1 with ⟨⟨w1⟩⟩ | _ | _ <;> rcases v2 with ⟨⟨w2⟩⟩ | _ | _ <;>
      simp [shapeOfHOLExact, shapeEqHOL] at hx
    obtain ⟨_, hL⟩ := hx
    refine ⟨w1, w2, rfl, ?_, ?_⟩ <;> (rw [← hL]; simp [hne, Ne.symm hne])
  · simp at hx

theorem lookupCode_three_words {fname p1 p2 p3 : MlS} {body : ProgHOL 64} {vals : List (ValueHOL 64)}
    {L : HolFiniteMapExact MlS (ValueHOL 64)}
    (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h23 : p2 ≠ p3)
    (hlook : originalRuntimeCode.lookup fname = some ([(p1, .one), (p2, .one), (p3, .one)], body, .one))
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup fname vals = some (body, L, .one)) :
    ∃ w1 w2 w3 : BitVec 64,
      vals = [.val (.word w1), .val (.word w2), .val (.word w3)] ∧
      L.lookup p1 = some (.val (.word w1)) ∧
      L.lookup p2 = some (.val (.word w2)) ∧
      L.lookup p3 = some (.val (.word w3)) := by
  have hx := lookupCodeHOLFinite_eq_some originalRuntimeCode.lookup fname vals body L .one hl
  simp only [lookupCodeHOLExact, hlook] at hx
  rcases vals with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | _⟩⟩⟩
  · simp at hx
  · simp at hx
  · simp at hx
  · rcases v1 with ⟨⟨w1⟩⟩ | _ | _ <;> rcases v2 with ⟨⟨w2⟩⟩ | _ | _ <;>
      rcases v3 with ⟨⟨w3⟩⟩ | _ | _ <;> simp [shapeOfHOLExact, shapeEqHOL] at hx
    obtain ⟨_, hL⟩ := hx
    refine ⟨w1, w2, w3, rfl, ?_, ?_, ?_⟩ <;>
      (rw [← hL]; simp [h12, h13, h23, Ne.symm h12, Ne.symm h13, Ne.symm h23])
  · simp at hx

theorem lookupCode_four_words {fname p1 p2 p3 p4 : MlS} {body : ProgHOL 64} {vals : List (ValueHOL 64)}
    {L : HolFiniteMapExact MlS (ValueHOL 64)}
    (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h14 : p1 ≠ p4)
    (h23 : p2 ≠ p3) (h24 : p2 ≠ p4) (h34 : p3 ≠ p4)
    (hlook : originalRuntimeCode.lookup fname =
      some ([(p1, .one), (p2, .one), (p3, .one), (p4, .one)], body, .one))
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup fname vals = some (body, L, .one)) :
    ∃ w1 w2 w3 w4 : BitVec 64,
      vals = [.val (.word w1), .val (.word w2), .val (.word w3), .val (.word w4)] ∧
      L.lookup p1 = some (.val (.word w1)) ∧
      L.lookup p2 = some (.val (.word w2)) ∧
      L.lookup p3 = some (.val (.word w3)) ∧
      L.lookup p4 = some (.val (.word w4)) := by
  have hx := lookupCodeHOLFinite_eq_some originalRuntimeCode.lookup fname vals body L .one hl
  simp only [lookupCodeHOLExact, hlook] at hx
  rcases vals with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | ⟨v4, _ | _⟩⟩⟩⟩
  · simp at hx
  · simp at hx
  · simp at hx
  · simp at hx
  · rcases v1 with ⟨⟨w1⟩⟩ | _ | _ <;> rcases v2 with ⟨⟨w2⟩⟩ | _ | _ <;>
      rcases v3 with ⟨⟨w3⟩⟩ | _ | _ <;> rcases v4 with ⟨⟨w4⟩⟩ | _ | _ <;>
      simp [shapeOfHOLExact, shapeEqHOL] at hx
    obtain ⟨_, hL⟩ := hx
    refine ⟨w1, w2, w3, w4, rfl, ?_, ?_, ?_, ?_⟩ <;>
      (rw [← hL]; simp [h12, h13, h14, h23, h24, h34,
        Ne.symm h12, Ne.symm h13, Ne.symm h14, Ne.symm h23, Ne.symm h24, Ne.symm h24, Ne.symm h34])
  · simp at hx

theorem funByteEff_memzero :
    FunByteEff (ofString "memzero")
      (fun vals _ => [(valWordNat (vals[0]?.getD (.rStruct [])), valWordNat (vals[1]?.getD (.rStruct [])))]) := by
  refine ⟨_, _, _, lookup_memzero, fun entry vals hc hG hl _ hres => ?_⟩
  obtain ⟨dst0, n0, rfl, hdst, hn⟩ := lookupCode_two_words (by decide) lookup_memzero hl
  exact (memzero_body_eff entry dst0 n0 hc hG hdst hn hres).1

theorem funByteEff_memcpy :
    FunByteEff (ofString "memcpy")
      (fun vals _ => [(valWordNat (vals[0]?.getD (.rStruct [])), valWordNat (vals[2]?.getD (.rStruct [])))]) := by
  have hlook : originalRuntimeCode.lookup (ofString "memcpy") =
      some ([(ofString "dst", .one), (ofString "src", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_memcpy, .one) :=
    lookup_of_guestAst_getElem 16 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_memcpy) rfl
  refine ⟨_, _, _, hlook, fun entry vals hc hG hl _ hres => ?_⟩
  obtain ⟨dst0, _, n0, rfl, hdst, _, hn⟩ := lookupCode_three_words (by decide) (by decide) (by decide) hlook hl
  exact (memcpy_body_eff entry dst0 n0 hc hG hdst hn hres).1


/-! ## 3. `keccak_f1600`, `keccak_absorb_block`, `keccak256` -/

/-- Check that `prog` writes only to `[base, base + sz)` via single-word `.store` at `ptrVar + off`
(`off + 8 ≤ sz ≤ 2048`), with single-word value expressions (`const`, `op`, `shift`, `load .one`,
or local variable in `wordVars` whose wordness is preserved!), and never modifies `ptrVar` or globals. -/
def isGuaranteedWordExp (wordVars : List MlS) : ExpHOL 64 → Bool
  | .const _ | .load .one _ | .loadByte _ | .load32 _
  | .op _ _ | .panop _ _ | .cmp _ _ _ | .shift _ _ _ | .baseAddr | .topAddr => true
  | .var .local nm => wordVars.contains nm
  | _ => false

theorem eval_isGuaranteedWordExp {F : Type} (s : PanSemStateFiniteExact 64 F)
    (wordVars : List MlS)
    (hwv : ∀ nm ∈ wordVars, ∃ w : BitVec 64, s.locals.lookup nm = some (.val (.word w)))
    (e : ExpHOL 64) (he : isGuaranteedWordExp wordVars e = true) :
    ∀ v, @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e = some v →
      ∃ w : BitVec 64, v = .val (.word w) := by
  intro v hv
  cases e with
  | const c => simp [evalHOLExact] at hv; exact ⟨c, hv.symm⟩
  | baseAddr => simp [evalHOLExact] at hv; exact ⟨s.baseAddr, hv.symm⟩
  | topAddr => simp [evalHOLExact] at hv; exact ⟨s.topAddr, hv.symm⟩
  | var vk nm =>
    cases vk with
    | global => simp [isGuaranteedWordExp] at he
    | «local» =>
      have hmem : nm ∈ wordVars := List.contains_iff_mem.1 (by simpa [isGuaranteedWordExp] using he)
      obtain ⟨w, hw⟩ := hwv nm hmem
      simp [evalHOLExact, hw] at hv; exact ⟨w, hv.symm⟩
  | load sh addrExp =>
    cases sh with
    | one => exact eval_load_one_word s addrExp v hv
    | comb _ | named _ => simp [isGuaranteedWordExp] at he
  | loadByte _ =>
    simp only [evalHOLExact] at hv
    split at hv
    · simp only [Option.map_eq_some_iff] at hv
      obtain ⟨_, _, rfl⟩ := hv; exact ⟨_, rfl⟩
    · cases hv
  | load32 _ =>
    simp only [evalHOLExact] at hv
    split at hv
    · simp only [Option.map_eq_some_iff] at hv
      obtain ⟨_, _, rfl⟩ := hv; exact ⟨_, rfl⟩
    · cases hv
  | op _ _ =>
    simp only [evalHOLExact] at hv
    split at hv
    · split at hv
      · simp only [Option.map_eq_some_iff] at hv
        obtain ⟨_, _, rfl⟩ := hv; exact ⟨_, rfl⟩
      · cases hv
    · cases hv
  | panop _ _ =>
    simp only [evalHOLExact] at hv
    split at hv
    · split at hv
      · simp only [Option.map_eq_some_iff] at hv
        obtain ⟨_, _, rfl⟩ := hv; exact ⟨_, rfl⟩
      · cases hv
    · cases hv
  | cmp _ _ _ =>
    simp only [evalHOLExact] at hv
    split at hv
    · injection hv with h; exact ⟨_, h.symm⟩
    · cases hv
  | shift _ _ _ =>
    simp only [evalHOLExact] at hv
    split at hv
    · simp only [Option.map_eq_some_iff] at hv
      obtain ⟨_, _, rfl⟩ := hv; exact ⟨_, rfl⟩
    · cases hv
  | _ => simp [isGuaranteedWordExp] at he

def checkWordStoresLocal (ptrVar : MlS) (sz : Nat) (wordVars : List MlS) : ProgHOL 64 → Bool
  | .dec nm .one init b =>
      !(nm == ptrVar) && isGuaranteedWordExp wordVars init &&
      checkWordStoresLocal ptrVar sz (nm :: wordVars) b
  | .seq a b => checkWordStoresLocal ptrVar sz wordVars a && checkWordStoresLocal ptrVar sz wordVars b
  | .ite _ a b => checkWordStoresLocal ptrVar sz wordVars a && checkWordStoresLocal ptrVar sz wordVars b
  | .while _ b => checkWordStoresLocal ptrVar sz wordVars b
  | .assign .local nm e => !(nm == ptrVar) &&
      (!(wordVars.contains nm) || isGuaranteedWordExp wordVars e)
  | .store (.var .local nm) vexp =>
      (nm == ptrVar) && decide (8 ≤ sz) && isGuaranteedWordExp wordVars vexp
  | .store (.op .add [.var .local nm, .const off]) vexp =>
      (nm == ptrVar) && decide (off.toNat + 8 ≤ sz) && isGuaranteedWordExp wordVars vexp
  | .skip | .break | .continue | .return _ | .raise _ _ | .annot _ _ => true
  | _ => false

theorem checkWordStoresLocal_sound {F : Type} (ptrVar : MlS) (sz : Nat) (hsz : sz ≤ 2048)
    (wordVars : List MlS) (prog : ProgHOL 64)
    (hok : checkWordStoresLocal ptrVar sz wordVars prog = true)
    (s : PanSemStateFiniteExact 64 F) (p : BitVec 64)
    (hc : s.code = originalRuntimeCode) (hG : GuestInv s)
    (hp : s.locals.lookup ptrVar = some (.val (.word p)))
    (hwv : ∀ nm ∈ wordVars, ∃ w : BitVec 64, s.locals.lookup nm = some (.val (.word w))) :
    ByteEff s (evaluateHOLFiniteState s prog).2 [(p.toNat, sz)] ∧
    ((evaluateHOLFiniteState s prog).1 = none ∨
     (evaluateHOLFiniteState s prog).1 = some .break ∨
     (evaluateHOLFiniteState s prog).1 = some .continue →
      (evaluateHOLFiniteState s prog).2.locals.lookup ptrVar = some (.val (.word p)) ∧
      ∀ nm ∈ wordVars, ∃ w : BitVec 64,
        (evaluateHOLFiniteState s prog).2.locals.lookup nm = some (.val (.word w))) := by
  have hsb : 2048 < sourceBase := by rw [sourceBase_val]; decide
  cases shape : prog with
  | skip => rw [evaluateHOLFiniteState_skip]; exact ⟨ByteEff.refl s _, fun _ => ⟨hp, hwv⟩⟩
  | «break» => rw [evaluateHOLFiniteState_break]; exact ⟨ByteEff.refl s _, fun _ => ⟨hp, hwv⟩⟩
  | «continue» => rw [evaluateHOLFiniteState_continue]; exact ⟨ByteEff.refl s _, fun _ => ⟨hp, hwv⟩⟩
  | annot _ _ => rw [evaluateHOLFiniteState_annot]; exact ⟨ByteEff.refl s _, fun _ => ⟨hp, hwv⟩⟩
  | «return» e =>
    refine ⟨byteEff_return s e _, fun h => ?_⟩
    rw [evaluateHOLFiniteState_return] at h
    split at h
    · simp at h
    · split at h <;> simp at h
  | raise _ _ =>
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only; split
      · exact ⟨(ByteEff.refl s _).locals_clock _ _, by simp⟩
      · exact ⟨ByteEff.refl s _, by simp⟩
    · exact ⟨ByteEff.refl s _, by simp⟩
  | assign k nm e =>
    cases k with
    | global => simp [shape, checkWordStoresLocal] at hok
    | «local» =>
      have h12 : nm ≠ ptrVar ∧ (!(wordVars.contains nm) || isGuaranteedWordExp wordVars e) = true := by
        simpa [shape, checkWordStoresLocal, Bool.and_eq_true] using hok
      refine ⟨byteEff_assign_local s nm e _, fun h => ?_⟩
      rw [evaluateHOLFiniteState_assign] at h ⊢
      rcases hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e with _ | val
      · simp [hev] at h
      · simp only [hev] at h ⊢
        split at h
        · rename_i hv; rw [if_pos hv]
          refine ⟨by simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, h12.1, hp],
            fun m hm => ?_⟩
          by_cases hmn : m = nm
          · subst hmn
            have hge : isGuaranteedWordExp wordVars e = true := by
              have hmem : wordVars.contains m = true := List.contains_iff_mem.2 hm
              have h2 := h12.2
              rw [hmem] at h2; simpa using h2
            obtain ⟨w, rfl⟩ := eval_isGuaranteedWordExp s wordVars hwv e hge val hev
            exact ⟨w, by simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩
          · obtain ⟨w, hw⟩ := hwv m hm
            exact ⟨w, by simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hmn, hw]⟩
        · simp at h
  | dec nm sh init b =>
    cases sh with
    | comb _ | named _ => simp [shape, checkWordStoresLocal] at hok
    | one =>
      have h123 : (nm ≠ ptrVar ∧ isGuaranteedWordExp wordVars init = true) ∧
          checkWordStoresLocal ptrVar sz (nm :: wordVars) b = true := by
        simpa [shape, checkWordStoresLocal, Bool.and_eq_true] using hok
      rw [evaluateHOLFiniteState_dec_total]; dsimp only
      rcases hinit : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) init with _ | val
      · exact ⟨ByteEff.refl s _, by simp⟩
      · dsimp only
        split
        · obtain ⟨wi, rfl⟩ := eval_isGuaranteedWordExp s wordVars hwv init h123.1.2 val hinit
          have hp' : (setVarHOLFinite nm (.val (.word wi)) s).locals.lookup ptrVar = some (.val (.word p)) := by
            simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, h123.1.1, hp]
          have hwv' : ∀ m ∈ nm :: wordVars, ∃ w : BitVec 64,
              (setVarHOLFinite nm (.val (.word wi)) s).locals.lookup m = some (.val (.word w)) := by
            intro m hm
            by_cases hmn : m = nm
            · subst hmn; exact ⟨wi, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩
            · have hm_old : m ∈ wordVars := by simp [hmn] at hm; exact hm
              obtain ⟨w, hw⟩ := hwv m hm_old
              exact ⟨w, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hmn, hw]⟩
          have ih := checkWordStoresLocal_sound ptrVar sz hsz (nm :: wordVars) b h123.2
            (setVarHOLFinite nm (.val (.word wi)) s) p hc (guestInv_setVar nm _ s hG) hp' hwv'
          refine ⟨(((ByteEff.refl s _).locals_clock _ _).trans ih.1).locals_clock _ _, fun h => ?_⟩
          dsimp only at h ⊢
          obtain ⟨hp_post, hwv_post⟩ := ih.2 h
          refine ⟨by rw [resVarEq_lookup_ne _ nm ptrVar _ (Ne.symm h123.1.1), hp_post], fun m hm => ?_⟩
          by_cases hmn : m = nm
          · subst hmn
            obtain ⟨w0, hw0⟩ := hwv m hm
            exact ⟨w0, by simp [HolFiniteMapExact.resVarEq, hw0, HolFiniteMapExact.updateEq, FUPDATE_HOL]⟩
          · obtain ⟨w', hw'⟩ := hwv_post m (List.mem_cons_of_mem _ hm)
            exact ⟨w', by rw [resVarEq_lookup_ne _ nm m _ hmn, hw']⟩
        · exact ⟨ByteEff.refl s _, by simp⟩
  | seq a b =>
    have h12 : checkWordStoresLocal ptrVar sz wordVars a = true ∧
        checkWordStoresLocal ptrVar sz wordVars b = true := by
      simpa [shape, checkWordStoresLocal, Bool.and_eq_true] using hok
    have rem := evaluateHOLFiniteState_clock_le s a
    have iha := checkWordStoresLocal_sound ptrVar sz hsz wordVars a h12.1 s p hc hG hp hwv
    rw [evaluateHOLFiniteState_seq_line780]
    rcases hra : evaluateHOLFiniteState s a with ⟨r1, m⟩
    rw [hra] at iha rem
    cases r1 with
    | none =>
      have mclk : m.clock ≤ s.clock := rem
      obtain ⟨hpm, hwvm⟩ := iha.2 (Or.inl rfl)
      have hGm := guestInv_congr iha.1.code iha.1.memaddrs iha.1.shMemaddrs iha.1.baseAddr hG
      have ihb := checkWordStoresLocal_sound ptrVar sz hsz wordVars b h12.2 m p (iha.1.code.trans hc) hGm hpm hwvm
      exact ⟨iha.1.trans ihb.1, ihb.2⟩
    | some _ => exact iha
  | ite c a b =>
    have h12 : checkWordStoresLocal ptrVar sz wordVars a = true ∧
        checkWordStoresLocal ptrVar sz wordVars b = true := by
      simpa [shape, checkWordStoresLocal, Bool.and_eq_true] using hok
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact checkWordStoresLocal_sound ptrVar sz hsz wordVars b h12.2 s p hc hG hp hwv
      · exact checkWordStoresLocal_sound ptrVar sz hsz wordVars a h12.1 s p hc hG hp hwv
    · exact ⟨ByteEff.refl s _, by simp⟩
  | «while» c b =>
    have hb : checkWordStoresLocal ptrVar sz wordVars b = true := by
      simpa [shape, checkWordStoresLocal] using hok
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · exact ⟨(ByteEff.refl s _).locals_clock _ _, by simp⟩
        · have dec_lt : (decClockHOLFinite s).clock < s.clock := by simp only [decClockHOLFinite]; omega
          dsimp only; rw [fixClockHOLFinite_evaluateState]
          have hGd : GuestInv (decClockHOLFinite s) := guestInv_congr (s := s) rfl rfl rfl rfl hG
          have ih1 := checkWordStoresLocal_sound ptrVar sz hsz wordVars b hb (decClockHOLFinite s) p hc hGd hp hwv
          have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) b
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite s) b with ⟨r1, mid⟩
          rw [hbr] at ih1 rem
          have smaller : mid.clock < s.clock := by change mid.clock ≤ s.clock - 1 at rem; omega
          have heff1 : ByteEff s mid [(p.toNat, sz)] := ((ByteEff.refl s _).locals_clock _ _).trans ih1.1
          have hGm : GuestInv mid := guestInv_congr heff1.code heff1.memaddrs heff1.shMemaddrs heff1.baseAddr hG
          cases r1 with
          | none =>
            obtain ⟨hpm, hwvm⟩ := ih1.2 (Or.inl rfl)
            have ihw := checkWordStoresLocal_sound ptrVar sz hsz wordVars (.while c b)
              (by simpa [checkWordStoresLocal] using hb) mid p (heff1.code.trans hc) hGm hpm hwvm
            exact ⟨heff1.trans ihw.1, ihw.2⟩
          | some res =>
            cases res with
            | «continue» =>
              obtain ⟨hpm, hwvm⟩ := ih1.2 (Or.inr (Or.inr rfl))
              have ihw := checkWordStoresLocal_sound ptrVar sz hsz wordVars (.while c b)
                (by simpa [checkWordStoresLocal] using hb) mid p (heff1.code.trans hc) hGm hpm hwvm
              exact ⟨heff1.trans ihw.1, ihw.2⟩
            | «break» => exact ⟨heff1, fun _ => ih1.2 (Or.inr (Or.inl rfl))⟩
            | _ => exact ⟨heff1, by simp⟩
      · exact ⟨ByteEff.refl s _, fun _ => ⟨hp, hwv⟩⟩
    · exact ⟨ByteEff.refl s _, by simp⟩
  | store dst vexp =>
    have hloc_st := (evaluate_store_control_frame s dst vexp).2.1
    refine ⟨?_, fun _ => by rw [hloc_st]; exact ⟨hp, hwv⟩⟩
    cases dst with
    | var vk nm =>
      cases vk with
      | global => simp [shape, checkWordStoresLocal] at hok
      | «local» =>
        have h123 : (nm = ptrVar ∧ 8 ≤ sz) ∧ isGuaranteedWordExp wordVars vexp = true := by
          simpa [shape, checkWordStoresLocal, Bool.and_eq_true] using hok
        rcases h123 with ⟨⟨rfl, hsz8⟩, hv_ok⟩
        exact (byteEff_store_one hG (.var .local nm) vexp
          (eval_isGuaranteedWordExp s wordVars hwv vexp hv_ok)
          (fun x hx _ => by
            simp [evalHOLExact, hp] at hx; subst hx
            exact ⟨(p.toNat, sz), List.mem_singleton.2 rfl, le_rfl, by omega⟩)).1
    | op bop args =>
      cases bop <;> try (simp [shape, checkWordStoresLocal] at hok)
      rcases args with _ | ⟨e1, _ | ⟨e2, _ | _⟩⟩ <;> try (simp [shape, checkWordStoresLocal] at hok)
      cases e1 with
      | var vk1 nm1 =>
        cases vk1 <;> try (simp [shape, checkWordStoresLocal] at hok)
        cases e2 with
        | const off =>
          have h123 : (nm1 = ptrVar ∧ off.toNat + 8 ≤ sz) ∧ isGuaranteedWordExp wordVars vexp = true := by
            simpa [shape, checkWordStoresLocal, Bool.and_eq_true] using hok
          rcases h123 with ⟨⟨rfl, hoff⟩, hv_ok⟩
          refine (byteEff_store_one hG (.op .add [.var .local nm1, .const off]) vexp
            (eval_isGuaranteedWordExp s wordVars hwv vexp hv_ok) (fun x hx hdom => ?_)).1
          simp [evalHOLExact, evalListHOLExact, hp, valueIsWord, valueWord, wordOpHOL, wordOp] at hx
          subst hx
          rw [hG.memaddrs, ordinaryDomain_iff] at hdom
          have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := rfl
          have hp_lt := p.isLt; have hoff_lt := off.isLt
          have hnw : p.toNat + off.toNat < 2 ^ 64 := by
            by_contra hge
            have : (p + off).toNat = p.toNat + off.toNat - 2 ^ 64 := by rw [BitVec.toNat_add]; omega
            omega
          have hadd : (p + off).toNat = p.toNat + off.toNat := BitVec.toNat_add_of_lt hnw
          exact ⟨(p.toNat, sz), List.mem_singleton.2 rfl, by omega, by omega⟩
        | _ => simp [shape, checkWordStoresLocal] at hok
      | _ => simp [shape, checkWordStoresLocal] at hok
    | _ => simp [shape, checkWordStoresLocal] at hok
  | _ => simp [shape, checkWordStoresLocal] at hok
termination_by (s.clock, sizeOf prog)
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

theorem funByteEff_keccak_f1600 :
    FunByteEff (ofString "keccak_f1600")
      (fun vals _ => [(valWordNat (vals[0]?.getD (.rStruct [])), 200)]) := by
  have hlook : originalRuntimeCode.lookup (ofString "keccak_f1600") =
      some ([(ofString "stp", .one)], sourceFnBody Guest.Software.guestFn_keccak_f1600, .one) :=
    lookup_of_guestAst_getElem 101 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_keccak_f1600) rfl
  refine ⟨_, _, _, hlook, fun entry vals hc hG hl _ _ => ?_⟩
  obtain ⟨stp, rfl, hstp⟩ := lookupCode_one_word hlook hl
  exact (checkWordStoresLocal_sound (ofString "stp") 200 (by omega) []
    (sourceFnBody Guest.Software.guestFn_keccak_f1600) rfl entry stp hc hG hstp
    (fun _ h => by simp at h)).1

/-- `keccak_absorb_block(stp, blk)`: loop updates `stp + i` for `i <s 136`, then calls `keccak_f1600(stp)`. -/
private theorem absorb_loop_eff {F : Type}
    (valExp : ExpHOL 64)
    (hval : ∀ (t : PanSemStateFiniteExact 64 F) v,
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) valExp = some v →
      ∃ w : BitVec 64, v = .val (.word w))
    (k : Nat) (s : PanSemStateFiniteExact 64 F) (stp iw : BitVec 64)
    (hk : s.clock ≤ k) (hc : s.code = originalRuntimeCode) (hG : GuestInv s)
    (hstp : s.locals.lookup (ofString "stp") = some (.val (.word stp)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iw)))
    (hi_bound : iw.toNat ≤ 136 ∧ iw.toNat % 8 = 0) :
    let body := ProgHOL.seq
      (.store (.op .add [.var .local (ofString "stp"), .var .local (ofString "i")]) valExp)
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 8]))
    let lp := ProgHOL.while (.cmp .less (.var .local (ofString "i")) (.const 136)) body
    ByteEff s (evaluateHOLFiniteState s lp).2 [(stp.toNat, 200)] ∧
    ((evaluateHOLFiniteState s lp).1 = none →
      (evaluateHOLFiniteState s lp).2.locals.lookup (ofString "stp") = some (.val (.word stp))) := by
  have hsb : 200 < sourceBase := by rw [sourceBase_val]; decide
  induction k generalizing s iw with
  | zero =>
    dsimp only; rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · exact ⟨(ByteEff.refl s _).locals_clock _ _, by simp⟩
        · omega
      · exact ⟨ByteEff.refl s _, fun _ => hstp⟩
    · exact ⟨ByteEff.refl s _, by simp⟩
  | succ k ih =>
    dsimp only; rw [evaluateHOLFiniteState_while_total]
    split
    · rename_i cw hcond
      split
      · rename_i hnz
        split
        · exact ⟨(ByteEff.refl s _).locals_clock _ _, by simp⟩
        · dsimp only; rw [fixClockHOLFinite_evaluateState]
          have hlt136 : iw.toNat < 136 := by
            rw [evalHOLFinite_eq_toExact] at hcond
            simp only [evalHOLExact, hi, Compiler.Encoders.Asm.wordCmpHOL,
              holAsmSignedLess_small iw 136 (by omega) (by decide)] at hcond
            by_cases hlt : iw.toNat < (136 : BitVec 64).toNat
            · exact hlt
            · have h136_val : (136 : BitVec 64).toNat = 136 := rfl
              rw [h136_val] at hlt
              simp [hlt] at hcond; exact absurd hcond.symm hnz
          let sd := decClockHOLFinite s
          have hGd : GuestInv sd := guestInv_congr (s := s) rfl rfl rfl rfl hG
          have heff_st : ByteEff sd
              (evaluateHOLFiniteState sd (.store (.op .add [.var .local (ofString "stp"), .var .local (ofString "i")]) valExp)).2
              [(stp.toNat, 200)] := by
            refine (byteEff_store_one hGd _ valExp (hval sd) (fun x hx hdom => ?_)).1
            have ex := eval_add2_locals sd _ _ stp iw hstp hi
            rw [ex] at hx; injection hx with hx; injection hx with hx; injection hx with hx; subst hx
            rw [hGd.memaddrs, ordinaryDomain_iff] at hdom
            have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := rfl
            have hs_lt := stp.isLt
            have hnw : stp.toNat + iw.toNat < 2 ^ 64 := by
              by_contra hge
              have : (stp + iw).toNat = stp.toNat + iw.toNat - 2 ^ 64 := by rw [BitVec.toNat_add]; omega
              omega
            have hadd : (stp + iw).toNat = stp.toNat + iw.toNat := BitVec.toNat_add_of_lt hnw
            exact ⟨(stp.toNat, 200), List.mem_singleton.2 rfl, by omega, by omega⟩
          have hloc_st := (evaluate_store_control_frame sd (.op .add [.var .local (ofString "stp"), .var .local (ofString "i")]) valExp).2.1
          have hclk_st := (evaluate_store_control_frame sd (.op .add [.var .local (ofString "stp"), .var .local (ofString "i")]) valExp).2.2
          rw [evaluateHOLFiniteState_seq_line780]
          rcases hst_r : evaluateHOLFiniteState sd (.store (.op .add [.var .local (ofString "stp"), .var .local (ofString "i")]) valExp) with ⟨r1, m1⟩
          rw [hst_r] at heff_st hloc_st hclk_st
          cases r1 with
          | some r1' =>
            have hcf := (evaluate_store_control_frame sd (.op .add [.var .local (ofString "stp"), .var .local (ofString "i")]) valExp).1
            rw [hst_r] at hcf
            rcases hcf with h | h <;> simp at h; subst h
            exact ⟨((ByteEff.refl s _).locals_clock _ _).trans heff_st, by simp⟩
          | none =>
            dsimp only
            have hi_m1 : m1.locals.lookup (ofString "i") = some (.val (.word iw)) := by rw [hloc_st]; exact hi
            have hstp_m1 : m1.locals.lookup (ofString "stp") = some (.val (.word stp)) := by rw [hloc_st]; exact hstp
            have hasgn : evaluateHOLFiniteState m1
                (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 8])) =
                (none, setVarHOLFinite (ofString "i") (.val (.word (iw + 8))) m1) := by
              simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hi_m1, wordOpHOL, wordOp,
                valueIsWord, valueWord, lookupKvarHOLExact, isValidValueHOLExact, setKvarHOLFinite,
                shapeOfHOLExact, shapeEqHOL]
            rw [hasgn]; dsimp only
            let m2 := setVarHOLFinite (ofString "i") (.val (.word (iw + 8))) m1
            have heff_m2 : ByteEff s m2 [(stp.toNat, 200)] :=
              (((ByteEff.refl s _).locals_clock _ _).trans heff_st).locals_clock _ _
            have hGm2 : GuestInv m2 := guestInv_congr heff_m2.code heff_m2.memaddrs heff_m2.shMemaddrs heff_m2.baseAddr hG
            have hstp_m2 : m2.locals.lookup (ofString "stp") = some (.val (.word stp)) := by
              simp [m2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hstp_m1, show ofString "i" ≠ ofString "stp" by decide]
            have hi_m2 : m2.locals.lookup (ofString "i") = some (.val (.word (iw + 8))) := by
              simp [m2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
            have hi8_le : (iw + 8).toNat ≤ 136 ∧ (iw + 8).toNat % 8 = 0 := by
              have : (iw + 8).toNat = iw.toNat + 8 := BitVec.toNat_add_of_lt (by change iw.toNat + 8 < 2 ^ 64; omega)
              omega
            have hm2_clk : m2.clock ≤ k := by
              change m1.clock ≤ k; rw [hclk_st]; change s.clock - 1 ≤ k; omega
            have ih_res := ih m2 (iw + 8) hm2_clk (heff_m2.code.trans hc) hGm2 hstp_m2 hi_m2 hi8_le
            exact ⟨heff_m2.trans ih_res.1, ih_res.2⟩
      · exact ⟨ByteEff.refl s _, fun _ => hstp⟩
    · exact ⟨ByteEff.refl s _, by simp⟩

theorem funByteEff_keccak_absorb_block :
    FunByteEff (ofString "keccak_absorb_block")
      (fun vals _ => [(valWordNat (vals[0]?.getD (.rStruct [])), 200)]) := by
  have hlook : originalRuntimeCode.lookup (ofString "keccak_absorb_block") =
      some ([(ofString "stp", .one), (ofString "blk", .one)],
        sourceFnBody Guest.Software.guestFn_keccak_absorb_block, .one) :=
    lookup_of_guestAst_getElem 102 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_keccak_absorb_block) rfl
  refine ⟨_, _, _, hlook, fun {F} entry vals hc hG hl hnt hres => ?_⟩
  obtain ⟨stp, blk, rfl, hstp, _⟩ := lookupCode_two_words (by decide) hlook hl
  change ByteEff entry _ [(stp.toNat, 200)]
  have hop_word : ∀ (t : PanSemStateFiniteExact 64 F) bop eL v,
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) (.op bop eL) = some v →
      ∃ w : BitVec 64, v = .val (.word w) :=
    fun t bop eL => eval_isGuaranteedWordExp t [] (fun _ h => by simp at h) (.op bop eL) rfl
  let vAligned : ExpHOL 64 := InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural
    (Exp.op BinOp.xor
      [Exp.load Shape.one (Exp.op BinOp.add [Exp.var VarKind.local "stp", Exp.var VarKind.local "i"]),
       Exp.load Shape.one (Exp.op BinOp.add [Exp.var VarKind.local "blk", Exp.var VarKind.local "i"])])
  let vUnaligned : ExpHOL 64 := InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural
    (Exp.op BinOp.xor
      [Exp.load Shape.one (Exp.op BinOp.add [Exp.var VarKind.local "stp", Exp.var VarKind.local "i"]),
       Exp.op BinOp.or
        [(Exp.op BinOp.add [Exp.var VarKind.local "blk", Exp.var VarKind.local "i"]).loadByte,
         Exp.shift Shift.lsl (Exp.op BinOp.add [Exp.var VarKind.local "blk", Exp.var VarKind.local "i", Exp.const 1#64]).loadByte (Exp.const 8#64),
         Exp.shift Shift.lsl (Exp.op BinOp.add [Exp.var VarKind.local "blk", Exp.var VarKind.local "i", Exp.const 2#64]).loadByte (Exp.const 16#64),
         Exp.shift Shift.lsl (Exp.op BinOp.add [Exp.var VarKind.local "blk", Exp.var VarKind.local "i", Exp.const 3#64]).loadByte (Exp.const 24#64),
         Exp.shift Shift.lsl
          (Exp.op BinOp.or
            [(Exp.op BinOp.add [Exp.var VarKind.local "blk", Exp.var VarKind.local "i", Exp.const 4#64]).loadByte,
             Exp.shift Shift.lsl (Exp.op BinOp.add [Exp.var VarKind.local "blk", Exp.var VarKind.local "i", Exp.const 4#64, Exp.const 1#64]).loadByte (Exp.const 8#64),
             Exp.shift Shift.lsl (Exp.op BinOp.add [Exp.var VarKind.local "blk", Exp.var VarKind.local "i", Exp.const 4#64, Exp.const 2#64]).loadByte (Exp.const 16#64),
             Exp.shift Shift.lsl (Exp.op BinOp.add [Exp.var VarKind.local "blk", Exp.var VarKind.local "i", Exp.const 4#64, Exp.const 3#64]).loadByte (Exp.const 24#64)])
          (Exp.const 32#64)]])
  let lpA := ProgHOL.while (.cmp .less (.var .local (ofString "i")) (.const 136))
    (.seq (.store (.op .add [.var .local (ofString "stp"), .var .local (ofString "i")]) vAligned)
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 8])))
  let lpU := ProgHOL.while (.cmp .less (.var .local (ofString "i")) (.const 136))
    (.seq (.store (.op .add [.var .local (ofString "stp"), .var .local (ofString "i")]) vUnaligned)
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 8])))
  have hbody : sourceFnBody Guest.Software.guestFn_keccak_absorb_block =
      .dec (ofString "i") .one (.const 0)
        (.seq (.ite (.cmp .equal (.op .and [.var .local (ofString "blk"), .const 7]) (.const 0)) lpA lpU)
          (.seq (.call (some (none, none)) (ofString "keccak_f1600") [.var .local (ofString "stp")])
            (.return (.const 0)))) := rfl
  rw [hbody] at hnt hres ⊢
  rw [evaluateHOLFiniteState_dec_total] at hnt hres ⊢
  have hev0 : @evalHOLExact 64 F _ entry.toExact (fun a => Classical.propDecidable (entry.memaddrs a)) (.const 0) =
      some (.val (.word 0)) := rfl
  have hsh0 : shapeEqHOL .one (shapeOfHOLExact (.val (.word (0 : BitVec 64)))) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  dsimp only at hnt hres ⊢
  rw [hev0] at hnt hres ⊢; dsimp only at hnt hres ⊢
  rw [if_pos hsh0] at hnt hres ⊢; dsimp only at hnt hres ⊢
  let si := setVarHOLFinite (ofString "i") (.val (.word 0)) entry
  have hGi : GuestInv si := guestInv_setVar _ _ entry hG
  have hstp_i : si.locals.lookup (ofString "stp") = some (.val (.word stp)) := by
    simp [si, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hstp, show ofString "i" ≠ ofString "stp" by decide]
  have hi_i : si.locals.lookup (ofString "i") = some (.val (.word 0)) := by
    simp [si, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  rw [evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
  have hite_eff : ByteEff si (evaluateHOLFiniteState si
      (.ite (.cmp .equal (.op .and [.var .local (ofString "blk"), .const 7]) (.const 0)) lpA lpU)).2 [(stp.toNat, 200)] ∧
      ((evaluateHOLFiniteState si
        (.ite (.cmp .equal (.op .and [.var .local (ofString "blk"), .const 7]) (.const 0)) lpA lpU)).1 = none →
        (evaluateHOLFiniteState si
          (.ite (.cmp .equal (.op .and [.var .local (ofString "blk"), .const 7]) (.const 0)) lpA lpU)).2.locals.lookup
          (ofString "stp") = some (.val (.word stp))) := by
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact absorb_loop_eff vUnaligned (fun t => hop_word t _ _) si.clock si stp 0 le_rfl hc hGi hstp_i hi_i ⟨by simp, by simp⟩
      · exact absorb_loop_eff vAligned (fun t => hop_word t _ _) si.clock si stp 0 le_rfl hc hGi hstp_i hi_i ⟨by simp, by simp⟩
    · exact ⟨ByteEff.refl si _, by simp⟩
  rcases h1 : evaluateHOLFiniteState si
      (.ite (.cmp .equal (.op .and [.var .local (ofString "blk"), .const 7]) (.const 0)) lpA lpU) with ⟨r1, s1⟩
  rw [h1] at hnt hres hite_eff
  have heff_e1 : ByteEff entry s1 [(stp.toNat, 200)] := ((ByteEff.refl entry _).locals_clock _ _).trans hite_eff.1
  cases r1 with
  | some _ => exact heff_e1.locals_clock _ _
  | none =>
    dsimp only at hnt hres ⊢
    have hstp_1 : s1.locals.lookup (ofString "stp") = some (.val (.word stp)) := hite_eff.2 rfl
    have hGs1 : GuestInv s1 := guestInv_congr heff_e1.code heff_e1.memaddrs heff_e1.shMemaddrs heff_e1.baseAddr hG
    have hc_s1 : s1.code = originalRuntimeCode := heff_e1.code.trans hc
    rw [evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
    rcases hc_f : evaluateHOLFiniteState s1
        (.call (some (none, none)) (ofString "keccak_f1600") [.var .local (ofString "stp")]) with ⟨rf, sf⟩
    rw [hc_f] at hnt hres
    have hnt_f : rf ≠ some .timeOut := by intro h; subst h; simp at hnt
    have hargs_f : evalListHOLFinite s1 (h := fun a => Classical.propDecidable (s1.memaddrs a))
        [.var .local (ofString "stp")] = some [.val (.word stp)] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hstp_1]
    have heff_f : ByteEff s1 sf [(stp.toNat, 200)] := by
      have := call0_byteEff funByteEff_keccak_f1600 s1 _ [(stp.toNat, 200)] hc_s1 hGs1
        (fun vs hvs i hi _ => by
          rw [hargs_f] at hvs; injection hvs with hvs; subst hvs
          simp [valWordNat] at hi; subst hi
          exact ⟨(stp.toNat, 200), List.mem_singleton.2 rfl, le_rfl, le_rfl⟩)
        (by rw [hc_f]; exact hnt_f)
        (by rw [hc_f]; cases rf with | none => exact Or.inl rfl | some _ => exact Or.inr hres)
      rwa [hc_f] at this
    cases rf with
    | some _ => exact (heff_e1.trans heff_f).locals_clock _ _
    | none => exact ((heff_e1.trans heff_f).trans (byteEff_return sf _ _)).locals_clock _ _

private theorem call0_any_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (fname : MlS) (args : List (ExpHOL 64))
    (hnone : (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).1 = none) :
    (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).2.locals = s.locals := by
  rw [evaluateHOLFiniteState_call]
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vals
  · rfl
  · dsimp only
    rcases hl : lookupCodeHOLFinite s.code.lookup fname vals with _ | ⟨b, c, r⟩
    · rfl
    · dsimp only
      by_cases hclk : s.clock = 0
      · exfalso
        rw [evaluateHOLFiniteState_call, hargs] at hnone
        simp [hl, hclk] at hnone
      · rw [if_neg hclk]
        rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s c) b with ⟨rb, pb⟩
        cases rb with
        | none =>
          exfalso; rw [evaluateHOLFiniteState_call, hargs] at hnone
          simp [hl, hclk, hb] at hnone
        | some rb' =>
          cases rb' with
          | returned rv =>
            dsimp only
            split
            · rfl
            · rename_i hbad
              exfalso; rw [evaluateHOLFiniteState_call, hargs] at hnone
              simp [hl, hclk, hb, hbad] at hnone
          | _ =>
            exfalso; rw [evaluateHOLFiniteState_call, hargs] at hnone
            simp [hl, hclk, hb] at hnone

private theorem eval_cmp_notLower_i136 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (n iw cw : BitVec 64)
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iw)))
    (hev : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 136])) =
      some (.val (.word cw))) :
    cw = if (iw + 136).toNat ≤ n.toNat then 1 else 0 := by
  rw [evalHOLFinite_eq_toExact] at hev
  simp [evalHOLExact, evalListHOLExact, hn, hi, valueIsWord, valueWord, wordOpHOL, wordOp,
    Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, BitVec.le_def] at hev
  by_cases hle : (iw + 136).toNat ≤ n.toNat
  · have hnl : ¬ (n.toNat < (iw + 136).toNat) := by omega
    simp [hle, hnl] at hev ⊢; exact hev.symm
  · have hl : n.toNat < (iw + 136).toNat := by omega
    simp [hle, hl] at hev ⊢; exact hev.symm

private theorem call0_ne_break_continue {F : Type} (s : PanSemStateFiniteExact 64 F)
    (fname : MlS) (args : List (ExpHOL 64)) :
    (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).1 ≠ some .break ∧
    (evaluateHOLFiniteState s (.call (some (none, none)) fname args)).1 ≠ some .continue := by
  rw [evaluateHOLFiniteState_call]
  rcases evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vals
  · simp
  · dsimp only
    rcases lookupCodeHOLFinite s.code.lookup fname vals with _ | ⟨b, c, r⟩
    · simp
    · dsimp only
      by_cases hclk : s.clock = 0
      · simp [hclk]
      · rw [if_neg hclk]
        rcases evaluateHOLFiniteState (callEntryStateHOLFinite s c) b with ⟨rb, pb⟩
        cases rb with
        | none => simp
        | some rb' =>
          cases rb' <;> dsimp only
          all_goals try (split <;> simp)
          all_goals simp

private theorem keccak_main_loop_eff {F : Type}
    (k : Nat) (s : PanSemStateFiniteExact 64 F) (stp p n iw : BitVec 64)
    (hk : s.clock ≤ k) (hc : s.code = originalRuntimeCode) (hG : GuestInv s)
    (hstp : s.locals.lookup (ofString "stp") = some (.val (.word stp)))
    (hp : s.locals.lookup (ofString "p") = some (.val (.word p)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iw)))
    (hle : iw.toNat ≤ n.toNat)
    (hnt : (evaluateHOLFiniteState s
      (.while (.cmp .notLower (.var .local (ofString "n"))
          (.op .add [.var .local (ofString "i"), .const 136]))
        (.seq (.call (some (none, none)) (ofString "keccak_absorb_block")
            [.var .local (ofString "stp"), .op .add [.var .local (ofString "p"), .var .local (ofString "i")]])
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 136]))))).1 ≠ some .timeOut)
    (hor : (evaluateHOLFiniteState s
      (.while (.cmp .notLower (.var .local (ofString "n"))
          (.op .add [.var .local (ofString "i"), .const 136]))
        (.seq (.call (some (none, none)) (ofString "keccak_absorb_block")
            [.var .local (ofString "stp"), .op .add [.var .local (ofString "p"), .var .local (ofString "i")]])
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 136]))))).1 = none ∨
      Resumes (evaluateHOLFiniteState s
        (.while (.cmp .notLower (.var .local (ofString "n"))
            (.op .add [.var .local (ofString "i"), .const 136]))
          (.seq (.call (some (none, none)) (ofString "keccak_absorb_block")
              [.var .local (ofString "stp"), .op .add [.var .local (ofString "p"), .var .local (ofString "i")]])
            (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 136]))))).1) :
    let out := evaluateHOLFiniteState s
      (.while (.cmp .notLower (.var .local (ofString "n"))
          (.op .add [.var .local (ofString "i"), .const 136]))
        (.seq (.call (some (none, none)) (ofString "keccak_absorb_block")
            [.var .local (ofString "stp"), .op .add [.var .local (ofString "p"), .var .local (ofString "i")]])
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 136]))))
    ByteEff s out.2 [(stp.toNat, 200)] ∧
    (out.1 = none →
      (∀ v, v ≠ ofString "i" → out.2.locals.lookup v = s.locals.lookup v) ∧
      ∃ iw' : BitVec 64,
        out.2.locals.lookup (ofString "i") = some (.val (.word iw')) ∧
        (n - iw').toNat < 136) := by
  induction k generalizing s iw with
  | zero =>
    dsimp only at hnt hor ⊢
    rw [evaluateHOLFiniteState_while_total] at hnt hor ⊢
    rcases hc_ev : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 136])) with _ | cv
    · simp only [hc_ev] at hor ⊢; exact ⟨ByteEff.refl s _, by simp⟩
    · rcases cv with ⟨⟨cw⟩⟩ | _ | _ <;> try (simp only [hc_ev] at hor ⊢; exact ⟨ByteEff.refl s _, by simp⟩)
      simp only [hc_ev] at hnt hor ⊢
      by_cases hnz : cw ≠ 0
      · have hz : s.clock = 0 := by omega
        rw [if_pos hnz, if_pos hz] at hnt
        exact absurd rfl hnt
      · have hcw0 : cw = 0 := Classical.not_not.1 hnz
        subst hcw0
        rw [if_neg (by simp)]
        refine ⟨ByteEff.refl s _, fun _ => ⟨fun _ _ => rfl, iw, hi, ?_⟩⟩
        have hcw_eq := eval_cmp_notLower_i136 s n iw 0 hn hi hc_ev
        have hnlt := n.isLt; have hilt := iw.isLt
        have hsub : (n - iw).toNat = n.toNat - iw.toNat := by rw [BitVec.toNat_sub]; omega
        by_cases hlt136 : (iw + 136).toNat ≤ n.toNat
        · rw [if_pos hlt136] at hcw_eq; cases hcw_eq
        · by_cases hwrap : iw.toNat + 136 < 2 ^ 64
          · have : (iw + 136).toNat = iw.toNat + 136 := BitVec.toNat_add_of_lt hwrap
            omega
          · omega
  | succ k ih =>
    dsimp only at hnt hor ⊢
    rw [evaluateHOLFiniteState_while_total] at hnt hor ⊢
    rcases hc_ev : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 136])) with _ | cv
    · simp only [hc_ev] at hor ⊢; exact ⟨ByteEff.refl s _, by simp⟩
    · rcases cv with ⟨⟨cw⟩⟩ | _ | _ <;> try (simp only [hc_ev] at hor ⊢; exact ⟨ByteEff.refl s _, by simp⟩)
      simp only [hc_ev] at hnt hor ⊢
      by_cases hnz : cw ≠ 0
      · rw [if_pos hnz] at hnt hor ⊢
        by_cases hz : s.clock = 0
        · rw [if_pos hz] at hnt; exact absurd rfl hnt
        · rw [if_neg hz] at hnt hor ⊢
          rw [fixClockHOLFinite_evaluateState] at hnt hor ⊢
          have hik_le : (iw + 136).toNat ≤ n.toNat := by
            have hcw_eq := eval_cmp_notLower_i136 s n iw cw hn hi hc_ev
            by_cases hle' : (iw + 136).toNat ≤ n.toNat
            · exact hle'
            · rw [if_neg hle'] at hcw_eq; exact absurd hcw_eq hnz
          let sd := decClockHOLFinite s
          have hGd : GuestInv sd := guestInv_congr (s := s) rfl rfl rfl rfl hG
          rw [evaluateHOLFiniteState_seq_line780] at hnt hor ⊢
          rcases hcall : evaluateHOLFiniteState (decClockHOLFinite s)
              (.call (some (none, none)) (ofString "keccak_absorb_block")
                [.var .local (ofString "stp"), .op .add [.var .local (ofString "p"), .var .local (ofString "i")]]) with ⟨rc, m1⟩
          have hnt' := hnt; have hor' := hor
          rw [hcall] at hnt' hor'
          have hnt_c : rc ≠ some .timeOut := by
            intro h; subst h; simp at hnt'
          have hnbc := call0_ne_break_continue (decClockHOLFinite s) (ofString "keccak_absorb_block")
            [.var .local (ofString "stp"), .op .add [.var .local (ofString "p"), .var .local (ofString "i")]]
          rw [hcall] at hnbc
          have hor_c : rc = none ∨ Resumes rc := by
            cases rc with
            | none => exact Or.inl rfl
            | some rc' =>
              cases rc' with
              | returned v => exact Or.inr (Or.inl ⟨v, rfl⟩)
              | exception e v =>
                rcases hor' with h | ⟨_, h⟩ | ⟨e', v', h, hne⟩
                · simp at h
                · simp at h
                · simp at h; obtain ⟨rfl, _⟩ := h; exact Or.inr (Or.inr ⟨e, v, rfl, hne⟩)
              | «break» => exact absurd rfl hnbc.1
              | «continue» => exact absurd rfl hnbc.2
              | error | timeOut | finalFfi _ =>
                exfalso; rcases hor' with h | ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
          have hargs_c : evalListHOLFinite sd (h := fun a => Classical.propDecidable (sd.memaddrs a))
              [.var .local (ofString "stp"), .op .add [.var .local (ofString "p"), .var .local (ofString "i")]] =
              some [.val (.word stp), .val (.word (p + iw))] := by
            simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, sd, decClockHOLFinite, hstp, hp, hi,
              valueIsWord, valueWord, wordOpHOL, wordOp]
          have heff_c : ByteEff sd m1 [(stp.toNat, 200)] := by
            have := call0_byteEff funByteEff_keccak_absorb_block sd _ [(stp.toNat, 200)] hc hGd
              (fun vs hvs i hi_in _ => by
                rw [hargs_c] at hvs; injection hvs with hvs; subst hvs
                simp [valWordNat] at hi_in; subst hi_in
                exact ⟨(stp.toNat, 200), List.mem_singleton.2 rfl, le_rfl, le_rfl⟩)
              (by dsimp only [sd]; rw [hcall]; exact hnt_c)
              (by dsimp only [sd]; rw [hcall]; exact hor_c)
            dsimp only [sd] at this; rwa [hcall] at this
          have hclk_c := evaluateHOLFiniteState_clock_le (decClockHOLFinite s)
            (.call (some (none, none)) (ofString "keccak_absorb_block")
              [.var .local (ofString "stp"), .op .add [.var .local (ofString "p"), .var .local (ofString "i")]])
          rw [hcall] at hclk_c
          cases rc with
          | some rc' =>
            cases rc' with
            | «break» => exact absurd rfl hnbc.1
            | «continue» => exact absurd rfl hnbc.2
            | _ => exact ⟨((ByteEff.refl s _).locals_clock _ _).trans heff_c, by simp⟩
          | none =>
            have hloc_m1 : m1.locals = sd.locals := by
              have := call0_any_locals (decClockHOLFinite s) (ofString "keccak_absorb_block")
                [.var .local (ofString "stp"), .op .add [.var .local (ofString "p"), .var .local (ofString "i")]]
                (by rw [hcall])
              rwa [hcall] at this
            dsimp only at hnt' hor' ⊢
            have hi_m1 : m1.locals.lookup (ofString "i") = some (.val (.word iw)) := by rw [hloc_m1]; exact hi
            have hasgn : evaluateHOLFiniteState m1
                (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 136])) =
                (none, setVarHOLFinite (ofString "i") (.val (.word (iw + 136))) m1) := by
              simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hi_m1, wordOpHOL, wordOp,
                valueIsWord, valueWord, lookupKvarHOLExact, isValidValueHOLExact, setKvarHOLFinite,
                shapeOfHOLExact, shapeEqHOL]
            rw [hasgn] at hnt' hor' ⊢
            dsimp only at hnt' hor' ⊢
            let m2 := setVarHOLFinite (ofString "i") (.val (.word (iw + 136))) m1
            have heff_m2 : ByteEff s m2 [(stp.toNat, 200)] :=
              (((ByteEff.refl s _).locals_clock _ _).trans heff_c).locals_clock _ _
            have hGm2 : GuestInv m2 := guestInv_congr heff_m2.code heff_m2.memaddrs heff_m2.shMemaddrs heff_m2.baseAddr hG
            have hm2_other : ∀ v, v ≠ ofString "i" → m2.locals.lookup v = s.locals.lookup v := by
              intro v hv
              have hv' : (ofString "i" == v) = false := beq_eq_false_iff_ne.2 (Ne.symm hv)
              simp only [m2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hv',
                Bool.false_eq_true, ↓reduceIte, hloc_m1]
              rfl
            have hi_m2 : m2.locals.lookup (ofString "i") = some (.val (.word (iw + 136))) := by
              simp [m2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
            have hm2_clk : m2.clock ≤ k := by change m1.clock ≤ k; change m1.clock ≤ s.clock - 1 at hclk_c; omega
            have ih_res := ih m2 (iw + 136) hm2_clk (heff_m2.code.trans hc) hGm2
              (by rw [hm2_other _ (by decide)]; exact hstp)
              (by rw [hm2_other _ (by decide)]; exact hp)
              (by rw [hm2_other _ (by decide)]; exact hn)
              hi_m2 hik_le hnt' hor'
            refine ⟨heff_m2.trans ih_res.1, fun hnone => ?_⟩
            obtain ⟨ho, hr⟩ := ih_res.2 hnone
            exact ⟨fun v hv => (ho v hv).trans (hm2_other v hv), hr⟩
      · have hcw0 : cw = 0 := Classical.not_not.1 hnz
        subst hcw0
        rw [if_neg (by simp)]
        refine ⟨ByteEff.refl s _, fun _ => ⟨fun _ _ => rfl, iw, hi, ?_⟩⟩
        have hcw_eq := eval_cmp_notLower_i136 s n iw 0 hn hi hc_ev
        have hnlt := n.isLt; have hilt := iw.isLt
        have hsub : (n - iw).toNat = n.toNat - iw.toNat := by rw [BitVec.toNat_sub]; omega
        by_cases hlt136 : (iw + 136).toNat ≤ n.toNat
        · rw [if_pos hlt136] at hcw_eq; cases hcw_eq
        · by_cases hwrap : iw.toNat + 136 < 2 ^ 64
          · have : (iw + 136).toNat = iw.toNat + 136 := BitVec.toNat_add_of_lt hwrap
            omega
          · omega

theorem call0_two_word_resumes {F : Type} (s : PanSemStateFiniteExact 64 F)
    (fname p1 p2 : MlS) (body : ProgHOL 64) (a1 a2 : ExpHOL 64) (w1 w2 : BitVec 64)
    (hne : p1 ≠ p2)
    (hc : s.code = originalRuntimeCode)
    (hlook : originalRuntimeCode.lookup fname = some ([(p1, .one), (p2, .one)], body, .one))
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [a1, a2] =
      some [.val (.word w1), .val (.word w2)])
    (hor : (evaluateHOLFiniteState s (.call (some (none, none)) fname [a1, a2])).1 = none ∨
      Resumes (evaluateHOLFiniteState s (.call (some (none, none)) fname [a1, a2])).1) :
    Resumes (evaluateHOLFiniteState
      (callEntryStateHOLFinite s ((HolFiniteMapExact.empty.update (p1, .val (.word w1))).update (p2, .val (.word w2))))
      body).1 := by
  rw [evaluateHOLFiniteState_call, ha] at hor
  dsimp only at hor
  have hl := pan_two_word_lookup s.code.lookup fname p1 p2 body w1 w2 hne (by rw [hc]; exact hlook)
  rw [hl] at hor; dsimp only at hor
  split at hor
  · rcases hor with h | ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
  · rcases hb : evaluateHOLFiniteState
        (callEntryStateHOLFinite s ((HolFiniteMapExact.empty.update (p1, .val (.word w1))).update (p2, .val (.word w2))))
        body with ⟨rb, pb⟩
    rw [hb] at hor ⊢
    cases rb with
    | none => rcases hor with h | ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
    | some rb' =>
      cases rb' with
      | returned rv => exact Or.inl ⟨rv, rfl⟩
      | exception eid ev =>
        rcases hor with h | ⟨_, h⟩ | ⟨e', v', h, hne_t⟩
        · simp at h
        · simp at h
        · simp at h; obtain ⟨rfl, rfl⟩ := h; exact Or.inr ⟨eid, ev, rfl, hne_t⟩
      | _ => rcases hor with h | ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h

private theorem keccak_out_ite_eff {F : Type}
    (s : PanSemStateFiniteExact 64 F) (out stp : BitVec 64) (Rl : List Ivl)
    (hc : s.code = originalRuntimeCode) (hG : GuestInv s)
    (hout : s.locals.lookup (ofString "out") = some (.val (.word out)))
    (hstp : s.locals.lookup (ofString "stp") = some (.val (.word stp)))
    (hout_in : ∀ i ∈ [(out.toNat, 32)], 0 < i.2 → ∃ j ∈ Rl, j.1 ≤ i.1 ∧ i.1 + i.2 ≤ j.1 + j.2)
    (hnt : (evaluateHOLFiniteState s
      (.ite (.cmp .equal (.op .and [.var .local (ofString "out"), .const 7]) (.const 0))
        (.seq (.store (.var .local (ofString "out")) (.load .one (.var .local (ofString "stp"))))
          (.seq (.store (.op .add [.var .local (ofString "out"), .const 8])
              (.load .one (.op .add [.var .local (ofString "stp"), .const 8])))
            (.seq (.store (.op .add [.var .local (ofString "out"), .const 16])
                (.load .one (.op .add [.var .local (ofString "stp"), .const 16])))
              (.store (.op .add [.var .local (ofString "out"), .const 24])
                (.load .one (.op .add [.var .local (ofString "stp"), .const 24]))))))
        (.call (some (none, none)) (ofString "memcpy")
          [.var .local (ofString "out"), .var .local (ofString "stp"), .const 32]))).1 ≠ some .timeOut)
    (hor : (evaluateHOLFiniteState s
      (.ite (.cmp .equal (.op .and [.var .local (ofString "out"), .const 7]) (.const 0))
        (.seq (.store (.var .local (ofString "out")) (.load .one (.var .local (ofString "stp"))))
          (.seq (.store (.op .add [.var .local (ofString "out"), .const 8])
              (.load .one (.op .add [.var .local (ofString "stp"), .const 8])))
            (.seq (.store (.op .add [.var .local (ofString "out"), .const 16])
                (.load .one (.op .add [.var .local (ofString "stp"), .const 16])))
              (.store (.op .add [.var .local (ofString "out"), .const 24])
                (.load .one (.op .add [.var .local (ofString "stp"), .const 24]))))))
        (.call (some (none, none)) (ofString "memcpy")
          [.var .local (ofString "out"), .var .local (ofString "stp"), .const 32]))).1 = none ∨
      Resumes (evaluateHOLFiniteState s
        (.ite (.cmp .equal (.op .and [.var .local (ofString "out"), .const 7]) (.const 0))
          (.seq (.store (.var .local (ofString "out")) (.load .one (.var .local (ofString "stp"))))
            (.seq (.store (.op .add [.var .local (ofString "out"), .const 8])
                (.load .one (.op .add [.var .local (ofString "stp"), .const 8])))
              (.seq (.store (.op .add [.var .local (ofString "out"), .const 16])
                  (.load .one (.op .add [.var .local (ofString "stp"), .const 16])))
                (.store (.op .add [.var .local (ofString "out"), .const 24])
                  (.load .one (.op .add [.var .local (ofString "stp"), .const 24]))))))
          (.call (some (none, none)) (ofString "memcpy")
            [.var .local (ofString "out"), .var .local (ofString "stp"), .const 32]))).1) :
    ByteEff s (evaluateHOLFiniteState s
      (.ite (.cmp .equal (.op .and [.var .local (ofString "out"), .const 7]) (.const 0))
        (.seq (.store (.var .local (ofString "out")) (.load .one (.var .local (ofString "stp"))))
          (.seq (.store (.op .add [.var .local (ofString "out"), .const 8])
              (.load .one (.op .add [.var .local (ofString "stp"), .const 8])))
            (.seq (.store (.op .add [.var .local (ofString "out"), .const 16])
                (.load .one (.op .add [.var .local (ofString "stp"), .const 16])))
              (.store (.op .add [.var .local (ofString "out"), .const 24])
                (.load .one (.op .add [.var .local (ofString "stp"), .const 24]))))))
        (.call (some (none, none)) (ofString "memcpy")
          [.var .local (ofString "out"), .var .local (ofString "stp"), .const 32]))).2 Rl := by
  rw [evaluateHOLFiniteState_ite] at hnt hor ⊢
  rcases hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .equal (.op .and [.var .local (ofString "out"), .const 7]) (.const 0)) with _ | cv
  · exact ByteEff.refl s Rl
  · rcases cv with ⟨⟨cw⟩⟩ | _ | _ <;> try exact ByteEff.refl s Rl
    have hnt' := hnt; have hor' := hor
    rw [hev] at hnt' hor'
    dsimp only at hnt' hor' ⊢
    by_cases h0 : cw = 0
    · rw [if_pos h0] at hnt' hor' ⊢
      have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
          [.var .local (ofString "out"), .var .local (ofString "stp"), .const 32] =
          some [.val (.word out), .val (.word stp), .val (.word 32)] := by
        simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hout, hstp]
      exact call0_byteEff funByteEff_memcpy s _ Rl hc hG
        (fun vs hvs i hi hp => by
          rw [hargs] at hvs; injection hvs with hvs; subst hvs
          simp [valWordNat] at hi; subst hi
          exact hout_in (out.toNat, 32) (List.mem_singleton.2 rfl) hp)
        hnt' hor'
    · rw [if_neg h0]
      exact (checkWordStoresLocal_sound (ofString "out") 32 (by omega) [] _ rfl s out hc hG hout
        (fun _ h => by simp at h)).1.mono hout_in

theorem funByteEff_keccak256 :
    FunByteEff (ofString "keccak256")
      (fun vals G =>
        [globBufIvl G "keccak_st" 200, globBufIvl G "keccak_pad" 136,
         (valWordNat (vals[2]?.getD (.rStruct [])), 32)]) := by
  have hlook : originalRuntimeCode.lookup (ofString "keccak256") =
      some ([(ofString "p", .one), (ofString "n", .one), (ofString "out", .one)],
        sourceFnBody Guest.Software.guestFn_keccak256, .one) :=
    lookup_of_guestAst_getElem 103 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_keccak256) rfl
  have hlook_mz : originalRuntimeCode.lookup (ofString "memzero") =
      some ([(ofString "dst", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_memzero, .one) := lookup_memzero
  refine ⟨_, _, _, hlook, fun {F} entry vals hc hG hl hnt hres => ?_⟩
  obtain ⟨p, n, out, rfl, hp0, hn0, hout0⟩ :=
    lookupCode_three_words (by decide) (by decide) (by decide) hlook hl
  let Rl := [globBufIvl entry.globals "keccak_st" 200,
    globBufIvl entry.globals "keccak_pad" 136, (out.toNat, 32)]
  change ByteEff entry (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_keccak256)).2 Rl
  have h264 : heapEnd < 2 ^ 64 := by rw [heapEnd_val]; decide
  have seq_step : ∀ (t : PanSemStateFiniteExact 64 F) (a b : ProgHOL 64),
      (evaluateHOLFiniteState t (.seq a b)).1 ≠ some .timeOut →
      ((evaluateHOLFiniteState t (.seq a b)).1 = none ∨ Resumes (evaluateHOLFiniteState t (.seq a b)).1) →
      (evaluateHOLFiniteState t a).1 ≠ some .timeOut ∧
      ((evaluateHOLFiniteState t a).1 = none ∨ Resumes (evaluateHOLFiniteState t a).1) := by
    intro t a b h1 h2
    rw [evaluateHOLFiniteState_seq_line780] at h1 h2
    rcases ha : evaluateHOLFiniteState t a with ⟨ra, ma⟩
    rw [ha] at h1 h2
    refine ⟨fun h => by subst h; simp at h1, ?_⟩
    cases ra with
    | none => exact Or.inl rfl
    | some _ =>
      right
      rcases h2 with h | h
      · simp at h
      · exact h
  -- Unfold outer `dec "stp"`
  have hbody : sourceFnBody Guest.Software.guestFn_keccak256 =
      .dec (ofString "stp") .one (.var .global (ofString "keccak_st"))
        (.seq (.call (some (none, none)) (ofString "memzero") [.var .local (ofString "stp"), .const 200])
          (.dec (ofString "i") .one (.const 0)
            (.seq (.while (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 136]))
                (.seq (.call (some (none, none)) (ofString "keccak_absorb_block")
                    [.var .local (ofString "stp"), .op .add [.var .local (ofString "p"), .var .local (ofString "i")]])
                  (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 136]))))
              (.dec (ofString "rem") .one (.op .sub [.var .local (ofString "n"), .var .local (ofString "i")])
                (.seq (.call (some (none, none)) (ofString "memzero") [.var .global (ofString "keccak_pad"), .const 136])
                  (.seq (.call (some (none, none)) (ofString "memcpy")
                      [.var .global (ofString "keccak_pad"),
                       .op .add [.var .local (ofString "p"), .var .local (ofString "i")],
                       .var .local (ofString "rem")])
                    (.seq (.storeByte (.op .add [.var .global (ofString "keccak_pad"), .var .local (ofString "rem")]) (.const 1))
                      (.seq (.storeByte (.op .add [.var .global (ofString "keccak_pad"), .const 135])
                          (.op .or [.loadByte (.op .add [.var .global (ofString "keccak_pad"), .const 135]), .const 128]))
                        (.seq (.call (some (none, none)) (ofString "keccak_absorb_block")
                            [.var .local (ofString "stp"), .var .global (ofString "keccak_pad")])
                          (.seq (.ite (.cmp .equal (.op .and [.var .local (ofString "out"), .const 7]) (.const 0))
                              (.seq (.store (.var .local (ofString "out")) (.load .one (.var .local (ofString "stp"))))
                                (.seq (.store (.op .add [.var .local (ofString "out"), .const 8])
                                    (.load .one (.op .add [.var .local (ofString "stp"), .const 8])))
                                  (.seq (.store (.op .add [.var .local (ofString "out"), .const 16])
                                      (.load .one (.op .add [.var .local (ofString "stp"), .const 16])))
                                    (.store (.op .add [.var .local (ofString "out"), .const 24])
                                      (.load .one (.op .add [.var .local (ofString "stp"), .const 24]))))))
                              (.call (some (none, none)) (ofString "memcpy")
                                [.var .local (ofString "out"), .var .local (ofString "stp"), .const 32]))
                            (.return (.const 0)))))))))))) := rfl
  rw [hbody] at hnt hres ⊢
  rw [evaluateHOLFiniteState_dec_total] at hnt hres ⊢
  dsimp only at hnt hres ⊢
  rcases hgst : entry.globals.lookup (ofString "keccak_st") with _ | vst
  · simp only [evalHOLExact, hgst]; exact ByteEff.refl entry Rl
  · rcases vst with ⟨⟨stp⟩⟩ | _ | _ <;>
      try (simp only [evalHOLExact, hgst, shapeOfHOLExact, shapeEqHOL, ↓reduceIte] at hres ⊢
           exact ByteEff.refl entry Rl)
    simp only [evalHOLExact, hgst, shapeOfHOLExact, shapeEqHOL, ↓reduceIte] at hnt hres ⊢
    have hsb_pos : 0 < sourceBase := by rw [sourceBase_val]; decide
    let s0 := setVarHOLFinite (ofString "stp") (.val (.word stp)) entry
    have hGs0 : GuestInv s0 := guestInv_setVar _ _ entry hG
    have hstp_0 : s0.locals.lookup (ofString "stp") = some (.val (.word stp)) := by
      simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hp_0 : s0.locals.lookup (ofString "p") = some (.val (.word p)) := by
      simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hp0, show ofString "stp" ≠ ofString "p" by decide]
    have hn_0 : s0.locals.lookup (ofString "n") = some (.val (.word n)) := by
      simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn0, show ofString "stp" ≠ ofString "n" by decide]
    have hout_0 : s0.locals.lookup (ofString "out") = some (.val (.word out)) := by
      simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hout0, show ofString "stp" ≠ ofString "out" by decide]
    -- Step 1: `memzero(stp, 200)`
    obtain ⟨hnt1, hor1⟩ := seq_step s0 _ _ hnt (Or.inr hres)
    have hargs1 : evalListHOLFinite s0 (h := fun a => Classical.propDecidable (s0.memaddrs a))
        [.var .local (ofString "stp"), .const 200] = some [.val (.word stp), .val (.word 200)] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hstp_0]
    have hres_mz1 := call0_two_word_resumes s0 _ _ _ _ _ _ stp 200 (by decide) hc hlook_mz hargs1 hor1
    let c0 := callEntryStateHOLFinite s0
      ((HolFiniteMapExact.empty.update (ofString "dst", .val (.word stp))).update (ofString "n", .val (.word 200)))
    have hstp_dom := (memzero_body_eff c0 stp 200 hc (guestInv_callEntry s0 _ hGs0)
      (by simp [c0, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "n" ≠ ofString "dst" by decide])
      (by simp [c0, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
      hres_mz1).2 (by decide)
    have hstp_nz : stp.toNat ≠ 0 := by omega
    have hstp_sub : ∀ i ∈ [(stp.toNat, 200)], 0 < i.2 → ∃ j ∈ Rl, j.1 ≤ i.1 ∧ i.1 + i.2 ≤ j.1 + j.2 := by
      intro i hi _
      simp at hi; subst hi
      refine ⟨globBufIvl entry.globals "keccak_st" 200, List.mem_cons_self, ?_, ?_⟩ <;>
        simp [globBufIvl, globMapN, hgst, hstp_nz]
    rw [evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
    rcases hm1 : evaluateHOLFiniteState s0
        (.call (some (none, none)) (ofString "memzero") [.var .local (ofString "stp"), .const 200]) with ⟨r1, s1⟩
    rw [hm1] at hnt hres
    have heff1 : ByteEff s0 s1 Rl := by
      have := call0_byteEff funByteEff_memzero s0 _ Rl hc hGs0
        (fun vs hvs i hi hp => by
          rw [hargs1] at hvs; injection hvs with hvs; subst hvs
          simp [valWordNat] at hi; subst hi
          exact hstp_sub (stp.toNat, 200) (List.mem_singleton.2 rfl) hp)
        hnt1 hor1
      rwa [hm1] at this
    have heff_e1 : ByteEff entry s1 Rl := ((ByteEff.refl entry Rl).locals_clock _ _).trans heff1
    cases r1 with
    | some _ => exact heff_e1.locals_clock _ _
    | none =>
      have hs1_loc : s1.locals = s0.locals := by
        have := call0_any_locals s0 _ _ (by rw [hm1])
        rwa [hm1] at this
      have hGs1 : GuestInv s1 := guestInv_congr heff_e1.code heff_e1.memaddrs heff_e1.shMemaddrs heff_e1.baseAddr hG
      have hc_s1 : s1.code = originalRuntimeCode := heff_e1.code.trans hc
      -- Step 2: `dec "i" 0`
      dsimp only at hnt hres ⊢
      rw [evaluateHOLFiniteState_dec_total] at hnt hres ⊢
      simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, ↓reduceIte] at hnt hres ⊢
      let s2 := setVarHOLFinite (ofString "i") (.val (.word 0)) s1
      have hGs2 : GuestInv s2 := guestInv_setVar _ _ s1 hGs1
      have hstp_2 : s2.locals.lookup (ofString "stp") = some (.val (.word stp)) := by
        simp only [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "i" ≠ ofString "stp" by decide, ↓reduceIte, hs1_loc]; exact hstp_0
      have hp_2 : s2.locals.lookup (ofString "p") = some (.val (.word p)) := by
        simp only [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "i" ≠ ofString "p" by decide, ↓reduceIte, hs1_loc]; exact hp_0
      have hn_2 : s2.locals.lookup (ofString "n") = some (.val (.word n)) := by
        simp only [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "i" ≠ ofString "n" by decide, ↓reduceIte, hs1_loc]; exact hn_0
      have hout_2 : s2.locals.lookup (ofString "out") = some (.val (.word out)) := by
        simp only [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "i" ≠ ofString "out" by decide, ↓reduceIte, hs1_loc]; exact hout_0
      have hi_2 : s2.locals.lookup (ofString "i") = some (.val (.word 0)) := by
        simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      -- Step 3: `while (n >=u i + 136)`
      obtain ⟨hnt_w, hor_w⟩ := seq_step s2 _ _ hnt (Or.inr hres)
      have hw_eff := keccak_main_loop_eff s2.clock s2 stp p n 0 le_rfl hc_s1 hGs2
        hstp_2 hp_2 hn_2 hi_2 (Nat.zero_le _) hnt_w hor_w
      rw [evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
      rcases hw : evaluateHOLFiniteState s2 _ with ⟨rw_res, s3⟩
      rw [hw] at hnt hres hw_eff
      have heff_e3 : ByteEff entry s3 Rl :=
        (heff_e1.locals_clock _ _).trans (hw_eff.1.mono hstp_sub)
      cases rw_res with
      | some _ => exact (heff_e3.locals_clock _ _).locals_clock _ _
      | none =>
        obtain ⟨hs3_other, iw, hi_3, hrem_lt⟩ := hw_eff.2 rfl
        have hGs3 : GuestInv s3 := guestInv_congr heff_e3.code heff_e3.memaddrs heff_e3.shMemaddrs heff_e3.baseAddr hG
        have hc_s3 : s3.code = originalRuntimeCode := heff_e3.code.trans hc
        have hglob_s3 : s3.globals = entry.globals := heff_e3.globals
        have hstp_3 : s3.locals.lookup (ofString "stp") = some (.val (.word stp)) := by
          rw [hs3_other _ (by decide)]; exact hstp_2
        have hp_3 : s3.locals.lookup (ofString "p") = some (.val (.word p)) := by
          rw [hs3_other _ (by decide)]; exact hp_2
        have hn_3 : s3.locals.lookup (ofString "n") = some (.val (.word n)) := by
          rw [hs3_other _ (by decide)]; exact hn_2
        have hout_3 : s3.locals.lookup (ofString "out") = some (.val (.word out)) := by
          rw [hs3_other _ (by decide)]; exact hout_2
        -- Step 4: `dec "rem" (n - i)`
        dsimp only at hnt hres ⊢
        rw [evaluateHOLFiniteState_dec_total] at hnt hres ⊢
        have hi_3' : s3.locals.lookup (ofString "i") = some (.val (.word iw)) := hi_3
        have hev_rem : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
            (.op .sub [.var .local (ofString "n"), .var .local (ofString "i")]) = some (.val (.word (n - iw))) := by
          simp [evalHOLExact, evalListHOLExact, hn_3, hi_3', valueIsWord, valueWord, wordOpHOL, wordOp]
        simp only [hev_rem, shapeOfHOLExact, shapeEqHOL, ↓reduceIte] at hnt hres ⊢
        let remw := n - iw
        let s4 := setVarHOLFinite (ofString "rem") (.val (.word remw)) s3
        have hGs4 : GuestInv s4 := guestInv_setVar _ _ s3 hGs3
        have hstp_4 : s4.locals.lookup (ofString "stp") = some (.val (.word stp)) := by
          simp only [s4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "rem" ≠ ofString "stp" by decide, ↓reduceIte]; exact hstp_3
        have hp_4 : s4.locals.lookup (ofString "p") = some (.val (.word p)) := by
          simp only [s4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "rem" ≠ ofString "p" by decide, ↓reduceIte]; exact hp_3
        have hi_4 : s4.locals.lookup (ofString "i") = some (.val (.word iw)) := by
          simp only [s4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "rem" ≠ ofString "i" by decide, ↓reduceIte]; exact hi_3'
        have hout_4 : s4.locals.lookup (ofString "out") = some (.val (.word out)) := by
          simp only [s4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "rem" ≠ ofString "out" by decide, ↓reduceIte]; exact hout_3
        have hrem_4 : s4.locals.lookup (ofString "rem") = some (.val (.word remw)) := by
          simp [s4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        -- Step 5: `memzero(keccak_pad, 136)`
        obtain ⟨hnt_p1, hor_p1⟩ := seq_step s4 _ _ hnt (Or.inr hres)
        have hnot_err : ∀ r, r = some .error → ¬ (r = none ∨ Resumes r) := by
          rintro _ rfl (h | ⟨_, h⟩ | ⟨_, _, h, _⟩) <;> cases h
        rcases hgpad : entry.globals.lookup (ofString "keccak_pad") with _ | vpad
        · exfalso
          apply hnot_err _ _ hor_p1
          rw [evaluateHOLFiniteState_call]
          have hgpad4 : s4.globals.lookup (ofString "keccak_pad") = none := by
            change s3.globals.lookup _ = none; rw [hglob_s3]; exact hgpad
          simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hgpad4]
        · have hpad_w : ∃ pad : BitVec 64, vpad = .val (.word pad) := by
            by_cases hsh1 : shapeEqHOL .one (shapeOfHOLExact vpad) = true
            · cases vpad with
              | val wlab =>
                cases wlab with
                | word pad => exact ⟨pad, rfl⟩
              | rStruct _ => simp [shapeOfHOLExact, shapeEqHOL] at hsh1
              | nStruct _ _ => simp [shapeOfHOLExact, shapeEqHOL] at hsh1
            · exfalso
              apply hnot_err _ _ hor_p1
              rw [evaluateHOLFiniteState_call]
              have hgpad4 : s4.globals.lookup (ofString "keccak_pad") = some vpad := by
                change s3.globals.lookup _ = _; rw [hglob_s3]; exact hgpad
              have hargs_bad : evalListHOLFinite s4 (h := fun a => Classical.propDecidable (s4.memaddrs a))
                  [.var .global (ofString "keccak_pad"), .const 136] =
                  some [vpad, .val (.word 136)] := by
                simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hgpad4]
              rw [hargs_bad]; dsimp only
              have hl_bad : lookupCodeHOLFinite s4.code.lookup (ofString "memzero") [vpad, .val (.word 136)] = none := by
                apply Option.eq_none_iff_forall_not_mem.2
                intro ⟨b, c, r⟩ hmem
                have hx := lookupCodeHOLFinite_eq_some s4.code.lookup _ _ b c r hmem
                have hc4 : s4.code = originalRuntimeCode := hc_s3
                rw [hc4] at hx
                simp [lookupCodeHOLExact, hlook_mz] at hx
                exact hsh1 hx.1.2.1
              rw [hl_bad]
          obtain ⟨pad, rfl⟩ := hpad_w
          have hgpad4 : s4.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)) := by
            change s3.globals.lookup _ = _; rw [hglob_s3]; exact hgpad
          have hargs_p1 : evalListHOLFinite s4 (h := fun a => Classical.propDecidable (s4.memaddrs a))
              [.var .global (ofString "keccak_pad"), .const 136] = some [.val (.word pad), .val (.word 136)] := by
            simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hgpad4]
          have hres_p1 := call0_two_word_resumes s4 _ _ _ _ _ _ pad 136 (by decide) hc_s3 hlook_mz hargs_p1 hor_p1
          let cp1 := callEntryStateHOLFinite s4
            ((HolFiniteMapExact.empty.update (ofString "dst", .val (.word pad))).update (ofString "n", .val (.word 136)))
          have hpad_dom := (memzero_body_eff cp1 pad 136 hc_s3 (guestInv_callEntry s4 _ hGs4)
            (by simp [cp1, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "n" ≠ ofString "dst" by decide])
            (by simp [cp1, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
            hres_p1).2 (by decide)
          have hpad_nz : pad.toNat ≠ 0 := by omega
          have hpad_sub : ∀ i ∈ [(pad.toNat, 136)], 0 < i.2 → ∃ j ∈ Rl, j.1 ≤ i.1 ∧ i.1 + i.2 ≤ j.1 + j.2 := by
            intro i hi _
            simp at hi; subst hi
            refine ⟨globBufIvl entry.globals "keccak_pad" 136, List.mem_cons_of_mem _ List.mem_cons_self, ?_, ?_⟩ <;>
              simp [globBufIvl, globMapN, hgpad, hpad_nz]
          have hpad_in : 0 < 136 → ∃ i ∈ Rl, i.1 ≤ pad.toNat ∧ pad.toNat + 136 ≤ i.1 + i.2 :=
            fun hp => hpad_sub (pad.toNat, 136) (List.mem_singleton.2 rfl) hp
          rw [evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
          rcases hmp1 : evaluateHOLFiniteState s4
              (.call (some (none, none)) (ofString "memzero") [.var .global (ofString "keccak_pad"), .const 136]) with ⟨rp1, s5⟩
          rw [hmp1] at hnt hres
          have heff_p1 : ByteEff s4 s5 Rl := by
            have := call0_byteEff funByteEff_memzero s4 _ Rl hc_s3 hGs4
              (fun vs hvs i hi hp => by
                rw [hargs_p1] at hvs; injection hvs with hvs; subst hvs
                simp [valWordNat] at hi; subst hi
                exact hpad_sub (pad.toNat, 136) (List.mem_singleton.2 rfl) hp)
              hnt_p1 hor_p1
            rwa [hmp1] at this
          have heff_e5 : ByteEff entry s5 Rl := (heff_e3.locals_clock _ _).trans heff_p1
          cases rp1 with
          | some _ => exact ((heff_e5.locals_clock _ _).locals_clock _ _).locals_clock _ _
          | none =>
            have hs5_loc : s5.locals = s4.locals := by
              have := call0_any_locals s4 _ _ (by rw [hmp1]); rwa [hmp1] at this
            have hGs5 : GuestInv s5 := guestInv_congr heff_e5.code heff_e5.memaddrs heff_e5.shMemaddrs heff_e5.baseAddr hG
            have hc_s5 : s5.code = originalRuntimeCode := heff_e5.code.trans hc
            have hgpad5 : s5.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)) := by
              rw [heff_e5.globals]; exact hgpad
            -- Step 6: `memcpy(keccak_pad, p + i, rem)`
            dsimp only at hnt hres ⊢
            obtain ⟨hnt_mc, hor_mc⟩ := seq_step s5 _ _ hnt (Or.inr hres)
            have hargs_mc : evalListHOLFinite s5 (h := fun a => Classical.propDecidable (s5.memaddrs a))
                [.var .global (ofString "keccak_pad"), .op .add [.var .local (ofString "p"), .var .local (ofString "i")],
                 .var .local (ofString "rem")] =
                some [.val (.word pad), .val (.word (p + iw)), .val (.word remw)] := by
              simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hgpad5, hs5_loc, hp_4, hi_4, hrem_4,
                valueIsWord, valueWord, wordOpHOL, wordOp]
            rw [evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
            rcases hmc : evaluateHOLFiniteState s5
                (.call (some (none, none)) (ofString "memcpy")
                  [.var .global (ofString "keccak_pad"), .op .add [.var .local (ofString "p"), .var .local (ofString "i")],
                   .var .local (ofString "rem")]) with ⟨rmc, s6⟩
            rw [hmc] at hnt hres
            have heff_mc : ByteEff s5 s6 Rl := by
              have := call0_byteEff funByteEff_memcpy s5 _ Rl hc_s5 hGs5
                (fun vs hvs i hi hp => by
                  rw [hargs_mc] at hvs; injection hvs with hvs; subst hvs
                  simp [valWordNat] at hi; subst hi
                  refine ⟨globBufIvl entry.globals "keccak_pad" 136, List.mem_cons_of_mem _ List.mem_cons_self, ?_, ?_⟩
                  · simp [globBufIvl, globMapN, hgpad, hpad_nz]
                  · simp only [globBufIvl, globMapN, hgpad, hpad_nz, ↓reduceIte]
                    change pad.toNat + (n - iw).toNat ≤ pad.toNat + 136; omega)
                hnt_mc hor_mc
              rwa [hmc] at this
            have heff_e6 : ByteEff entry s6 Rl := heff_e5.trans heff_mc
            cases rmc with
            | some _ => exact ((heff_e6.locals_clock _ _).locals_clock _ _).locals_clock _ _
            | none =>
              have hs6_loc : s6.locals = s4.locals := by
                have := call0_any_locals s5 _ _ (by rw [hmc]); rw [hmc] at this; exact this.trans hs5_loc
              have hGs6 : GuestInv s6 := guestInv_congr heff_e6.code heff_e6.memaddrs heff_e6.shMemaddrs heff_e6.baseAddr hG
              have hgpad6 : s6.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)) := by
                rw [heff_e6.globals]; exact hgpad
              -- Step 7: `storeByte(keccak_pad + rem, 1)`
              dsimp only at hnt hres ⊢
              rw [evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
              have hev_sb1 : @evalHOLExact 64 F _ s6.toExact (fun a => Classical.propDecidable (s6.memaddrs a))
                  (.op .add [.var .global (ofString "keccak_pad"), .var .local (ofString "rem")]) =
                  some (.val (.word (pad + BitVec.ofNat 64 remw.toNat))) := by
                simp [evalHOLExact, evalListHOLExact, hgpad6, hs6_loc, hrem_4, valueIsWord, valueWord, wordOpHOL, wordOp]
              have heff_sb1 : ByteEff s6 (evaluateHOLFiniteState s6
                  (.storeByte (.op .add [.var .global (ofString "keccak_pad"), .var .local (ofString "rem")]) (.const 1))).2 Rl :=
                byteEff_storeByte_at hGs6 _ _ pad remw.toNat 136 hpad_dom.2 hpad_in hrem_lt hev_sb1
              rcases hsb1 : evaluateHOLFiniteState s6
                  (.storeByte (.op .add [.var .global (ofString "keccak_pad"), .var .local (ofString "rem")]) (.const 1)) with ⟨rsb1, s7⟩
              rw [hsb1] at hnt hres heff_sb1
              have heff_e7 : ByteEff entry s7 Rl := heff_e6.trans heff_sb1
              cases rsb1 with
              | some _ => exact ((heff_e7.locals_clock _ _).locals_clock _ _).locals_clock _ _
              | none =>
                have hs7_loc : s7.locals = s4.locals := by
                  have := (evaluate_storeByte_control_frame s6
                    (.op .add [.var .global (ofString "keccak_pad"), .var .local (ofString "rem")]) (.const 1)).2.2.1
                  rw [hsb1] at this; exact this.trans hs6_loc
                have hGs7 : GuestInv s7 := guestInv_congr heff_e7.code heff_e7.memaddrs heff_e7.shMemaddrs heff_e7.baseAddr hG
                have hgpad7 : s7.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)) := by
                  rw [heff_e7.globals]; exact hgpad
                -- Step 8: `storeByte(keccak_pad + 135, ...)`
                dsimp only at hnt hres ⊢
                rw [evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
                have hev_sb2 : @evalHOLExact 64 F _ s7.toExact (fun a => Classical.propDecidable (s7.memaddrs a))
                    (.op .add [.var .global (ofString "keccak_pad"), .const 135]) =
                    some (.val (.word (pad + 135))) := by
                  simp [evalHOLExact, evalListHOLExact, hgpad7, valueIsWord, valueWord, wordOpHOL, wordOp]
                have heff_sb2 : ByteEff s7 (evaluateHOLFiniteState s7
                    (.storeByte (.op .add [.var .global (ofString "keccak_pad"), .const 135])
                      (.op .or [.loadByte (.op .add [.var .global (ofString "keccak_pad"), .const 135]), .const 128]))).2 Rl :=
                  byteEff_storeByte_at hGs7 _ _ pad 135 136 hpad_dom.2 hpad_in (by decide) hev_sb2
                rcases hsb2 : evaluateHOLFiniteState s7
                    (.storeByte (.op .add [.var .global (ofString "keccak_pad"), .const 135])
                      (.op .or [.loadByte (.op .add [.var .global (ofString "keccak_pad"), .const 135]), .const 128])) with ⟨rsb2, s8⟩
                rw [hsb2] at hnt hres heff_sb2
                have heff_e8 : ByteEff entry s8 Rl := heff_e7.trans heff_sb2
                cases rsb2 with
                | some _ => exact ((heff_e8.locals_clock _ _).locals_clock _ _).locals_clock _ _
                | none =>
                  have hs8_loc : s8.locals = s4.locals := by
                    have := (evaluate_storeByte_control_frame s7
                      (.op .add [.var .global (ofString "keccak_pad"), .const 135])
                      (.op .or [.loadByte (.op .add [.var .global (ofString "keccak_pad"), .const 135]), .const 128])).2.2.1
                    rw [hsb2] at this; exact this.trans hs7_loc
                  have hGs8 : GuestInv s8 := guestInv_congr heff_e8.code heff_e8.memaddrs heff_e8.shMemaddrs heff_e8.baseAddr hG
                  have hc_s8 : s8.code = originalRuntimeCode := heff_e8.code.trans hc
                  have hgpad8 : s8.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)) := by
                    rw [heff_e8.globals]; exact hgpad
                  -- Step 9: `keccak_absorb_block(stp, keccak_pad)`
                  dsimp only at hnt hres ⊢
                  obtain ⟨hnt_ab, hor_ab⟩ := seq_step s8 _ _ hnt (Or.inr hres)
                  have hargs_ab : evalListHOLFinite s8 (h := fun a => Classical.propDecidable (s8.memaddrs a))
                      [.var .local (ofString "stp"), .var .global (ofString "keccak_pad")] =
                      some [.val (.word stp), .val (.word pad)] := by
                    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hs8_loc, hstp_4, hgpad8]
                  rw [evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
                  rcases hab : evaluateHOLFiniteState s8
                      (.call (some (none, none)) (ofString "keccak_absorb_block")
                        [.var .local (ofString "stp"), .var .global (ofString "keccak_pad")]) with ⟨rab, s9⟩
                  rw [hab] at hnt hres
                  have heff_ab : ByteEff s8 s9 Rl := by
                    have := call0_byteEff funByteEff_keccak_absorb_block s8 _ Rl hc_s8 hGs8
                      (fun vs hvs i hi hp => by
                        rw [hargs_ab] at hvs; injection hvs with hvs; subst hvs
                        simp [valWordNat] at hi; subst hi
                        exact hstp_sub (stp.toNat, 200) (List.mem_singleton.2 rfl) hp)
                      hnt_ab hor_ab
                    rwa [hab] at this
                  have heff_e9 : ByteEff entry s9 Rl := heff_e8.trans heff_ab
                  cases rab with
                  | some _ => exact ((heff_e9.locals_clock _ _).locals_clock _ _).locals_clock _ _
                  | none =>
                    have hs9_loc : s9.locals = s4.locals := by
                      have := call0_any_locals s8 _ _ (by rw [hab]); rw [hab] at this; exact this.trans hs8_loc
                    have hGs9 : GuestInv s9 := guestInv_congr heff_e9.code heff_e9.memaddrs heff_e9.shMemaddrs heff_e9.baseAddr hG
                    have hc_s9 : s9.code = originalRuntimeCode := heff_e9.code.trans hc
                    -- Step 10: `ite` output 32 bytes to `out`, then `return 0`!
                    dsimp only at hnt hres ⊢
                    obtain ⟨hnt_oi, hor_oi⟩ := seq_step s9 _ _ hnt (Or.inr hres)
                    have hout_sub : ∀ i ∈ [(out.toNat, 32)], 0 < i.2 → ∃ j ∈ Rl, j.1 ≤ i.1 ∧ i.1 + i.2 ≤ j.1 + j.2 := by
                      intro i hi _
                      simp at hi; subst hi
                      exact ⟨(out.toNat, 32), List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), le_rfl, le_rfl⟩
                    have heff_oi := keccak_out_ite_eff s9 out stp Rl hc_s9 hGs9
                      (by rw [hs9_loc]; exact hout_4) (by rw [hs9_loc]; exact hstp_4)
                      hout_sub hnt_oi hor_oi
                    rw [evaluateHOLFiniteState_seq_line780] at ⊢
                    rcases hoi : evaluateHOLFiniteState s9 _ with ⟨roi, s10⟩
                    rw [hoi] at heff_oi
                    have heff_e10 : ByteEff entry s10 Rl := heff_e9.trans heff_oi
                    cases roi with
                    | some _ => exact ((heff_e10.locals_clock _ _).locals_clock _ _).locals_clock _ _
                    | none =>
                      exact (((heff_e10.trans (byteEff_return s10 _ Rl)).locals_clock _ _).locals_clock _ _).locals_clock _ _

end InitECandidate.Solver.Wave8GuestInv.R13Shards.Keccak256

namespace InitECandidate.Solver.Wave8GuestInv.R13Shards

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

theorem wk_keccak256_impl :
    WorldKeeps WorldOK
      (fun s => [(locN s "out", 32),
        (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
        (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)])
      []
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "keccak256") := by
  obtain ⟨params, body, retShape, hlook, hspec⟩ := Keccak256.funByteEff_keccak256
  refine ⟨params, body, retShape, hlook, fun {F} s hcode hWOK ⟨vals, hl⟩ hnt hres => ?_⟩
  have heff := hspec s vals hcode hWOK.1.1 hl hnt hres
  have hlook_eq : originalRuntimeCode.lookup (ofString "keccak256") =
      some ([(ofString "p", .one), (ofString "n", .one), (ofString "out", .one)],
        sourceFnBody Guest.Software.guestFn_keccak256, .one) :=
    lookup_of_guestAst_getElem 103 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_keccak256) rfl
  have hinj := Option.some.inj (hlook.symm.trans hlook_eq)
  obtain ⟨hp_eq, hb_eq⟩ := Prod.mk.inj hinj
  obtain ⟨hbody_eq, hret_eq⟩ := Prod.mk.inj hb_eq
  subst hp_eq hbody_eq hret_eq
  obtain ⟨pw, nw, outw, rfl, _, _, hout_lk⟩ :=
    R13Shards.Keccak256.lookupCode_three_words (by decide) (by decide) (by decide) hlook_eq hl
  have hout_eq : R13Shards.Keccak256.valWordNat
      (([.val (.word pw), .val (.word nw), .val (.word outw)] : List (ValueHOL 64))[2]?.getD (.rStruct [])) =
      locN s "out" := by
    simp [R13Shards.Keccak256.valWordNat, locN, hout_lk]
  let Rk : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl :=
    fun t => [(locN t "out", 32),
      (globN t "keccak_pad", if globN t "keccak_pad" = 0 then 0 else 136),
      (globN t "keccak_st", if globN t "keccak_st" = 0 then 0 else 200)]
  have hbre : M13.ByteRegionEffect s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_keccak256)).2
      (Rk s ++ ([] : List Ivl)) := by
    simp only [List.append_nil]
    have hmem_Rl : ∀ iv ∈
        [R13Shards.Keccak256.globBufIvl s.globals "keccak_st" 200,
         R13Shards.Keccak256.globBufIvl s.globals "keccak_pad" 136,
         (locN s "out", 32)], iv ∈ Rk s := by
      intro iv hiv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hiv
      rcases hiv with rfl | rfl | rfl
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
      · exact List.mem_cons_of_mem _ List.mem_cons_self
      · exact List.mem_cons_self
    dsimp only at heff
    rw [hout_eq] at heff
    refine ⟨heff.code, heff.memaddrs, heff.shMemaddrs, heff.baseAddr, heff.be, heff.globals, ?_, ?_, ?_⟩
    · intro a hna
      by_contra hne
      exact hna (heff.out_dom a hne)
    · intro a hno
      by_contra hne
      obtain ⟨iv, hiv, _, hch⟩ := heff.cell_frame a hne
      exact hno iv (hmem_Rl iv hiv) hch
    · intro b hb hno
      by_contra hne
      obtain ⟨iv, hiv, hin⟩ := heff.byte_frame b hb hne
      exact hno iv (hmem_Rl iv hiv) hin
  exact M13.ByteRegionEffect.to_worldStep (R := Rk) (extra := fun {F} _ => [])
    (r := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_keccak256)).1)
    hWOK (fun _ hx => by cases hx) hbre

end InitECandidate.Solver.Wave8GuestInv.R13Shards
