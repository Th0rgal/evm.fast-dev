import InitECandidate.Solver.Wave8GuestInv.LeafStatements
import InitECandidate.Solver.GuestUniformClockBound

/-! Core `fb_*` combinators and base leaves for `PrimShardP10P30` on R11 (`GuestInv`). -/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.GuestUniformClockBound
open InitECandidate.Solver.UniformSourceClock

theorem nat_max_eq (a b : Nat) : Nat.max a b = max a b := rfl

theorem fbOn_of_funBounded {f : MlS} {k K : Nat} (h : FunBounded f k) (hle : k ≤ K) :
    TerminatingFunBoundedOn GuestInv f K :=
  (TerminatingFunBoundedOn.of_unconditional (terminatingFunBounded_of_funBounded h)).weaken hle

theorem TerminatingProgBoundedOn.weaken' {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {prog : ProgHOL 64} {K K' : Nat} (h : TerminatingProgBoundedOn P prog K) (hle : K ≤ K') :
    TerminatingProgBoundedOn P prog K' :=
  fun s hc hP => (h s hc hP).weaken hle

theorem straightOn {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} (prog : ProgHOL 64)
    (hs : extStraightLine prog = true) : TerminatingProgBoundedOn P prog 0 :=
  fun s hc _ => TerminatingProgBounded.straight prog hs s hc

theorem progOn {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} {prog : ProgHOL 64} {K : Nat}
    (h : ProgBounded prog K) : TerminatingProgBoundedOn P prog K :=
  fun s hc _ => terminatingProgBounded_of_progBounded h s hc

theorem dec_guestInv (name : MlS) (shape : ShapeHOL) (init : ExpHOL 64) {body : ProgHOL 64}
    {K : Nat} (hbody : TerminatingProgBoundedOn GuestInv body K) :
    TerminatingProgBoundedOn GuestInv (.dec name shape init body) K :=
  TerminatingProgBoundedOn.dec_on localsFree_guestInv name shape init hbody

theorem call_guestInv' {fname : MlS} {B : Nat} {destination : Option (VarKind × MlS)}
    {arguments : List (ExpHOL 64)} (hf : TerminatingFunBoundedOn GuestInv fname B) :
    TerminatingProgBoundedOn GuestInv (.call (some (destination, none)) fname arguments) (B + 1) :=
  TerminatingProgBoundedOn.call_guestInv hf destination arguments

theorem decCall_guestInv' {fname : MlS} {B Bc : Nat} {name : MlS} {shape : ShapeHOL}
    {arguments : List (ExpHOL 64)} {continuation : ProgHOL 64}
    (hf : TerminatingFunBoundedOn GuestInv fname B)
    (hcont : TerminatingProgBoundedOn GuestInv continuation Bc) :
    TerminatingProgBoundedOn GuestInv (.decCall name shape fname arguments continuation)
      (B + Bc + 1) :=
  TerminatingProgBoundedOn.decCall_guestInv hf name shape arguments hcont

theorem callHandle_guestInv' {fname : MlS} {B Bh : Nat} {destination : Option (VarKind × MlS)}
    {exn var : MlS} {handler : ProgHOL 64} {arguments : List (ExpHOL 64)}
    (hf : TerminatingFunBoundedOn GuestInv fname B)
    (hh : TerminatingProgBoundedOn GuestInv handler Bh) :
    TerminatingProgBoundedOn GuestInv
      (.call (some (destination, some (exn, var, handler))) fname arguments) (B + Bh + 1) :=
  TerminatingProgBoundedOn.callHandle_guestInv hf destination exn var hh arguments

/-! ### Ordinary-domain bounds and `while_walk_cost` -/

theorem addresses_bounds (base : BitVec 64) (n : Nat) (x : BitVec 64)
    (hfit : base.toNat + 8 * n < 2 ^ 64)
    (h : Flapjack.Compiler.Backend.StackRemove.addresses base n x) :
    base.toNat ≤ x.toNat ∧ x.toNat + 8 ≤ base.toNat + 8 * n := by
  induction n generalizing base with
  | zero => exact absurd h id
  | succ n ih =>
    rcases h with h | h
    · subst h; omega
    · have hb : (base + Flapjack.Compiler.Backend.StackRemove.bytesInWord 64).toNat = base.toNat + 8 := by
        rw [BitVec.toNat_add_of_lt] <;>
          simp [Flapjack.Compiler.Backend.StackRemove.bytesInWord] <;> omega
      have := ih (base + Flapjack.Compiler.Backend.StackRemove.bytesInWord 64) (by omega) h
      omega

theorem ordinaryDomain_bounds (x : BitVec 64) (h : ordinaryDomain x) :
    sourceBase ≤ x.toNat ∧ x.toNat + 8 ≤ heapEnd := by
  unfold ordinaryDomain at h
  have hn : ((stackStart - sourceBase) / 8 - globalsWords) = 3888119741 := by decide
  rw [hn] at h
  have hs : (BitVec.ofNat 64 sourceBase).toNat = 2701131776 := by decide
  have := addresses_bounds _ _ x (by rw [hs]; decide) h
  rw [hs] at this
  have e1 : sourceBase = 2701131776 := by decide
  have e2 : heapEnd = 2701131776 + 8 * 3888119741 := by decide
  omega

theorem addresses_aligned (base : BitVec 64) (hb : base.toNat % 8 = 0) (n : Nat) (x : BitVec 64)
    (hfit : base.toNat + 8 * n < 2 ^ 64)
    (h : Flapjack.Compiler.Backend.StackRemove.addresses base n x) :
    x.toNat % 8 = 0 := by
  induction n generalizing base with
  | zero => exact absurd h id
  | succ n ih =>
    rcases h with h | h
    · subst h; exact hb
    · have hstep : (base + Flapjack.Compiler.Backend.StackRemove.bytesInWord 64).toNat = base.toNat + 8 := by
        rw [BitVec.toNat_add_of_lt] <;>
          simp [Flapjack.Compiler.Backend.StackRemove.bytesInWord] <;> omega
      exact ih (base + Flapjack.Compiler.Backend.StackRemove.bytesInWord 64) (by omega) (by omega) h

theorem ordinaryDomain_aligned (x : BitVec 64) (h : ordinaryDomain x) :
    x.toNat % 8 = 0 := by
  unfold ordinaryDomain at h
  have hn : ((stackStart - sourceBase) / 8 - globalsWords) = 3888119741 := by decide
  rw [hn] at h
  have hs : (BitVec.ofNat 64 sourceBase).toNat = 2701131776 := by decide
  have hb : (BitVec.ofNat 64 sourceBase).toNat % 8 = 0 := by decide
  have hfit : (BitVec.ofNat 64 sourceBase).toNat + 8 * 3888119741 < 2 ^ 64 := by decide
  exact addresses_aligned _ hb _ x hfit h

theorem byteAlign_bounds (a : BitVec 64) :
    (panByteAlignHOL (width := 64) a).toNat ≤ a.toNat ∧
      a.toNat < (panByteAlignHOL (width := 64) a).toNat + 8 := by
  have h8 : 2 ^ Nat.log2 (64 / 8) = 8 := by decide
  simp only [panByteAlignHOL, h8, BitVec.toNat_ofNat]
  have ha := a.isLt
  have : a.toNat / 8 * 8 < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt this]
  omega

def walkRank (a : BitVec 64) : Nat := min (heapEnd - a.toNat) (domainBytes + 1)

def walkMu (d i : MlS) : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Nat := fun s =>
  match s.locals.lookup d, s.locals.lookup i with
  | some (.val (.word x)), some (.val (.word y)) => walkRank (x + y)
  | _, _ => 0

theorem walkMu_le (d i : MlS) {F : Type} (s : PanSemStateFiniteExact 64 F) :
    walkMu d i s ≤ domainBytes + 1 := by
  unfold walkMu
  split
  · exact Nat.min_le_right _ _
  · exact Nat.zero_le _

theorem walkRank_step (a stride : BitVec 64) (hs : 0 < stride.toNat) (hs2 : stride.toNat ≤ 256)
    (hlo : sourceBase ≤ a.toNat) (hhi : a.toNat < heapEnd) :
    walkRank (a + stride) < walkRank a := by
  have eH : heapEnd = 2701131776 + 8 * 3888119741 := by decide
  have eS : sourceBase = 2701131776 := by decide
  have eD : domainBytes = heapEnd - sourceBase := rfl
  have hadd : (a + stride).toNat = a.toNat + stride.toNat :=
    BitVec.toNat_add_of_lt (by omega)
  unfold walkRank
  rw [hadd]
  omega

def FirstAccess (d i : MlS) (first : ProgHOL 64) : Prop :=
  ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode → GuestInv s →
    (evaluateHOLFiniteState s first).1 = none →
    ∃ x y : BitVec 64, s.locals.lookup d = some (.val (.word x)) ∧
      s.locals.lookup i = some (.val (.word y)) ∧
      sourceBase ≤ (x + y).toNat ∧ (x + y).toNat < heapEnd

theorem seq_none_first {F : Type} (s : PanSemStateFiniteExact 64 F) (first tail : ProgHOL 64)
    (h : (evaluateHOLFiniteState s (.seq first tail)).1 = none) :
    (evaluateHOLFiniteState s first).1 = none := by
  rw [evaluateHOLFiniteState_seq_line780] at h
  rcases hr : evaluateHOLFiniteState s first with ⟨r, mid⟩
  rw [hr] at h
  cases r with
  | none => rfl
  | some _ => simp at h

theorem firstAccess_seq {d i : MlS} {first : ProgHOL 64} (tail : ProgHOL 64)
    (h : FirstAccess d i first) : FirstAccess d i (.seq first tail) :=
  fun s hc hP hn => h s hc hP (seq_none_first s first tail hn)

theorem while_walk_cost {cond : ExpHOL 64} {body : ProgHOL 64} {d i : MlS} {stride : BitVec 64}
    {B : Nat}
    (hs : 0 < stride.toNat) (hs2 : stride.toNat ≤ 256)
    (hbody : TerminatingProgBoundedOn GuestInv body B)
    (hstep_i : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (y : BitVec 64),
      s.code = originalRuntimeCode →
      s.locals.lookup i = some (.val (.word y)) →
      (evaluateHOLFiniteState s body).1 = none →
      (evaluateHOLFiniteState s body).2.locals.lookup i = some (.val (.word (y + stride))))
    (hd : avoidsLocal d body = true)
    (hfirst : FirstAccess d i body)
    (hnc : noTopContinue body = true) :
    TerminatingProgBoundedOn GuestInv (.while cond body) ((domainBytes + 1 + 1) * (B + 1)) := by
  refine TerminatingProgBoundedOn.while_rank (walkMu d i)
    (fun s hP => guestInv_congr (s := s) rfl rfl rfl rfl hP)
    hbody
    (fun s _ _ _ => walkMu_le d i s)
    ?_
  intro F s hcode hP _ hflow
  have hPd : GuestInv (decClockHOLFinite s) := guestInv_congr (s := s) rfl rfl rfl rfl hP
  have hnc' := evaluate_noTopContinue body hnc (decClockHOLFinite s)
  have hnone : (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none :=
    hflow.resolve_right hnc'
  obtain ⟨x, y, hx, hy, hlo, hhi⟩ := hfirst (decClockHOLFinite s) hcode hPd hnone
  have hip := hstep_i (decClockHOLFinite s) y hcode hy hnone
  have hdk := evaluate_avoidsLocal_flowing d body hd (decClockHOLFinite s) (Or.inl hnone)
  refine ⟨guestInv_evaluate (decClockHOLFinite s) body hPd, ?_⟩
  have hx' : s.locals.lookup d = some (.val (.word x)) := hx
  have hy' : s.locals.lookup i = some (.val (.word y)) := hy
  have hdp : (evaluateHOLFiniteState (decClockHOLFinite s) body).2.locals.lookup d =
      some (.val (.word x)) := hdk.trans hx
  unfold walkMu
  rw [hdp, hip, hx', hy']
  dsimp only
  rw [← BitVec.add_assoc]
  exact walkRank_step _ _ hs hs2 hlo hhi

/-- Any `CountedBody i stride body 0` yields `y + stride` on `none` (since `0 ≤ s.clock`). -/
theorem counted0_step {i : MlS} {stride : BitVec 64} {body : ProgHOL 64}
    (hc : CountedBody i stride body 0) :
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (y : BitVec 64),
      s.code = originalRuntimeCode →
      s.locals.lookup i = some (.val (.word y)) →
      (evaluateHOLFiniteState s body).1 = none →
      (evaluateHOLFiniteState s body).2.locals.lookup i = some (.val (.word (y + stride))) := by
  intro F s y hcode hy hnone
  exact ((hc.run s hcode y hy (Nat.zero_le _)).2.2.2.2 hnone).1

theorem while_walk' {cond : ExpHOL 64} {body : ProgHOL 64} {d i : MlS} {stride : BitVec 64}
    (hcount : CountedBody i stride body 0) (hfirst : FirstAccess d i body)
    (hd : avoidsLocal d body = true) (hstraight : extStraightLine body = true)
    (hnc : noTopContinue body = true) (hs : 0 < stride.toNat) (hs2 : stride.toNat ≤ 256) :
    TerminatingProgBoundedOn GuestInv (.while cond body) ((domainBytes + 1 + 1) * (0 + 1)) :=
  while_walk_cost hs hs2 (straightOn body hstraight) (counted0_step hcount) hd hfirst hnc

theorem eval_add2_word {F : Type} (s : PanSemStateFiniteExact 64 F) [h : DecidablePred s.memaddrs]
    (d i : MlS) (a : BitVec 64)
    (he : @evalHOLExact 64 F _ s.toExact h (.op .add [.var .local d, .var .local i]) =
      some (.val (.word a))) :
    ∃ x y : BitVec 64, s.locals.lookup d = some (.val (.word x)) ∧
      s.locals.lookup i = some (.val (.word y)) ∧ a = x + y := by
  simp only [evalHOLExact, evalListHOLExact] at he
  rcases hd : s.locals.lookup d with _ | vd <;> rcases hi : s.locals.lookup i with _ | vi <;>
    simp only [hd, hi] at he
  · simp at he
  · simp at he
  · simp at he
  · rcases vd with ⟨⟨x⟩⟩ | _ | _ <;> rcases vi with ⟨⟨y⟩⟩ | _ | _ <;>
      simp [valueIsWord] at he
    refine ⟨x, y, rfl, rfl, ?_⟩
    simp [valueWord, wordOpHOL, wordOp] at he
    exact he.symm

theorem eval_load_one {F : Type} (s : PanSemStateFiniteExact 64 F) [h : DecidablePred s.memaddrs]
    (e : ExpHOL 64) (v : ValueHOL 64)
    (he : @evalHOLExact 64 F _ s.toExact h (.load .one e) = some v) :
    ∃ a : BitVec 64, @evalHOLExact 64 F _ s.toExact h e = some (.val (.word a)) ∧ s.memaddrs a ∧
      ∃ w, v = .val w := by
  simp only [evalHOLExact] at he
  split at he
  · split at he
    · rename_i a ha
      simp only [memLoadHOLExact] at he
      split at he
      · rename_i hd
        exact ⟨a, ha, hd, _, (Option.some.inj he).symm⟩
      · simp at he
    · simp at he
  · simp at he

theorem eval_loadByte {F : Type} (s : PanSemStateFiniteExact 64 F) [h : DecidablePred s.memaddrs]
    (e : ExpHOL 64) (v : ValueHOL 64)
    (he : @evalHOLExact 64 F _ s.toExact h (.loadByte e) = some v) :
    ∃ a : BitVec 64, @evalHOLExact 64 F _ s.toExact h e = some (.val (.word a)) ∧
      s.memaddrs (panByteAlignHOL (width := 64) a) := by
  simp only [evalHOLExact] at he
  split at he
  · rename_i a ha
    refine ⟨a, ha, ?_⟩
    by_contra hc
    revert he
    simp only [panMemLoadByteHOL]
    split <;> first | contradiction | simp [hc]
  · simp at he

theorem const_isVal (c : BitVec 64) : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : DecidablePred s.memaddrs) (val : ValueHOL 64),
    @evalHOLExact 64 F _ s.toExact h (.const c) = some val → ∃ w, val = .val w := by
  intro F s h val hv
  simp [evalHOLExact] at hv
  exact ⟨_, hv.symm⟩

theorem load_isVal (e : ExpHOL 64) : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : DecidablePred s.memaddrs) (val : ValueHOL 64),
    @evalHOLExact 64 F _ s.toExact h (.load .one e) = some val → ∃ w, val = .val w := by
  intro F s h val hv
  obtain ⟨_, _, _, w, hw⟩ := eval_load_one s (h := h) e val hv
  exact ⟨w, hw⟩

theorem firstAccess_store (d i : MlS) (v : ExpHOL 64)
    (hv : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (h : DecidablePred s.memaddrs)
      (val : ValueHOL 64), @evalHOLExact 64 F _ s.toExact h v = some val → ∃ w, val = .val w) :
    FirstAccess d i (.store (.op .add [.var .local d, .var .local i]) v) := by
  intro F s _ hP h
  rw [evaluateHOLFiniteState_store] at h
  split at h
  · rename_i address hdst
    obtain ⟨x, y, hx, hy, rfl⟩ := eval_add2_word s (h := fun a => Classical.propDecidable (s.memaddrs a)) d i address hdst
    refine ⟨x, y, hx, hy, ?_⟩
    split at h
    · rename_i val hval
      obtain ⟨w, rfl⟩ := hv s _ val hval
      split at h
      · rename_i mem hmem
        have hdom : s.memaddrs (x + y) := by
          simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL] at hmem
          by_contra hc
          simp [hc] at hmem
        rw [hP.memaddrs] at hdom
        have := ordinaryDomain_bounds _ hdom
        omega
      · simp at h
    · simp at h
  · simp at h

theorem firstAccess_storeByte (d i : MlS) (v : ExpHOL 64) :
    FirstAccess d i (.storeByte (.op .add [.var .local d, .var .local i]) v) := by
  intro F s _ hP h
  rw [evaluateHOLFiniteState_storeByte] at h
  split at h
  · rename_i address hdst
    obtain ⟨x, y, hx, hy, rfl⟩ := eval_add2_word s (h := fun a => Classical.propDecidable (s.memaddrs a)) d i address hdst
    refine ⟨x, y, hx, hy, ?_⟩
    split at h
    · split at h
      · rename_i mem hmem
        have hdom : s.memaddrs (panByteAlignHOL (width := 64) (x + y)) := by
          by_contra hc
          revert hmem
          simp only [panMemStoreByteWord8HOL]
          split <;> first | contradiction | simp [hc] | (split <;> first | contradiction | simp [hc])
        rw [hP.memaddrs] at hdom
        have := ordinaryDomain_bounds _ hdom
        have := byteAlign_bounds (x + y)
        omega
      · simp at h
    · simp at h
  · simp at h

theorem eval_cmp_left {F : Type} (s : PanSemStateFiniteExact 64 F) [h : DecidablePred s.memaddrs]
    (c : Cmp) (l r : ExpHOL 64) (v : ValueHOL 64)
    (he : @evalHOLExact 64 F _ s.toExact h (.cmp c l r) = some v) :
    ∃ vl, @evalHOLExact 64 F _ s.toExact h l = some vl := by
  simp only [evalHOLExact] at he
  split at he
  · rename_i _ _ w _ hl _
    exact ⟨_, hl⟩
  · simp at he

theorem ite_cond_some {F : Type} (s : PanSemStateFiniteExact 64 F) (cond : ExpHOL 64)
    (yes no : ProgHOL 64) (h : (evaluateHOLFiniteState s (.ite cond yes no)).1 = none) :
    ∃ v, @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) cond = some v := by
  rw [evaluateHOLFiniteState_ite] at h
  split at h
  · exact ⟨_, by assumption⟩
  · simp at h

theorem firstAccess_ite_load (d i : MlS) (c : Cmp) (r : ExpHOL 64) (yes no : ProgHOL 64) :
    FirstAccess d i (.ite (.cmp c (.load .one (.op .add [.var .local d, .var .local i])) r) yes no) := by
  intro F s _ hP h
  obtain ⟨v, hv⟩ := ite_cond_some s _ yes no h
  obtain ⟨vl, hl⟩ := eval_cmp_left s (h := fun a => Classical.propDecidable (s.memaddrs a)) c _ r v hv
  obtain ⟨a, ha, hdom, _⟩ := eval_load_one s (h := fun a => Classical.propDecidable (s.memaddrs a)) _ vl hl
  obtain ⟨x, y, hx, hy, rfl⟩ := eval_add2_word s (h := fun a => Classical.propDecidable (s.memaddrs a)) d i a ha
  refine ⟨x, y, hx, hy, ?_⟩
  rw [hP.memaddrs] at hdom
  have := ordinaryDomain_bounds _ hdom
  omega

theorem firstAccess_ite_loadByte (d i : MlS) (c : Cmp) (r : ExpHOL 64) (yes no : ProgHOL 64) :
    FirstAccess d i (.ite (.cmp c (.loadByte (.op .add [.var .local d, .var .local i])) r) yes no) := by
  intro F s _ hP h
  obtain ⟨v, hv⟩ := ite_cond_some s _ yes no h
  obtain ⟨vl, hl⟩ := eval_cmp_left s (h := fun a => Classical.propDecidable (s.memaddrs a)) c _ r v hv
  obtain ⟨a, ha, hdom⟩ := eval_loadByte s (h := fun a => Classical.propDecidable (s.memaddrs a)) _ vl hl
  obtain ⟨x, y, hx, hy, rfl⟩ := eval_add2_word s (h := fun a => Classical.propDecidable (s.memaddrs a)) d i a ha
  refine ⟨x, y, hx, hy, ?_⟩
  rw [hP.memaddrs] at hdom
  have := ordinaryDomain_bounds _ hdom
  have := byteAlign_bounds (x + y)
  omega

theorem firstAccess_dec_loadByte (d i : MlS) (name : MlS) (shape : ShapeHOL) (body : ProgHOL 64) :
    FirstAccess d i (.dec name shape (.loadByte (.op .add [.var .local d, .var .local i])) body) := by
  intro F s _ hP h
  rw [evaluateHOLFiniteState_dec_total] at h
  dsimp only at h
  split at h
  · simp at h
  · rename_i v hv
    obtain ⟨a, ha, hdom⟩ := eval_loadByte s (h := fun a => Classical.propDecidable (s.memaddrs a)) _ v hv
    obtain ⟨x, y, hx, hy, rfl⟩ := eval_add2_word s (h := fun a => Classical.propDecidable (s.memaddrs a)) d i a ha
    refine ⟨x, y, hx, hy, ?_⟩
    rw [hP.memaddrs] at hdom
    have := ordinaryDomain_bounds _ hdom
    have := byteAlign_bounds (x + y)
    omega

theorem firstAccess_assign_or_loadByte (d i : MlS) (v : MlS) (lhs : ExpHOL 64) :
    FirstAccess d i (.assign .local v (.op .or [lhs, .loadByte (.op .add [.var .local d, .var .local i])])) := by
  intro F s _ hP h
  rw [evaluateHOLFiniteState_assign] at h
  split at h
  · simp at h
  · rename_i val hv
    rcases hr : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.loadByte (.op .add [.var .local d, .var .local i])) with _ | vr
    · rcases hl : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) lhs with _ | vl
      · simp [evalHOLExact, evalListHOLExact] at hl hv
        rw [hl] at hv; simp at hv
      · simp [evalHOLExact, evalListHOLExact] at hl hr hv
        rw [hl, hr] at hv; simp at hv
    · obtain ⟨a, ha, hdom⟩ := eval_loadByte s (h := fun a => Classical.propDecidable (s.memaddrs a)) _ vr hr
      obtain ⟨x, y, hx, hy, rfl⟩ := eval_add2_word s (h := fun a => Classical.propDecidable (s.memaddrs a)) d i a ha
      refine ⟨x, y, hx, hy, ?_⟩
      rw [hP.memaddrs] at hdom
      have := ordinaryDomain_bounds _ hdom
      have := byteAlign_bounds (x + y)
      omega

theorem firstAccess_dec_xor_loadByte (d i : MlS) (name : MlS) (shape : ShapeHOL)
    (rhs : ExpHOL 64) (body : ProgHOL 64) :
    FirstAccess d i (.dec name shape (.op .xor [.loadByte (.op .add [.var .local d, .var .local i]), rhs]) body) := by
  intro F s _ hP h
  rw [evaluateHOLFiniteState_dec_total] at h
  dsimp only at h
  split at h
  · simp at h
  · rename_i val hv
    rcases hl : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.loadByte (.op .add [.var .local d, .var .local i])) with _ | vl
    · simp [evalHOLExact, evalListHOLExact] at hl hv
      rw [hl] at hv; simp at hv
    · obtain ⟨a, ha, hdom⟩ := eval_loadByte s (h := fun a => Classical.propDecidable (s.memaddrs a)) _ vl hl
      obtain ⟨x, y, hx, hy, rfl⟩ := eval_add2_word s (h := fun a => Classical.propDecidable (s.memaddrs a)) d i a ha
      refine ⟨x, y, hx, hy, ?_⟩
      rw [hP.memaddrs] at hdom
      have := ordinaryDomain_bounds _ hdom
      have := byteAlign_bounds (x + y)
      omega

theorem countedBody_seq_straight {counter : MlS} {step : BitVec 64}
    (first : ProgHOL 64) {tail : ProgHOL 64} {cost : Nat}
    (hs : extStraightLine first = true) (ha : avoidsLocal counter first = true)
    (hn : noTopContinue first = true) (hrest : CountedBody counter step tail cost) :
    CountedBody counter step (.seq first tail) cost := by
  simpa using CountedBody.seq first (ProgBounded.straight first hs) ha hn hrest

theorem countedBody_seq' {counter : MlS} {step : BitVec 64} {first tail : ProgHOL 64} {cost : Nat}
    (hrest : CountedBody counter step tail cost) (hs : extStraightLine first = true)
    (ha : avoidsLocal counter first = true) (hn : noTopContinue first = true) :
    CountedBody counter step (.seq first tail) cost :=
  countedBody_seq_straight first hs ha hn hrest

theorem countedBody_dec' {counter : MlS} {step : BitVec 64} {name : MlS} {shape : ShapeHOL}
    {initializer : ExpHOL 64} {body : ProgHOL 64} {cost : Nat}
    (rest : CountedBody counter step body cost) (distinct : counter ≠ name) :
    CountedBody counter step (.dec name shape initializer body) cost :=
  CountedBody.dec name shape initializer distinct rest

/-! ### Strict local unsigned counter `while i < n` -/

def ctrMu (i n : MlS) : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Nat := fun s =>
  match s.locals.lookup i, s.locals.lookup n with
  | some (.val (.word y)), some (.val (.word m)) => m.toNat - y.toNat
  | _, _ => 0

theorem ctrMu_le (i n : MlS) {F : Type} (s : PanSemStateFiniteExact 64 F) :
    ctrMu i n s ≤ 2 ^ 64 := by
  unfold ctrMu
  split
  · rename_i y m _ _
    have := m.isLt
    omega
  · exact Nat.zero_le _

theorem eval_lower_locals {F : Type} (s : PanSemStateFiniteExact 64 F) [h : DecidablePred s.memaddrs]
    (i n : MlS) (w : BitVec 64)
    (he : @evalHOLExact 64 F _ s.toExact h (.cmp .lower (.var .local i) (.var .local n)) =
      some (.val (.word w))) (hw : w ≠ 0) :
    ∃ y m : BitVec 64, s.locals.lookup i = some (.val (.word y)) ∧
      s.locals.lookup n = some (.val (.word m)) ∧ y.toNat < m.toNat := by
  simp only [evalHOLExact] at he
  rcases hi : s.locals.lookup i with _ | vi <;> rcases hn : s.locals.lookup n with _ | vn <;>
    simp only [hi, hn] at he
  · simp at he
  · simp at he
  · simp at he
  · rcases vi with ⟨⟨y⟩⟩ | _ | _ <;> rcases vn with ⟨⟨m⟩⟩ | _ | _ <;> simp at he
    refine ⟨y, m, rfl, rfl, ?_⟩
    simp only [Compiler.Encoders.Asm.wordCmpHOL] at he
    by_contra hc
    have : ¬ (y < m) := by rw [BitVec.lt_def]; omega
    simp [this] at he
    exact hw he.symm

theorem while_ctr {i n : MlS} {body : ProgHOL 64}
    (hcount : CountedBody i 1 body 0) (hn : avoidsLocal n body = true)
    (hstraight : extStraightLine body = true) (hnc : noTopContinue body = true) :
    TerminatingProgBoundedOn GuestInv (.while (.cmp .lower (.var .local i) (.var .local n)) body)
      ((2 ^ 64 + 1) * (0 + 1)) := by
  refine TerminatingProgBoundedOn.while_rank (ctrMu i n)
    (fun s hP => guestInv_congr (s := s) rfl rfl rfl rfl hP)
    (straightOn body hstraight)
    (fun s _ _ _ => ctrMu_le i n s)
    ?_
  intro F s hcode hP hact hflow
  obtain ⟨w, hw, hnz⟩ := hact
  rw [evalHOLFinite_eq_toExact] at hw
  obtain ⟨y, m, hy, hm, hlt⟩ := eval_lower_locals s
    (h := fun a => Classical.propDecidable (s.memaddrs a)) i n w hw hnz
  have hnone : (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none :=
    hflow.resolve_right (evaluate_noTopContinue body hnc (decClockHOLFinite s))
  have hip := counted0_step hcount (decClockHOLFinite s) y hcode hy hnone
  have hnk := evaluate_avoidsLocal_flowing n body hn (decClockHOLFinite s) (Or.inl hnone)
  refine ⟨guestInv_evaluate (decClockHOLFinite s) body (guestInv_congr (s := s) rfl rfl rfl rfl hP), ?_⟩
  have hmp : (evaluateHOLFiniteState (decClockHOLFinite s) body).2.locals.lookup n =
      some (.val (.word m)) := hnk.trans hm
  unfold ctrMu
  rw [hip, hmp, hy, hm]
  dsimp only
  have hadd : (y + 1).toNat = y.toNat + 1 := by
    rw [BitVec.toNat_add_of_lt] <;> simp <;> omega
  omega

attribute [local irreducible] TerminatingProgBoundedOn in
theorem while_ctr_expr {i : MlS} {lim : ExpHOL 64} {body : ProgHOL 64} {B : Nat}
    (hbody : TerminatingProgBoundedOn GuestInv body B)
    (hstep_i : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (y : BitVec 64),
      s.code = originalRuntimeCode →
      s.locals.lookup i = some (.val (.word y)) →
      (evaluateHOLFiniteState s body).1 = none →
      (evaluateHOLFiniteState s body).2.locals.lookup i = some (.val (.word (y + 1))))
    (hlim : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      (evaluateHOLFiniteState s body).1 = none →
      @evalHOLExact 64 F _ (evaluateHOLFiniteState s body).2.toExact
        (fun a => Classical.propDecidable ((evaluateHOLFiniteState s body).2.memaddrs a)) lim =
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) lim)
    (hnc : noTopContinue body = true) :
    TerminatingProgBoundedOn GuestInv (.while (.cmp .lower (.var .local i) lim) body)
      ((2 ^ 64 + 1) * (B + 1)) := by
  let mu : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Nat := fun s =>
    match s.locals.lookup i,
      @evalHOLExact 64 _ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) lim with
    | some (.val (.word y)), some (.val (.word m)) => m.toNat - y.toNat
    | _, _ => 0
  refine TerminatingProgBoundedOn.while_rank (P := GuestInv) (N := 2 ^ 64)
    (condition := .cmp .lower (.var .local i) lim) mu
    (fun s hP => guestInv_congr (s := s) rfl rfl rfl rfl hP)
    hbody
    (fun s _ _ _ => by
      dsimp only [mu]; split
      · rename_i y m _ _; have := m.isLt; omega
      · exact Nat.zero_le _)
    ?_
  intro F s hcode hP hact hflow
  obtain ⟨w, hw, hnz⟩ := hact
  rw [evalHOLFinite_eq_toExact] at hw
  simp only [evalHOLExact] at hw
  rcases hi : s.locals.lookup i with _ | vi
  · simp [hi] at hw
  · rcases hm : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) lim with _ | vm
    · simp [hi, hm] at hw
    · simp only [hi, hm] at hw
      rcases vi with ⟨⟨y⟩⟩ | _ | _ <;> rcases vm with ⟨⟨m⟩⟩ | _ | _ <;> try (simp at hw; done)
      have hlt : y.toNat < m.toNat := by
        simp only [Compiler.Encoders.Asm.wordCmpHOL] at hw
        by_contra hc
        have : ¬ (y < m) := by rw [BitVec.lt_def]; omega
        simp [this] at hw
        exact hnz hw.symm
      have hnone : (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none :=
        hflow.resolve_right (evaluate_noTopContinue body hnc (decClockHOLFinite s))
      have hip := hstep_i (decClockHOLFinite s) y hcode hi hnone
      have hmp := hlim (decClockHOLFinite s) hnone
      have hmd : @evalHOLExact 64 F _ (decClockHOLFinite s).toExact
          (fun a => Classical.propDecidable ((decClockHOLFinite s).memaddrs a)) lim =
          some (.val (.word m)) := by
        rw [← evalHOLFinite_eq_toExact]
        have hu := @evalHOLFinite_upd_clock_eq 64 F _ s
          (fun a => Classical.propDecidable (s.memaddrs a)) (s.clock - 1) lim
        exact hu.trans (by rw [evalHOLFinite_eq_toExact]; exact hm)
      rw [hmd] at hmp
      refine ⟨guestInv_evaluate (decClockHOLFinite s) body (guestInv_congr (s := s) rfl rfl rfl rfl hP), ?_⟩
      dsimp only [mu]
      rw [hip, hmp, hi, hm]
      dsimp only
      have hadd : (y + 1).toNat = y.toNat + 1 := by
        rw [BitVec.toNat_add_of_lt] <;> simp <;> omega
      omega

/-! ### Tactics -/

syntax "counted_auto" : tactic
macro_rules
  | `(tactic| counted_auto) => `(tactic| first
      | exact CountedBody.incr
      | (apply countedBody_seq'
         · counted_auto
         · rfl
         · rfl
         · rfl)
      | (apply countedBody_dec'
         · counted_auto
         · decide))

syntax "access_auto" : tactic
macro_rules
  | `(tactic| access_auto) => `(tactic| first
      | exact firstAccess_store _ _ _ (const_isVal _)
      | exact firstAccess_store _ _ _ (load_isVal _)
      | exact firstAccess_storeByte _ _ _
      | exact firstAccess_ite_load _ _ _ _ _ _
      | exact firstAccess_ite_loadByte _ _ _ _ _ _
      | exact firstAccess_dec_loadByte _ _ _ _ _
      | exact firstAccess_assign_or_loadByte _ _ _ _
      | exact firstAccess_dec_xor_loadByte _ _ _ _ _ _
      | (apply firstAccess_seq; access_auto))

open Lean Elab Tactic Meta in
elab "callee_fb" : tactic => withMainContext do
  let g ← instantiateMVars (← getMainTarget)
  unless g.isAppOfArity ``TerminatingFunBoundedOn 3 do throwError "callee_fb: bad goal"
  let fn := g.getAppArgs[1]!
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let t ← whnfR (← instantiateMVars d.type)
    if t.isAppOfArity ``TerminatingFunBoundedOn 3 && t.getAppArgs[1]! == fn then
      if ← isDefEq t g then
        (← getMainGoal).assign d.toExpr
        replaceMainGoal []
        return
  let some e := fn.find? (fun e => e.isAppOfArity ``Flapjack.Basis.Pure.MlString.ofString 1 &&
      e.appArg!.isStringLit) | throwError "callee_fb: no function name"
  let .lit (.strVal name) := e.appArg! | throwError "callee_fb: not literal"
  let full := Name.mkStr `InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30 ("fb_" ++ name)
  unless (← getEnv).contains full do throwError "callee_fb: {full} not proved yet"
  evalTactic (← `(tactic| exact $(mkIdent full):ident))

syntax "fb_auto" : tactic
macro_rules
  | `(tactic| fb_auto) => `(tactic| first
      | exact straightOn _ rfl
      | (apply TerminatingProgBoundedOn.seq_guestInv
         · fb_auto
         · fb_auto)
      | (apply TerminatingProgBoundedOn.ite_on
         · fb_auto
         · fb_auto)
      | (apply dec_guestInv; fb_auto)
      | (apply call_guestInv'; callee_fb)
      | (apply decCall_guestInv'
         · callee_fb
         · fb_auto)
      | (apply callHandle_guestInv'
         · callee_fb
         · fb_auto)
      | (apply while_walk'
         · counted_auto
         · access_auto
         · rfl
         · rfl
         · rfl
         · decide
         · decide)
      | (apply while_ctr
         · counted_auto
         · rfl
         · rfl
         · rfl))

syntax "fb_unfold " num ident : tactic
macro_rules
  | `(tactic| fb_unfold $idx $fn) => `(tactic|
      (refine ⟨_, _, _, lookup_of_guestAst_getElem $idx (by rw [guestAst_len]; decide)
          (extractFn $fn) rfl, ?_⟩
       dsimp only [extractFn, $fn:ident,
         InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
         InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
         InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
         InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
         InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural,
         List.map, Option.map]))

open Lean Elab Tactic Meta in
elab "generalize_K" : tactic => do
  let t ← instantiateMVars (← (← getMainGoal).getType)
  let cs := t.foldConsts #[] fun c acc =>
    if c.getPrefix == `InitECandidate.Solver.Wave8GuestInv.K && !acc.contains c then acc.push c else acc
  let mut i := 0
  for c in cs do
    i := i + 1
    let x := mkIdent (Name.mkSimple s!"kg{i}")
    evalTactic (← `(tactic| generalize ($(mkIdent c) : Nat) = $x))

syntax "fb_arith " ident : tactic
macro_rules
  | `(tactic| fb_arith $k) => `(tactic|
      (have hD : domainBytes + 1 + 1 ≤ 2 ^ 64 + 1 := by rw [domainBytes_eq]; decide
       unfold $k:ident
       generalize_K
       generalize domainBytes = D at hD ⊢
       generalize (2 : Nat) ^ 64 = T at hD ⊢
       try simp only [Nat.max_def, max_def]
       (try split_ifs) <;> omega))

syntax "fb_prove " num ident ident : tactic
macro_rules
  | `(tactic| fb_prove $idx $fn $k) => `(tactic|
      (fb_unfold $idx $fn
       apply TerminatingProgBoundedOn.weaken'
       · fb_auto
       · fb_arith $k))

/-! ### Base unguarded leaves -/

theorem fb_trap_with : TerminatingFunBoundedOn GuestInv (ofString "trap_with") K.«trap_with» :=
  fbOn_of_funBounded funBounded_trap_with (by decide)

theorem fb_alloc : TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc» :=
  fbOn_of_funBounded funBounded_alloc (by decide)

theorem fb_heap_mark : TerminatingFunBoundedOn GuestInv (ofString "heap_mark") K.«heap_mark» :=
  fbOn_of_funBounded funBounded_heap_mark (by decide)

theorem fb_heap_release : TerminatingFunBoundedOn GuestInv (ofString "heap_release") K.«heap_release» :=
  fbOn_of_funBounded funBounded_heap_release (by decide)

theorem fb_scratch_alloc : TerminatingFunBoundedOn GuestInv (ofString "scratch_alloc") K.«scratch_alloc» :=
  fbOn_of_funBounded funBounded_scratch_alloc (by decide)

theorem fb_scratch_mark : TerminatingFunBoundedOn GuestInv (ofString "scratch_mark") K.«scratch_mark» :=
  fbOn_of_funBounded funBounded_scratch_mark (by decide)

theorem fb_scratch_release : TerminatingFunBoundedOn GuestInv (ofString "scratch_release") K.«scratch_release» :=
  fbOn_of_funBounded funBounded_scratch_release (by decide)

theorem fb_keccak_f1600 : TerminatingFunBoundedOn GuestInv (ofString "keccak_f1600") K.«keccak_f1600» :=
  fbOn_of_funBounded funBounded_keccak_f1600 (by decide)

theorem fb_keccak_absorb_block :
    TerminatingFunBoundedOn GuestInv (ofString "keccak_absorb_block") K.«keccak_absorb_block» :=
  fbOn_of_funBounded funBounded_keccak_absorb_block (by decide)

theorem fb_rlp_fail : TerminatingFunBoundedOn GuestInv (ofString "rlp_fail") K.«rlp_fail» := by
  fb_prove 105 Guest.Software.guestFn_rlp_fail K.«rlp_fail»

theorem fb_mpt_fail : TerminatingFunBoundedOn GuestInv (ofString "mpt_fail") K.«mpt_fail» := by
  fb_prove 246 Guest.Software.guestFn_mpt_fail K.«mpt_fail»

theorem fb_memzero : TerminatingFunBoundedOn GuestInv (ofString "memzero") K.«memzero» := by
  fb_prove 17 Guest.Software.guestFn_memzero K.«memzero»

theorem fb_memcpy : TerminatingFunBoundedOn GuestInv (ofString "memcpy") K.«memcpy» := by
  fb_prove 16 Guest.Software.guestFn_memcpy K.«memcpy»

theorem fb_memeq : TerminatingFunBoundedOn GuestInv (ofString "memeq") K.«memeq» := by
  fb_prove 18 Guest.Software.guestFn_memeq K.«memeq»

theorem fb_key_to_nibbles : TerminatingFunBoundedOn GuestInv (ofString "key_to_nibbles") K.«key_to_nibbles» := by
  fb_prove 248 Guest.Software.guestFn_key_to_nibbles K.«key_to_nibbles»

theorem fb_rlp_read_length :
    TerminatingFunBoundedOn GuestInv (ofString "rlp_read_length") K.«rlp_read_length» := by
  fb_prove 106 Guest.Software.guestFn_rlp_read_length K.«rlp_read_length»

theorem fb_rlp_item_header :
    TerminatingFunBoundedOn GuestInv (ofString "rlp_item_header") K.«rlp_item_header» := by
  fb_prove 109 Guest.Software.guestFn_rlp_item_header K.«rlp_item_header»

theorem fb_rlp_item_total_unchecked :
    TerminatingFunBoundedOn GuestInv (ofString "rlp_item_total_unchecked") K.«rlp_item_total_unchecked» := by
  fb_prove 114 Guest.Software.guestFn_rlp_item_total_unchecked K.«rlp_item_total_unchecked»

theorem fb_charge_gas : TerminatingFunBoundedOn GuestInv (ofString "charge_gas") K.«charge_gas» := by
  fb_prove 448 Guest.Software.guestFn_charge_gas K.«charge_gas»

theorem fb_stack_push : TerminatingFunBoundedOn GuestInv (ofString "stack_push") K.«stack_push» := by
  fb_prove 454 Guest.Software.guestFn_stack_push K.«stack_push»

theorem fb_sk_make : TerminatingFunBoundedOn GuestInv (ofString "sk_make") K.«sk_make» := by
  fb_prove 360 Guest.Software.guestFn_sk_make K.«sk_make»

theorem fb_htab_item : TerminatingFunBoundedOn GuestInv (ofString "htab_item") K.«htab_item» := by
  fb_prove 143 Guest.Software.guestFn_htab_item K.«htab_item»

theorem fb_htab_new : TerminatingFunBoundedOn GuestInv (ofString "htab_new") K.«htab_new» := by
  fb_prove 128 Guest.Software.guestFn_htab_new K.«htab_new»

theorem fb_htab_grow : TerminatingFunBoundedOn GuestInv (ofString "htab_grow") K.«htab_grow» := by
  fb_prove 137 Guest.Software.guestFn_htab_grow K.«htab_grow»

theorem fb_htab_new_node : TerminatingFunBoundedOn GuestInv (ofString "htab_new_node") K.«htab_new_node» := by
  fb_prove 134 Guest.Software.guestFn_htab_new_node K.«htab_new_node»

theorem fb_htab_new_leaf : TerminatingFunBoundedOn GuestInv (ofString "htab_new_leaf") K.«htab_new_leaf» := by
  fb_prove 135 Guest.Software.guestFn_htab_new_leaf K.«htab_new_leaf»

theorem fb_htab_new_internal :
    TerminatingFunBoundedOn GuestInv (ofString "htab_new_internal") K.«htab_new_internal» := by
  fb_prove 136 Guest.Software.guestFn_htab_new_internal K.«htab_new_internal»

/-! ### Structural counter increment without clock budget (`IncrStep`) -/

inductive IncrStep (c : MlS) (step : BitVec 64) : ProgHOL 64 → Prop
  | incr : IncrStep c step (.assign .local c (.op .add [.var .local c, .const step]))
  | seq (first : ProgHOL 64) {tail : ProgHOL 64}
      (avoid : avoidsLocal c first = true) (rest : IncrStep c step tail) :
      IncrStep c step (.seq first tail)
  | dec (name : MlS) (shape : ShapeHOL) (init : ExpHOL 64) {body : ProgHOL 64}
      (distinct : c ≠ name) (rest : IncrStep c step body) :
      IncrStep c step (.dec name shape init body)

theorem IncrStep.run {c : MlS} {step : BitVec 64} {body : ProgHOL 64}
    (hb : IncrStep c step body) :
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (y : BitVec 64),
      s.locals.lookup c = some (.val (.word y)) →
      (evaluateHOLFiniteState s body).1 = none →
      (evaluateHOLFiniteState s body).2.locals.lookup c = some (.val (.word (y + step))) := by
  induction hb with
  | incr =>
    intro F s y hy _
    have run : evaluateHOLFiniteState s
        (.assign .local c (.op .add [.var .local c, .const step])) =
        (none, setVarHOLFinite c (.val (.word (y + step))) s) := by
      simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hy, wordOpHOL, wordOp,
        valueIsWord, valueWord, lookupKvarHOLExact, isValidValueHOLExact, setKvarHOLFinite,
        shapeOfHOLExact, shapeEqHOL]
    rw [run]
    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  | seq first avoid rest ih =>
    intro F s y hy hnone
    have frame := evaluate_avoidsLocal_flowing c first avoid s
    rw [evaluateHOLFiniteState_seq_line780] at hnone ⊢
    rcases hr1 : evaluateHOLFiniteState s first with ⟨r1, mid⟩
    rw [hr1] at frame hnone
    cases r1 with
    | some _ => simp at hnone
    | none =>
      dsimp only at hnone ⊢
      exact ih mid y ((frame (Or.inl rfl)).trans hy) hnone
  | dec name shape init distinct rest ih =>
    rename_i sub
    intro F s y hy hnone
    rcases hrun : evaluateHOLFiniteState s (.dec name shape init sub) with ⟨r, post⟩
    rw [hrun] at hnone
    dsimp only at hnone ⊢
    obtain ⟨val, inner, hin, hpost⟩ := dec_flowing (Or.inl hnone) hrun
    have hy' : (setVarHOLFinite name val s).locals.lookup c = some (.val (.word y)) := by
      simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm distinct, hy]
    have hinner : (evaluateHOLFiniteState (setVarHOLFinite name val s) sub).1 = none := by
      rw [hin]; exact hnone
    have hres := ih (setVarHOLFinite name val s) y hy' hinner
    rw [hin] at hres
    rw [hpost, PanRunBounded.resVarEq_lookup, if_neg distinct]
    exact hres

/-! ### `htab_first_diff` (`guestAst[130]`) -/

attribute [local irreducible] TerminatingProgBoundedOn in
theorem fb_htab_first_diff :
    TerminatingFunBoundedOn GuestInv (ofString "htab_first_diff") K.«htab_first_diff» := by
  fb_unfold 130 Guest.Software.guestFn_htab_first_diff
  have hinner :
      ProgBounded
        (.dec (ofString "j") .one (.const 0)
          (.while (.cmp .less (.var .local (ofString "j")) (.const 8))
            (.seq
              (.ite
                (.cmp .notEqual
                  (.op .and
                    [.shift .lsr (.var .local (ofString "x"))
                      (.op .sub [.const 7, .var .local (ofString "j")]), .const 1])
                  (.const 0))
                (.return (.op .add [.panop .mul [.var .local (ofString "i"), .const 8],
                  .var .local (ofString "j")]))
                .skip)
              (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"), .const 1])))))
        8 := by
    intro F state hcode hbudget
    apply RunBounded.decConst
    let s0 := setVarHOLFinite (ofString "j") (.val (.word 0)) state
    have hs0_j : s0.locals.lookup (ofString "j") = some (.val (.word 0)) := by
      simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    exact countedWhile_from (ofString "j") .less (Or.inl rfl) 8 1 (by decide) (by decide)
      (cost := 0) (countedBody_seq_straight _ (by decide) (by decide) (by decide) CountedBody.incr)
      s0 hcode 0 hs0_j (by decide) hbudget
  refine TerminatingProgBoundedOn.weaken' (K := ((domainBytes + 1 + 1) * (8 + 1)) + 0) ?_ ?_
  · refine dec_guestInv _ _ _ (TerminatingProgBoundedOn.seq_guestInv ?_ (straightOn _ rfl))
    refine while_walk_cost (d := ofString "a") (i := ofString "i") (stride := BitVec.ofNat 64 1) (B := 8)
      (by decide) (by decide)
      (dec_guestInv _ _ _ (TerminatingProgBoundedOn.seq_guestInv
        (TerminatingProgBoundedOn.ite_on (progOn hinner) (straightOn _ rfl))
        (straightOn _ rfl)))
      (fun s y _ hy hnone =>
        (IncrStep.dec _ _ _ (by decide) (IncrStep.seq _ (by decide) IncrStep.incr)).run s y hy hnone)
      (by decide)
      (firstAccess_dec_xor_loadByte _ _ _ _ _ _)
      (by decide)
  · unfold K.«htab_first_diff»
    simp only [Nat.max_def]
    split_ifs <;> omega

/-! ### `keccak256` (`guestAst[103]`) -/

private theorem op_hd_none {F : Type} (s : PanSemStateFiniteExact 64 F)
    (bop : BinOp) (e1 : ExpHOL 64) (es : List (ExpHOL 64))
    (h1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e1 = none) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op bop (e1 :: es)) = none := by
  simp only [evalHOLExact, evalListHOLExact]
  rw [h1]

private theorem op2_snd_none {F : Type} (s : PanSemStateFiniteExact 64 F)
    (bop : BinOp) (e1 e2 : ExpHOL 64)
    (h2 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e2 = none) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op bop [e1, e2]) = none := by
  simp only [evalHOLExact, evalListHOLExact]
  rcases @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e1 with _ | v1
  · rfl
  · rw [h2]

private theorem store_rhs_none_err {F : Type} (s : PanSemStateFiniteExact 64 F)
    (lhs rhs : ExpHOL 64)
    (hr : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) rhs = none) :
    evaluateHOLFiniteState s (.store lhs rhs) = (some .error, s) := by
  rw [evaluateHOLFiniteState_store]
  split
  · rw [hr]
  · rfl

private theorem keccak_absorb_body_access {F : Type}
    (s : PanSemStateFiniteExact 64 F) (b : BitVec 64)
    (hP : GuestInv s)
    (hblk : s.locals.lookup (ofString "blk") = some (.val (.word b)))
    (hret : ∃ w, (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_keccak_absorb_block)).1 =
      some (.returned w)) :
    sourceBase ≤ b.toNat ∧ b.toNat < heapEnd := by
  by_contra hout
  obtain ⟨wret, hr⟩ := hret
  dsimp only [sourceFnBody, sourceFunctionEntry, extractFn, Guest.Software.guestFn_keccak_absorb_block,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map] at hr
  rw [evaluateHOLFiniteState_dec_total] at hr
  dsimp only at hr
  have hev0 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.const (BitVec.ofNat 64 0)) = some (.val (.word (BitVec.ofNat 64 0))) := rfl
  have hsh0 : shapeEqHOL .one (shapeOfHOLExact (.val (.word (BitVec.ofNat 64 0)) : ValueHOL 64)) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  rw [hev0] at hr; dsimp only at hr; rw [if_pos hsh0] at hr; dsimp only at hr
  set s0 := setVarHOLFinite (ofString "i") (.val (.word (BitVec.ofNat 64 0))) s
  have hs0_blk : s0.locals.lookup (ofString "blk") = some (.val (.word b)) := by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "i" ≠ ofString "blk" by decide, hblk]
  have hs0_i : s0.locals.lookup (ofString "i") = some (.val (.word 0)) := by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  rw [evaluateHOLFiniteState_seq_line780] at hr
  have h1_bad : ∀ r1 m1,
      evaluateHOLFiniteState s0
        (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
          (match (extractFn Guest.Software.guestFn_keccak_absorb_block).body with
           | .dec _ _ _ (.seq p _) => p | _ => .skip)) = (r1, m1) →
      r1 = some .error ∨ r1 = some .timeOut := by
    intro r1 m1 h1
    dsimp only [extractFn, Guest.Software.guestFn_keccak_absorb_block,
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map] at h1
    rw [evaluateHOLFiniteState_ite] at h1
    have hc_less : @evalHOLFinite 64 F _ s0 (fun a => Classical.propDecidable (s0.memaddrs a))
        (.cmp .less (.var .local (ofString "i")) (.const (BitVec.ofNat 64 136))) = some (.val (.word 1)) := by
      rw [evalHOLFinite_eq_toExact]
      simp [evalHOLExact, hs0_i, Compiler.Encoders.Asm.wordCmpHOL,
        Compiler.Encoders.Asm.holAsmSignedLess]
    have h10 : (1 : BitVec 64) ≠ 0 := by decide
    have ha_eval : @evalHOLExact 64 F _ (decClockHOLFinite s0).toExact
        (fun a => Classical.propDecidable ((decClockHOLFinite s0).memaddrs a))
        (.op .add [.var .local (ofString "blk"), .var .local (ofString "i")]) =
        some (.val (.word b)) := by
      have hblkd : (decClockHOLFinite s0).locals.lookup (ofString "blk") = some (.val (.word b)) := hs0_blk
      have hid : (decClockHOLFinite s0).locals.lookup (ofString "i") = some (.val (.word 0)) := hs0_i
      simp [evalHOLExact, evalListHOLExact, hblkd, hid, wordOpHOL, wordOp, valueIsWord, valueWord]
    split at h1
    · rename_i cw _
      by_cases hcw0 : cw = 0
      · rw [if_pos hcw0] at h1
        rw [evaluateHOLFiniteState_while_fixClockRewrite, hc_less] at h1
        dsimp only at h1
        rw [if_pos h10] at h1
        by_cases hk0 : s0.clock = 0
        · rw [if_pos hk0] at h1; injection h1 with hr1 _; exact Or.inr hr1.symm
        · rw [if_neg hk0, evaluateHOLFiniteState_seq_line780] at h1
          have hndom : ¬ (decClockHOLFinite s0).memaddrs (panByteAlignHOL (width := 64) b) := by
            intro hd; change s.memaddrs _ at hd; rw [hP.memaddrs] at hd
            have := ordinaryDomain_bounds _ hd
            have := byteAlign_bounds b
            exact hout ⟨by omega, by omega⟩
          have hlb : @evalHOLExact 64 F _ (decClockHOLFinite s0).toExact
              (fun a => Classical.propDecidable ((decClockHOLFinite s0).memaddrs a))
              (.loadByte (.op .add [.var .local (ofString "blk"), .var .local (ofString "i")])) = none := by
            rcases heq : @evalHOLExact 64 F _ (decClockHOLFinite s0).toExact
                (fun a => Classical.propDecidable ((decClockHOLFinite s0).memaddrs a))
                (.loadByte (.op .add [.var .local (ofString "blk"), .var .local (ofString "i")])) with _ | v
            · rfl
            · obtain ⟨a, ha, hd⟩ := eval_loadByte (decClockHOLFinite s0)
                (h := fun a => Classical.propDecidable ((decClockHOLFinite s0).memaddrs a)) _ v heq
              rw [ha_eval] at ha; injection ha with ha; injection ha with ha; injection ha with ha
              subst ha; exact absurd hd hndom
          rw [store_rhs_none_err (decClockHOLFinite s0) _ _
            (op2_snd_none (decClockHOLFinite s0) .xor _ _
              (op_hd_none (decClockHOLFinite s0) .or _ _ hlb))] at h1
          dsimp only at h1
          injection h1 with hr1 _; exact Or.inl hr1.symm
      · rw [if_neg hcw0] at h1
        rw [evaluateHOLFiniteState_while_fixClockRewrite, hc_less] at h1
        dsimp only at h1
        rw [if_pos h10] at h1
        by_cases hk0 : s0.clock = 0
        · rw [if_pos hk0] at h1; injection h1 with hr1 _; exact Or.inr hr1.symm
        · rw [if_neg hk0, evaluateHOLFiniteState_seq_line780] at h1
          have hndom : ¬ (decClockHOLFinite s0).memaddrs b := by
            intro hd; change s.memaddrs b at hd; rw [hP.memaddrs] at hd
            have := ordinaryDomain_bounds b hd; exact hout ⟨by omega, by omega⟩
          have hld : @evalHOLExact 64 F _ (decClockHOLFinite s0).toExact
              (fun a => Classical.propDecidable ((decClockHOLFinite s0).memaddrs a))
              (.load .one (.op .add [.var .local (ofString "blk"), .var .local (ofString "i")])) = none := by
            rcases heq : @evalHOLExact 64 F _ (decClockHOLFinite s0).toExact
                (fun a => Classical.propDecidable ((decClockHOLFinite s0).memaddrs a))
                (.load .one (.op .add [.var .local (ofString "blk"), .var .local (ofString "i")])) with _ | v
            · rfl
            · obtain ⟨a, ha, hd, _⟩ := eval_load_one (decClockHOLFinite s0)
                (h := fun a => Classical.propDecidable ((decClockHOLFinite s0).memaddrs a)) _ v heq
              rw [ha_eval] at ha; injection ha with ha; injection ha with ha; injection ha with ha
              subst ha; exact absurd hd hndom
          rw [store_rhs_none_err (decClockHOLFinite s0) _ _
            (op2_snd_none (decClockHOLFinite s0) .xor _ _ hld)] at h1
          dsimp only at h1
          injection h1 with hr1 _; exact Or.inl hr1.symm
    · injection h1 with hr1 _; exact Or.inl hr1.symm
  rcases h1_eq : evaluateHOLFiniteState s0 _ with ⟨r1, m1⟩
  rw [h1_eq] at hr
  rcases h1_bad r1 m1 h1_eq with rfl | rfl <;> simp at hr

private theorem firstAccess_keccak_absorb (stp d i : MlS) :
    FirstAccess d i (.call (some (none, none)) (ofString "keccak_absorb_block")
      [.var .local stp, .op .add [.var .local d, .var .local i]]) := by
  have hlk_inst : originalRuntimeCode.lookup (ofString "keccak_absorb_block") =
      some ([(ofString "stp", .one), (ofString "blk", .one)],
        sourceFnBody Guest.Software.guestFn_keccak_absorb_block, .one) :=
    lookup_of_guestAst_getElem 102 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_keccak_absorb_block) rfl
  intro F s hcode hP hnone
  rw [evaluateHOLFiniteState_call] at hnone
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local stp, .op .add [.var .local d, .var .local i]] with _ | vals
  · rw [hargs] at hnone; simp at hnone
  · rw [hargs] at hnone; dsimp only at hnone
    rcases hlk : lookupCodeHOLFinite s.code.lookup (ofString "keccak_absorb_block") vals with _ | ⟨body, callee, rs⟩
    · rw [hlk] at hnone; simp at hnone
    · rw [hlk] at hnone; dsimp only at hnone
      split at hnone
      · simp at hnone
      · rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨r1, bpost⟩
        rw [hrun] at hnone
        rcases r1 with _ | (_ | _ | _ | _ | w | _ | _)
        all_goals try (simp [emptyLocalsHOLFinite] at hnone; done)
        have hbody := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "keccak_absorb_block")
          _ _ _ _ _ vals callee (by rw [hcode]; exact hlk_inst) hlk
        subst hbody
        rw [evalListHOLFinite_eq_toExact] at hargs
        simp only [evalListHOLExact] at hargs
        rcases hs1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
            (.var .local stp) with _ | vstp
        · simp [hs1] at hargs
        · rcases hs2 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
              (.op .add [.var .local d, .var .local i]) with _ | vblk
          · simp [hs1, hs2] at hargs
          · simp only [hs1, hs2] at hargs
            injection hargs with hvvals
            subst hvvals
            have hvblk_eq : ∃ x y : BitVec 64,
                s.locals.lookup d = some (.val (.word x)) ∧
                s.locals.lookup i = some (.val (.word y)) ∧
                vblk = .val (.word (x + y)) := by
              rcases vblk with ⟨⟨a⟩⟩ | fs | ⟨nm, fs⟩
              · obtain ⟨x, y, hx, hy, rfl⟩ := eval_add2_word s
                  (h := fun a => Classical.propDecidable (s.memaddrs a)) d i a hs2
                exact ⟨x, y, hx, hy, rfl⟩
              · simp only [evalHOLExact, evalListHOLExact] at hs2
                rcases hd : s.locals.lookup d with _ | vd <;> rcases hi : s.locals.lookup i with _ | vi <;>
                  simp only [hd, hi] at hs2
                · cases hs2
                · cases hs2
                · cases hs2
                · split at hs2
                  · simp [wordOpHOL] at hs2
                  · cases hs2
              · simp only [evalHOLExact, evalListHOLExact] at hs2
                rcases hd : s.locals.lookup d with _ | vd <;> rcases hi : s.locals.lookup i with _ | vi <;>
                  simp only [hd, hi] at hs2
                · cases hs2
                · cases hs2
                · cases hs2
                · split at hs2
                  · simp [wordOpHOL] at hs2
                  · cases hs2
            obtain ⟨x, y, hx, hy, heq_vblk⟩ := hvblk_eq
            subst heq_vblk
            have hcal_blk : callee.lookup (ofString "blk") = some (.val (.word (x + y))) := by
              unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hlk
              rw [hcode] at hlk
              split at hlk
              · cases hlk
              · rename_i eb el es raw
                have hinj := Option.some.inj hlk
                rcases Prod.mk.inj hinj with ⟨_, hr2⟩
                rcases Prod.mk.inj hr2 with ⟨rfl, _⟩
                unfold lookupCodeHOLExact at raw
                rw [hlk_inst] at raw
                dsimp only at raw
                split at raw
                · have rinj := Option.some.inj raw
                  rcases Prod.mk.inj rinj with ⟨_, r2⟩
                  rcases Prod.mk.inj r2 with ⟨hloc, _⟩
                  subst hloc
                  simp [List.zip, List.foldl]
                · cases raw
            have hbnd := keccak_absorb_body_access (callEntryStateHOLFinite s callee) (x + y)
              (guestInv_callEntry s callee hP) hcal_blk ⟨w, by rw [hrun]⟩
            exact ⟨x, y, hx, hy, hbnd.1, hbnd.2⟩

attribute [local irreducible] TerminatingProgBoundedOn in
theorem fb_keccak256 : TerminatingFunBoundedOn GuestInv (ofString "keccak256") K.«keccak256» := by
  fb_unfold 103 Guest.Software.guestFn_keccak256
  refine TerminatingProgBoundedOn.weaken'
    (K := (K.«memzero» + 1) +
      (((domainBytes + 1 + 1) * ((K.«keccak_absorb_block» + 1 + 0) + 1)) +
       ((K.«memzero» + 1) + ((K.«memcpy» + 1) + (0 + (0 + ((K.«keccak_absorb_block» + 1) +
         (max 0 (K.«memcpy» + 1) + 0)))))))) ?_ ?_
  · refine dec_guestInv _ _ _ (TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_memzero) ?_)
    refine dec_guestInv _ _ _ (TerminatingProgBoundedOn.seq_guestInv ?_ ?_)
    · refine while_walk_cost (d := ofString "p") (i := ofString "i") (stride := BitVec.ofNat 64 136)
        (B := K.«keccak_absorb_block» + 1 + 0) (by decide) (by decide)
        (TerminatingProgBoundedOn.seq_guestInv (call_guestInv' fb_keccak_absorb_block) (straightOn _ rfl))
        (fun s y _ hy hnone =>
          (IncrStep.seq _ (by decide) IncrStep.incr).run s y hy hnone)
        (by decide)
        (firstAccess_seq _ (firstAccess_keccak_absorb _ _ _))
        (by decide)
    · fb_auto
  · unfold K.«keccak256»
    generalize_K
    simp only [Nat.add_zero, Nat.zero_add, Nat.max_def, max_def]
    generalize domainBytes = D
    split_ifs <;> omega

end InitECandidate.Solver.Wave8GuestInv.PrimShardP10P30
