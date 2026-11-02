import InitECandidate.Solver.Wave8GuestInv.Shards.S13.LoopGuest

/- Reused/adapted from rlp/RlpWalk.lean at 998817a20efa0796e7eb06992d98f332943646bc. -/
set_option autoImplicit false
set_option maxRecDepth 100000

namespace InitECandidate.Solver.Wave8Leaves.S13

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8Leaves.S13.Spec

variable {GuestInv : ∀ {F : Type}, Flapjack.PanSemStateFiniteExact 64 F → Prop}
  [IsGuestInv GuestInv]
variable [HasOrdinaryDomain GuestInv]


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


/-- Rank of a walk address: bytes left below `heapEnd`, capped at `domainBytes + 1`. -/
def walkRank (a : BitVec 64) : Nat := min (heapEnd - a.toNat) (domainBytes + 1)

/-- Walk measure: the rank of `d + i` (`0` if either local is not a word). -/
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

/-- A program whose flowing runs access the address `d + i` inside `[sourceBase, heapEnd)`. -/
def FirstAccess (d i : MlS) (first : ProgHOL 64) : Prop :=
  ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), GuestInv s →
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
  | some r => simp at h

theorem firstAccess_seq {d i : MlS} {first : ProgHOL 64} (tail : ProgHOL 64)
    (h : FirstAccess (GuestInv := GuestInv) d i first) : FirstAccess (GuestInv := GuestInv) d i (.seq first tail) :=
  fun s hP hn => h s hP (seq_none_first s first tail hn)

theorem walkRank_step (a stride : BitVec 64) (hs : 0 < stride.toNat) (hs2 : stride.toNat ≤ 64)
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

theorem storeAccess_at (d i : MlS) (v : ExpHOL 64)
    {F : Type} (s : PanSemStateFiniteExact 64 F) (hP : GuestInv s)
    (hv : ∀ (h : DecidablePred s.memaddrs)
      (val : ValueHOL 64), @evalHOLExact 64 F _ s.toExact h v = some val → ∃ w, val = .val w) :
    (evaluateHOLFiniteState s (.store (.op .add [.var .local d, .var .local i]) v)).1 = none →
    ∃ x y : BitVec 64, s.locals.lookup d = some (.val (.word x)) ∧
      s.locals.lookup i = some (.val (.word y)) ∧
      sourceBase ≤ (x + y).toNat ∧ (x + y).toNat < heapEnd := by
  intro h
  rw [evaluateHOLFiniteState_store] at h
  split at h
  · rename_i address hdst
    obtain ⟨x, y, hx, hy, rfl⟩ := eval_add2_word s (h := fun a => Classical.propDecidable (s.memaddrs a)) d i address hdst
    refine ⟨x, y, hx, hy, ?_⟩
    split at h
    · rename_i val hval
      obtain ⟨w, rfl⟩ := hv _ val hval
      split at h
      · rename_i mem hmem
        have hdom : s.memaddrs (x + y) := by
          simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL] at hmem
          by_contra hc
          simp [hc] at hmem
        rw [HasOrdinaryDomain.memaddrs s hP] at hdom
        have := ordinaryDomain_bounds _ hdom
        omega
      · simp at h
    · simp at h
  · simp at h


/-- RLP walk rule restated with rev7's proved ranking combinator. -/
theorem while_walk {cond : ExpHOL 64} {body : ProgHOL 64} {d i : MlS} {stride : BitVec 64}
    (hs : 0 < stride.toNat) (hs2 : stride.toNat ≤ 64)
    (hcount : CountedBody i stride body 0) (hd : avoidsLocal d body = true)
    (hfirst : FirstAccess (GuestInv := GuestInv) d i body) (hstraight : extStraightLine body = true)
    (hnc : noTopContinue body = true) :
    TerminatingProgBoundedOn GuestInv (.while cond body) ((domainBytes + 1 + 1) * (0 + 1)) := by
  refine TerminatingProgBoundedOn.while_rank (walkMu d i)
    (fun s hs => guestInv_decClock s hs) (straightOn _ hstraight)
    (fun s _ _ _ => walkMu_le d i s) ?_
  intro F s hcode hP _ hflow
  have hPd := guestInv_decClock s hP
  have hnone : (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none := by
    rcases hflow with h | h
    · exact h
    · exact False.elim ((evaluate_noTopContinue body hnc (decClockHOLFinite s)) h)
  obtain ⟨x, y, hx, hy, hlo, hhi⟩ := hfirst (decClockHOLFinite s) hPd hnone
  obtain ⟨_, _, _, _, c5⟩ := hcount.run (decClockHOLFinite s) hcode y hy (Nat.zero_le _)
  obtain ⟨hiy, _⟩ := c5 hnone
  have hdk := evaluate_avoidsLocal_flowing d body hd (decClockHOLFinite s) (Or.inl hnone)
  refine ⟨guestInv_evaluate _ _ hPd, ?_⟩
  have hx' : s.locals.lookup d = some (.val (.word x)) := hx
  have hy' : s.locals.lookup i = some (.val (.word y)) := hy
  have hxp : (evaluateHOLFiniteState (decClockHOLFinite s) body).2.locals.lookup d =
      some (.val (.word x)) := hdk.trans hx
  unfold walkMu
  rw [hxp, hiy, hx', hy']
  dsimp only
  rw [← BitVec.add_assoc]
  exact walkRank_step _ _ hs hs2 hlo hhi

end InitECandidate.Solver.Wave8Leaves.S13
