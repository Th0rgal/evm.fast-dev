import InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptInsert.MptCuts
import InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptInsert.RlpPhased
import InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptInsert.RlpWord

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody.InsertCount
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8Leaves.Rlp

/-- Only cache cells in the heap interval can change during an empty extension. -/
noncomputable def dirty {F : Type} (s : PanSemStateFiniteExact 64 F) : Finset Nat := by
  classical
  exact (Finset.range (heapLimit - sourceBase)).filter fun a =>
    s.memory (BitVec.ofNat 64 (sourceBase + a)) ≠ .word 0

theorem dirty_le {F : Type} (s : PanSemStateFiniteExact 64 F) : (dirty s).card ≤ heapLimit - sourceBase := by
  classical
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp)

theorem dirty_clear_subset {F : Type} (s : PanSemStateFiniteExact 64 F) (n : Nat) :
    dirty (clearCache s n) ⊆ dirty s := by
  classical
  intro a ha
  simp only [dirty, Finset.mem_filter, Finset.mem_range] at ha ⊢
  refine ⟨ha.1, ?_⟩
  simpa only [clearCache] using (show s.memory (BitVec.ofNat 64 (sourceBase + a)) ≠ .word 0 from by
    intro hz
    apply ha.2
    simp only [clearCache]
    split
    · rfl
    · exact hz)

/-- Equal dirty-cell counts mean the entire memory is unchanged, including addresses
outside the heap. This charges every genuine warmup without assuming an acyclic trie. -/
theorem clear_eq_of_dirty_eq {F : Type} (s : PanSemStateFiniteExact 64 F) (n : Nat)
    (hlo : sourceBase ≤ n) (hn : n + 24 < heapLimit)
    (heq : (dirty (clearCache s n)).card = (dirty s).card) :
    clearCache s n = s := by
  classical
  have hset : dirty (clearCache s n) = dirty s :=
    Finset.eq_of_subset_of_card_le (dirty_clear_subset s n) (by omega)
  have hz (d : Nat) (hd : d = 8 ∨ d = 16 ∨ d = 24) :
      s.memory (BitVec.ofNat 64 (n + d)) = .word 0 := by
    by_contra h
    have haddr : sourceBase + (n + d - sourceBase) = n + d := by omega
    have hm : n + d - sourceBase ∈ dirty s := by
      simp only [dirty, Finset.mem_filter, Finset.mem_range, haddr]
      exact ⟨by rcases hd with rfl | rfl | rfl <;> omega, h⟩
    rw [← hset] at hm
    have hbad := (Finset.mem_filter.mp hm).2
    rw [haddr] at hbad
    apply hbad
    rcases hd with rfl | rfl | rfl <;> simp [clearCache]
  have hm : (clearCache s n).memory = s.memory := by
    funext a
    dsimp only [clearCache]
    split
    · rename_i h
      rcases h with rfl | rfl | rfl
      · exact (hz 8 (Or.inl rfl)).symm
      · exact (hz 16 (Or.inr (Or.inl rfl))).symm
      · exact (hz 24 (Or.inr (Or.inr rfl))).symm
    · rfl
  change { s with memory := (clearCache s n).memory } = s
  rw [hm]

/-- A syntactic certificate that assignments to a local only write Boolean words. -/
def boolWrites (x : MlS) (p : ProgHOL 64) : Bool :=
  if avoidsLocal x p then true else
  match p with
  | .assign .local _ (.const w) => w == 0 || w == 1
  | .seq a b | .ite _ a b => boolWrites x a && boolWrites x b
  | .dec n _ _ b | .decCall n _ _ _ b => n == x || boolWrites x b
  | _ => false

def BoolLocal {F : Type} (x : MlS) (s : PanSemStateFiniteExact 64 F) : Prop :=
  s.locals.lookup x = some (.val (.word 0)) ∨ s.locals.lookup x = some (.val (.word 1))

theorem boolLocal_congr {F : Type} (x : MlS) {s t : PanSemStateFiniteExact 64 F}
    (he : t.locals.lookup x = s.locals.lookup x) (h : BoolLocal x s) : BoolLocal x t := by
  simpa only [BoolLocal, he] using h

theorem evaluate_boolLocal {F : Type} (x : MlS) (p : ProgHOL 64)
    (hp : boolWrites x p = true) (s : PanSemStateFiniteExact 64 F)
    (hs : BoolLocal x s) (hf : Flowing (evaluateHOLFiniteState s p).1) :
    BoolLocal x (evaluateHOLFiniteState s p).2 := by
  by_cases hav : avoidsLocal x p = true
  · exact boolLocal_congr x (evaluate_avoidsLocal_flowing x p hav s hf) hs
  have hp' := hp
  unfold boolWrites at hp'
  rw [if_neg hav] at hp'
  cases hprog : p with
  | assign k n e =>
    cases k <;> cases e <;> simp only [hprog] at hp'
    all_goals try contradiction
    rename_i w
    have hw : w = 0 ∨ w = 1 := by simpa only [Bool.or_eq_true, beq_iff_eq] using hp'
    subst hprog
    rw [evaluateHOLFiniteState_assign]
    simp only [evalHOLExact]
    split
    · by_cases hn : n = x
      · subst hn
        rcases hw with rfl | rfl
        · left; simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        · right; simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      · apply boolLocal_congr x _ hs
        simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn]
    · exact hs
  | seq a b =>
    have hpab : boolWrites x a = true ∧ boolWrites x b = true := by
      simpa only [hprog, Bool.and_eq_true] using hp'
    subst hprog
    rw [evaluateHOLFiniteState_seq_line780] at hf ⊢
    cases hr : evaluateHOLFiniteState s a with
    | mk r t =>
      rw [hr] at hf
      cases r with
      | none =>
        apply evaluate_boolLocal x b hpab.2 t _ hf
        have h := evaluate_boolLocal x a hpab.1 s hs (by rw [hr]; exact Or.inl rfl)
        simpa only [hr] using h
      | some r =>
        have h := evaluate_boolLocal x a hpab.1 s hs (by rw [hr]; exact hf)
        simpa only [hr] using h
  | ite e a b =>
    have hpab : boolWrites x a = true ∧ boolWrites x b = true := by
      simpa only [hprog, Bool.and_eq_true] using hp'
    subst hprog
    rw [evaluateHOLFiniteState_ite] at hf ⊢
    split
    · rename_i w hw
      simp only [hw] at hf
      split
      · rename_i hz
        rw [if_pos hz] at hf
        exact evaluate_boolLocal x b hpab.2 s hs hf
      · rename_i hz
        rw [if_neg hz] at hf
        exact evaluate_boolLocal x a hpab.1 s hs hf
    · exact hs
  | dec n sh e b =>
    have hb : n = x ∨ boolWrites x b = true := by
      simpa only [hprog, Bool.or_eq_true, beq_iff_eq] using hp'
    subst hprog
    cases hr : evaluateHOLFiniteState s (.dec n sh e b) with
    | mk r t =>
      rw [hr] at hf
      obtain ⟨v, u, hu, hl⟩ := dec_flowing hf hr
      apply boolLocal_congr x (s := if n = x then s else u)
      · rw [hl, PanRunBounded.resVarEq_lookup]
        by_cases hn : n = x
        · simp [hn]
        · simp [hn, Ne.symm hn]
      · split
        · exact hs
        · rename_i hn
          have hbu : boolWrites x b = true := hb.resolve_left hn
          have hs' : BoolLocal x (setVarHOLFinite n v s) := by
            apply boolLocal_congr x _ hs
            simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn]
          have h := evaluate_boolLocal x b hbu (setVarHOLFinite n v s) hs' (by rw [hu]; exact hf)
          simpa only [hu] using h
  | decCall n sh f args b =>
    have hb : n = x ∨ boolWrites x b = true := by
      simpa only [hprog, Bool.or_eq_true, beq_iff_eq] using hp'
    subst hprog
    cases hr : evaluateHOLFiniteState s (.decCall n sh f args b) with
    | mk r t =>
      rw [hr] at hf
      obtain ⟨v, u, t', hl, _, hu, ht⟩ := decCall_flowing hf hr
      by_cases hn : n = x
      · apply boolLocal_congr x _ hs
        rw [ht, PanRunBounded.resVarEq_lookup, if_pos hn.symm, hn]
      · have hs' : BoolLocal x u := boolLocal_congr x (hl x (Ne.symm hn)) hs
        have h := evaluate_boolLocal x b (hb.resolve_left hn) u hs' (by rw [hu]; exact hf)
        apply boolLocal_congr x (s := t')
        · rw [ht, PanRunBounded.resVarEq_lookup, if_neg (Ne.symm hn)]
        · simpa only [hu] using h
  | _ => simp [hprog] at hp'
termination_by sizeOf p

end InitECandidate.Solver.Wave8GuestInv.GuardedBody.InsertCount
