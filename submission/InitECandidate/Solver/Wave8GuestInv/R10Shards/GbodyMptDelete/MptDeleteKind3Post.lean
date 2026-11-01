import InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptDelete.MptDeleteKind3Cont

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptDelete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
theorem mptBranchReady_locals {F : Type} {s : PanSemStateFiniteExact 64 F}
    (ls : HolFiniteMapExact MlS (ValueHOL 64)) (clock : Nat)
    (hl : ∀ n ∈ ["top", "res", "go", "level", "klen", "node", "key", "k"],
      ls.lookup (ofString n) = s.locals.lookup (ofString n))
    (hs : MptDeleteBranchReady s) : MptDeleteBranchReady { s with locals := ls, clock := clock } := by
  obtain ⟨ha, hgo, hk, Nd, fs, hn, hst, hres, hle, hnode, hkey⟩ := hs
  have heq : ∀ n ∈ ["top", "res", "go", "level", "klen", "node", "key", "k"],
      locN { s with locals := ls, clock := clock } n = locN s n :=
    fun n hn => mptLocN_locals (hl n hn)
  refine ⟨(arenaReady_with_locals s ls clock).2 ha, ?_, ?_, Nd, fs,
    (mptNodeHeap_locals s ls clock Nd).2 hn, ?_, ?_, ?_, ?_, ?_⟩
  · rw [heq "go" (by simp)]; exact hgo
  · rw [heq "k" (by simp)]; exact hk
  · rw [heq "top" (by simp)]; exact (mptStack_locals s ls clock Nd fs _).2 hst
  · rw [heq "res" (by simp)]; exact hres
  · rw [heq "level" (by simp), heq "klen" (by simp)]; exact hle
  · change locN { s with locals := ls, clock := clock } "node" ∈ Nd ∧
      memW s (locN { s with locals := ls, clock := clock } "node") = 3
    rw [heq "node" (by simp)]; exact hnode
  · rw [heq "key" (by simp), heq "level" (by simp), heq "klen" (by simp)]
    exact (mptKeyIn_locals s ls clock Nd _ _).2 hkey

theorem mptBranchReady_idx {F : Type} {s : PanSemStateFiniteExact 64 F}
    (w : BitVec 64) (hs : MptDeleteBranchReady s) :
    MptDeleteBranchReady (setVarHOLFinite (ofString "idx") (.val (.word w)) s) := by
  apply mptBranchReady_locals _ _ _ hs
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp +decide only [setVarHOLFinite, HolFiniteMapExact.lookup_update_pointwise, if_true, if_false]

theorem mptHead_restore {F : Type} {s : PanSemStateFiniteExact 64 F}
    (name : MlS) (old : Option (ValueHOL 64))
    (hname : ∀ n ∈ ["top", "res", "go", "level", "klen", "node", "key"], ofString n ≠ name)
    (hs : MptDeleteHead s) :
    MptDeleteHead { s with locals := HolFiniteMapExact.resVarEq s.locals (name, old) } := by
  exact mptDeleteHead_locals _ _ (fun n hn => resVarEq_lookup_ne _ _ _ _ (hname n hn)) hs

theorem mptCondTrue_eq {F : Type} {s : PanSemStateFiniteExact 64 F}
    {n : String} {c : BitVec 64}
    (h : CondTrue (.cmp .equal (.var .local (ofString n)) (.const c)) s) : locN s n = c.toNat := by
  obtain ⟨w, hw, hne⟩ := h
  obtain ⟨a, b, han, hb, hw⟩ := cond_local s .equal n (.const c) w hw
  have heq := evalAt_const s c (.val (.word b)) hb
  cases heq
  simp only [Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw
  by_cases hac : a = c
  · subst a; exact han.symm
  · simp [hac] at hw
    exact (hne hw).elim

theorem mptCondFalse_eqLoc {F : Type} {s : PanSemStateFiniteExact 64 F}
    {n m : String}
    (h : CondFalse (.cmp .equal (.var .local (ofString n)) (.var .local (ofString m))) s) :
    locN s n ≠ locN s m := by
  obtain ⟨a, b, ha, hb, heq⟩ := evalAt_cmp s .equal _ _ 0 h
  have han := evalAt_local s n a ha
  have hbn := evalAt_local s m b hb
  intro hh
  have hab : a = b := BitVec.eq_of_toNat_eq (han.trans (hh.trans hbn.symm))
  subst b
  simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at heq

end InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptDelete
