import InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptDelete.MptDeleteKind3Assemble

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
theorem mptDelete_kind3_run (h : MptDeleteCallees)
    {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (hc : s.code = originalRuntimeCode) (hp : MptDeleteActive s) (hk : mptKind s = 3)
    (hr : evaluateHOLFiniteState s mptDeleteBody = (none, t)) :
    MptDeleteHead t ∧ MptDeleteEffect s t := by
  have hnn : locN s "node" ≠ 0 := by
    intro hz
    simp [mptKind, hz] at hk
  have hkind : memW s (locN s "node") = 3 := by
    simpa only [mptKind, hnn, if_false] using hk
  obtain ⟨nw, hnw, hnwn⟩ := mptLocN_nonzero hnn
  obtain ⟨⟨ha, Nd, fs, hn, hst, hres, hact⟩, hgo⟩ := hp
  obtain ⟨hle, hroot, hkey⟩ := hact hgo
  have hnode : locN s "node" ∈ Nd := hroot.resolve_left hnn
  obtain ⟨s0, hreset, hrest⟩ := mptSeq_none hr
  obtain ⟨v, hv, _, hs0⟩ := mptAssign_none hreset
  have hv0 := evalAt_const s 0 v hv
  subst v
  subst s0
  rcases mptIte_none hrest with ⟨hz, _⟩ | ⟨_, hdec⟩
  · have hz0 := mptCondTrue_eq hz
    rw [mptSetVar_locN_ne s _ _ "node" (by decide)] at hz0
    exact (hnn hz0).elim
  · obtain ⟨kv, inner, hkv, hbody, ht⟩ := mptDec_none hdec
    let s0 := setVarHOLFinite (ofString "go") (.val (.word 0)) s
    have hnw0 : s0.locals.lookup (ofString "node") = some (.val (.word nw)) := by
      simp +decide only [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update_pointwise, if_false]
      exact hnw
    have haddr := mptAddConst_eval (s := s0) 0 hnw0
    obtain ⟨kw, rfl, hkwn⟩ := mptLoad_inv haddr hkv
    change kw.toNat = memW s (nw.toNat + 0) at hkwn
    have hkw3 : kw.toNat = 3 := by
      have hh : kw.toNat = memW s (locN s "node") := by
        simpa only [Nat.add_zero, hnwn] using hkwn
      exact hh.trans hkind
    let sk := setVarHOLFinite (ofString "k") (.val (.word kw)) s0
    have heq (n : String) (hname : n ∈ ["top", "res", "level", "klen", "node", "key"]) :
        locN sk n = locN s n := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hname
      rcases hname with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp +decide only [sk, s0, locN, setVarHOLFinite,
        HolFiniteMapExact.lookup_update_pointwise, if_false]
    have hready : MptDeleteBranchReady sk := by
      refine ⟨(arenaReady_with_locals s sk.locals s.clock).2 ha, ?_, ?_, Nd, fs,
        (mptNodeHeap_locals s sk.locals s.clock Nd).2 hn, ?_, ?_, ?_, ?_, ?_⟩
      · simp +decide only [sk, s0, locN, setVarHOLFinite,
          HolFiniteMapExact.lookup_update_pointwise, if_true, if_false]
      · simpa only [sk, mptSetVar_locN_word] using hkw3
      · rw [heq "top" (by simp)]
        exact (mptStack_locals s sk.locals s.clock Nd fs _).2 hst
      · rw [heq "res" (by simp)]; exact hres
      · rw [heq "level" (by simp), heq "klen" (by simp)]; exact hle
      · change locN sk "node" ∈ Nd ∧ memW s (locN sk "node") = 3
        rw [heq "node" (by simp)]
        exact ⟨hnode, hkind⟩
      · rw [heq "key" (by simp), heq "level" (by simp), heq "klen" (by simp)]
        exact (mptKeyIn_locals s sk.locals s.clock Nd _ _).2 hkey
    change evaluateHOLFiniteState sk mptDeleteAfterKind = (none, inner) at hbody
    have hdone := (mptDeleteAfterKind_hoare h (globN s "scratch_ptr")).run sk hc
      ⟨hready, Nat.le_refl _⟩ (by rw [hbody]; simp)
    rw [hbody] at hdone
    obtain ⟨hh, he⟩ := hdone rfl
    subst t
    refine ⟨mptHead_restore (ofString "k") _ ?_ hh, ?_⟩
    · simp +decide only [List.forall_mem_cons, List.forall_mem_nil, and_true]
    · rcases he with hstop | hdown
      · left
        have heqgo := resVarEq_lookup_ne inner.locals (ofString "k") (ofString "go")
          (s0.locals.lookup (ofString "k")) (by decide)
        exact mptLocN_locals heqgo |>.trans hstop
      · exact Or.inr hdown

end InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptDelete
