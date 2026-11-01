import InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptDelete.MptDeleteKind3Support

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
/-- The branch path after reading tag 3 and resetting the descent flag. -/
def MptDeleteBranchReady : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ locN s "go" = 0 ∧ locN s "k" = 3 ∧
    ∃ Nd fs, NodeHeap s Nd ∧ MptStack s Nd (locN s "top") fs ∧
      RootIn Nd (locN s "res") ∧ locN s "level" ≤ locN s "klen" ∧
      NodeKind s Nd "node" 3 ∧
      KeyIn s Nd (locN s "key" + locN s "level") (locN s "klen" - locN s "level")

theorem mptDeleteBranch_head {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : MptDeleteBranchReady s) : MptDeleteHead s := by
  obtain ⟨ha, hgo, _, Nd, fs, hn, hstack, hres, _⟩ := h
  exact ⟨ha, Nd, fs, hn, hstack, hres, fun h => (h hgo).elim⟩

theorem mptInvalidate_lookup : originalRuntimeCode.lookup (ofString "node_invalidate") =
    some ((sourceFunctionEntry Guest.Software.guestFn_node_invalidate).2) := by
  exact originalRuntimeCode_lookup_of_guestAst_getElem 259 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_node_invalidate) rfl

/-- Invalidation preserves the caller's branch invariant and cannot raise the
scratch pointer. This uses the supplied node contract. -/
theorem mptDeleteBranch_invalidate (h : MptDeleteCallees) (sp : Nat) :
    Hoare (fun s => MptDeleteBranchReady s ∧ globN s "scratch_ptr" ≤ sp)
      (.call (some (none, none)) (ofString "node_invalidate") [.var .local (ofString "node")])
      (fun r t => r = none → MptDeleteBranchReady t ∧ globN t "scratch_ptr" ≤ sp) := by
  apply mptCall_hoare none (ofString "node_invalidate") [.var .local (ofString "node")]
  · intro F s values body callee ret v post hc hp hargs hl hr _
    obtain ⟨⟨ha, hgo, htag, Nd, fs, hn, hstack, hres, hlevel, hnode, hkey⟩, hsp⟩ := hp
    have hparam := mptOneLocal_param (param := "nd") (arg := "node")
      (by rw [hc]; exact mptInvalidate_lookup) hargs hl
    have hloc : locN (callEntryStateHOLFinite s callee) "nd" = locN s "node" := by
      simp only [locN, callEntryStateHOLFinite, hparam]
    have hae : ArenaReady (callEntryStateHOLFinite s callee) :=
      (arenaReady_with_locals s callee (s.clock - 1)).2 ha
    have hne : NodeHeap (callEntryStateHOLFinite s callee) Nd := hn
    have hroots : ∀ n ∈ ["nd"], RootIn Nd (locN (callEntryStateHOLFinite s callee) n) := by
      intro n hmem
      obtain rfl := List.mem_singleton.1 hmem
      rw [hloc]
      exact Or.inr hnode.1
    have hentry : NodeArgs ["nd"] (fun _ _ => True) (callEntryStateHOLFinite s callee) :=
      ⟨hae, Nd, hne, hroots, trivial⟩
    have he := FunSpec.at_lookup h.nf_node_invalidate s hc values body callee ret hl
      hentry (by rw [hr]; simp)
    rw [hr] at he
    obtain ⟨hat, hheap, hscratch, he⟩ := he (Or.inl ⟨v, rfl⟩)
    obtain ⟨Nd', hnt, hsub, hkind, hfresh, hfr, _, _⟩ := he Nd hne hroots trivial
    have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body
    rw [hr] at hmeta
    have hbe : post.be = (callEntryStateHOLFinite s callee).be := hmeta.2.2.1
    have hg : AllocatorGrows (callEntryStateHOLFinite s callee) post := ⟨hheap, hscratch⟩
    have hkeys : ∀ p len, KeyIn (callEntryStateHOLFinite s callee) Nd p len → KeyIn post Nd' p len :=
      fun _ _ hk => mptKeyIn_nodeFrame hae hat hbe hg hne hkind hfresh hfr hk
    have hst : MptStack post Nd' (locN s "top") fs :=
      mptStack_transfer hae.1 hat.1 hg hsub hkind hkeys
        (fun _ hlo hhi _ => mptScratch_nodeFrame hae hne hfr hlo hhi) fs _ ((mptStack_locals s callee (s.clock - 1) Nd fs _).2 hstack)
    change MptDeleteBranchReady { post with locals := s.locals } ∧ globN post "scratch_ptr" ≤ sp
    refine ⟨⟨(arenaReady_with_locals post s.locals post.clock).2 hat,
      hgo, htag, Nd', fs, (mptNodeHeap_locals post s.locals post.clock Nd').2 hnt,
      (mptStack_locals post s.locals post.clock Nd' fs _).2 hst, ?_, hlevel, ?_, ?_⟩, ?_⟩
    · rcases hres with hz | hm
      · exact Or.inl hz
      · exact Or.inr (hsub _ hm)
    · exact ⟨hsub _ hnode.1, (hkind _ hnode.1).trans hnode.2⟩
    · exact (mptKeyIn_locals post s.locals post.clock Nd' _ _).2 (hkeys _ _ hkey)
    · change globN post "scratch_ptr" ≤ globN s "scratch_ptr" at hscratch
      omega
  · intro F r t hn _ hr
    exact (hn hr).elim

end InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptDelete
