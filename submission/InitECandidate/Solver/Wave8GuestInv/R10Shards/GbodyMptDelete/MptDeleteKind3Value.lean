import InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptDelete.MptDeleteKind3Stores

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
theorem mptCollapse_lookup : originalRuntimeCode.lookup (ofString "_collapse_branch") =
    some ((sourceFunctionEntry Guest.Software.guestFn__collapse_branch).2) := by
  exact originalRuntimeCode_lookup_of_guestAst_getElem 276 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn__collapse_branch) rfl

/-- A branch collapse returns a typed result while preserving the saved stack. -/
theorem mptDeleteBranch_collapse (h : MptDeleteCallees) :
    Hoare MptDeleteBranchReady
      (.call (some (some (.local, ofString "res"), none)) (ofString "_collapse_branch")
        [.var .local (ofString "node")])
      (fun r t => r = none → MptDeleteHead t ∧ locN t "go" = 0) := by
  apply mptCall_hoare (some (ofString "res")) (ofString "_collapse_branch")
    [.var .local (ofString "node")]
  · intro F s values body callee ret v post hc hp hargs hl hr _
    obtain ⟨ha, hgo, _, Nd, fs, hn, hstack, _, _, hnode, _⟩ := hp
    have hparam := mptOneLocal_param (param := "node") (arg := "node")
      (by rw [hc]; exact mptCollapse_lookup) hargs hl
    have hloc : locN (callEntryStateHOLFinite s callee) "node" = locN s "node" := by
      simp only [locN, callEntryStateHOLFinite, hparam]
    have hae : ArenaReady (callEntryStateHOLFinite s callee) :=
      (arenaReady_with_locals s callee (s.clock - 1)).2 ha
    have hne : NodeHeap (callEntryStateHOLFinite s callee) Nd := hn
    have hroots : ∀ n ∈ ["node"], RootIn Nd (locN (callEntryStateHOLFinite s callee) n) := by
      intro n hmem
      obtain rfl := List.mem_singleton.1 hmem
      rw [hloc]
      exact Or.inr hnode.1
    have hreq : NodeKind (callEntryStateHOLFinite s callee) Nd "node" 3 := by
      change locN (callEntryStateHOLFinite s callee) "node" ∈ Nd ∧
        memW s (locN (callEntryStateHOLFinite s callee) "node") = 3
      rw [hloc]
      exact hnode
    have hentry : NodeArgs ["node"] (fun s Nd => NodeKind s Nd "node" 3)
        (callEntryStateHOLFinite s callee) := ⟨hae, Nd, hne, hroots, hreq⟩
    have he := FunSpec.at_lookup h.nf__collapse_branch s hc values body callee ret hl
      hentry (by rw [hr]; simp)
    rw [hr] at he
    obtain ⟨hat, hheap, hscratch, he⟩ := he (Or.inl ⟨v, rfl⟩)
    obtain ⟨Nd', hnt, hsub, hkind, hfresh, hfr, _, hret⟩ := he Nd hne hroots hreq
    obtain ⟨w, rfl, hroot⟩ := hret v rfl
    have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body
    rw [hr] at hmeta
    have hbe : post.be = (callEntryStateHOLFinite s callee).be := hmeta.2.2.1
    have hg : AllocatorGrows (callEntryStateHOLFinite s callee) post := ⟨hheap, hscratch⟩
    have hkeys : ∀ p len, KeyIn (callEntryStateHOLFinite s callee) Nd p len → KeyIn post Nd' p len :=
      fun _ _ hk => mptKeyIn_nodeFrame hae hat hbe hg hne hkind hfresh hfr hk
    have hst : MptStack post Nd' (locN s "top") fs :=
      mptStack_transfer hae.1 hat.1 hg hsub hkind hkeys
        (fun _ hlo hhi _ => mptScratch_nodeFrame hae hne hfr hlo hhi) fs _
        ((mptStack_locals s callee (s.clock - 1) Nd fs _).2 hstack)
    let t := setVarHOLFinite (ofString "res") (.val (.word w)) { post with locals := s.locals }
    change MptDeleteHead t ∧ locN t "go" = 0
    have htgo : locN t "go" = 0 := by
      rw [mptSetVar_locN_ne _ _ _ "go" (by decide)]
      exact hgo
    have httop : locN t "top" = locN s "top" :=
      mptSetVar_locN_ne _ _ _ "top" (by decide)
    have htres : locN t "res" = w.toNat := mptSetVar_locN_word _ _ _
    refine ⟨⟨?_, Nd', fs, ?_, ?_, ?_, fun hg => (hg htgo).elim⟩, htgo⟩
    · exact (arenaReady_with_locals post t.locals post.clock).2 hat
    · exact (mptNodeHeap_locals post t.locals post.clock Nd').2 hnt
    · rw [httop]
      exact (mptStack_locals post t.locals post.clock Nd' fs _).2 hst
    · rw [htres]
      exact hroot
  · intro F r t hn _ hr
    exact (hn hr).elim

theorem mptDeleteBranch_keep_node :
    Hoare MptDeleteBranchReady (.assign .local (ofString "res") (.var .local (ofString "node")))
      (fun r t => r = none → MptDeleteHead t ∧ locN t "go" = 0) := by
  apply Hoare.assign
  · intro F s v hs hv _
    obtain ⟨ha, hgo, _, Nd, fs, hn, hstack, _, _, hnode, _⟩ := hs
    have hnonnull : locN s "node" ≠ 0 := by
      have := (hn.1 _ hnode.1).2.2.1.1
      have hbase : 0 < sourceBase := by decide
      change sourceBase ≤ locN s "node" at this
      omega
    obtain ⟨w, hw, hnat⟩ := mptLocN_nonzero hnonnull
    change s.locals.lookup (ofString "node") = some v at hv
    rw [hw] at hv
    cases hv
    change MptDeleteHead (setVarHOLFinite (ofString "res") (.val (.word w)) s) ∧
      locN (setVarHOLFinite (ofString "res") (.val (.word w)) s) "go" = 0
    let t := setVarHOLFinite (ofString "res") (.val (.word w)) s
    have htgo : locN t "go" = 0 := by
      rw [mptSetVar_locN_ne _ _ _ "go" (by decide)]
      exact hgo
    have httop : locN t "top" = locN s "top" := mptSetVar_locN_ne _ _ _ _ (by decide)
    have htres : locN t "res" = w.toNat := mptSetVar_locN_word _ _ _
    refine ⟨⟨(arenaReady_with_locals s t.locals s.clock).2 ha,
      Nd, fs, (mptNodeHeap_locals s t.locals s.clock Nd).2 hn, ?_, ?_,
      fun hg => (hg htgo).elim⟩, htgo⟩
    · rw [httop]
      exact (mptStack_locals s t.locals s.clock Nd fs _).2 hstack
    · rw [htres, hnat]
      exact Or.inr hnode.1
  · intro F s hs hz
    cases hz

def mptDeleteValueCode : ProgHOL 64 :=
  .ite (.cmp .equal
      (.load .one (.op .add [.var .local (ofString "node"), .const 168])) (.const 0))
    (.assign .local (ofString "res") (.var .local (ofString "node")))
    (.seq (.store (.op .add [.var .local (ofString "node"), .const 160]) (.const 0))
      (.seq (.store (.op .add [.var .local (ofString "node"), .const 168]) (.const 0))
        (.call (some (some (.local, ofString "res"), none)) (ofString "_collapse_branch")
          [.var .local (ofString "node")])))

/-- The complete terminal branch, including the two value-clearing stores. -/
theorem mptDeleteBranch_value (h : MptDeleteCallees) :
    Hoare MptDeleteBranchReady mptDeleteValueCode
      (fun r t => r = none → MptDeleteHead t ∧ locN t "go" = 0) := by
  apply Hoare.ite
  · exact Hoare.mono mptDeleteBranch_keep_node (fun _ h => h.1)
  · exact Hoare.mono
      (mptHoare_seq (mptDeleteBranch_store 160 (Or.inl rfl))
        (mptHoare_seq (mptDeleteBranch_store 168 (Or.inr rfl)) (mptDeleteBranch_collapse h)))
      (fun _ h => h.1)
  · intro F s hs hr
    cases hr

end InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptDelete
