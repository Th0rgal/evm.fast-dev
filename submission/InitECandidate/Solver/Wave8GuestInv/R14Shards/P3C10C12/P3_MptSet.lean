import InitECandidate.Solver.Wave8GuestInv.R14Shards.P3C10C12.P3_MptSet_Memory

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2000
set_option linter.style.nameCheck false
set_option linter.unusedSimpArgs false

namespace InitECandidate.Solver.Wave8GuestInv.P3MptSet

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestUniformClockBound
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

private def AfterNk : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ locN s "vlen" < 2 ^ 40 ∧
    ∃ p l : BitVec 64,
      s.locals.lookup (ofString "nk") = some (.rStruct [.val (.word p), .val (.word l)]) ∧
      l.toNat ≤ 64 ∧
      ∃ Nd, NodeHeap s Nd ∧ RootIn Nd (memW s (locN s "m")) ∧ KeyIn s Nd p.toNat l.toNat

private def AfterRoot : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ locN s "vlen" < 2 ^ 40 ∧
    ∃ p l : BitVec 64,
      s.locals.lookup (ofString "nk") = some (.rStruct [.val (.word p), .val (.word l)]) ∧
      l.toNat ≤ 64 ∧
      ∃ Nd, NodeHeap s Nd ∧ RootIn Nd (locN s "root") ∧ KeyIn s Nd p.toNat l.toNat

private theorem nk_resume
    (hww : WritesWithin (fun s => [(globN s "keccak_pad", 136), (globN s "keccak_st", 200), (globN s "mpt_hash_scratch", 40)])
      ["heap_ptr"] (ofString "mpt_nibble_key"))
    (hnk : RetNibbles (ofString "mpt_nibble_key")) :
    DecCallResumeOn MptSetReady AfterNk (ofString "nk") (ofString "mpt_nibble_key")
      [.var .local (ofString "m"), .var .local (ofString "key"), .var .local (ofString "klen")] := by
  intro F s values body callee ret value post hcode hP hargs hl hrun
  obtain ⟨⟨hA, S, hW, ⟨Nm, hm⟩, _⟩, hklen_le, hvlen_lt⟩ := hP
  rcases hA with ⟨hginv, hp_lo, hp_hi, hfm_lo, hfm_hi, hsp_hi, hp_al, hfm_al, hsp_al⟩
  have hA : ArenaReady s := ⟨hginv, hp_lo, hp_hi, hfm_lo, hfm_hi, hsp_hi, hp_al, hfm_al, hsp_al⟩
  have hF : FixedTyped s := hW.2.2.1
  have hp3 := callee_param_three_exp s (ofString "mpt_nibble_key")
    (ofString "m") (ofString "key") (ofString "klen") .one .one .one _ _
    (by rw [hcode]; exact lookup_mpt_nibble_key) _ _ _ values body callee ret hargs hl
  obtain ⟨vm, vkey, vklen, he_m, _, he_klen, _, _, hc_klen⟩ := hp3
  have hklen_eq : locN (callEntryStateHOLFinite s callee) "klen" = locN s "klen" := by
    simp only [evalAt, evalHOLExact] at he_klen
    simp only [locN, callEntryStateHOLFinite, hc_klen, he_klen]
  have hAe : ArenaReady (callEntryStateHOLFinite s callee) :=
    localsFree_arenaReady s callee (s.clock - 1) hA
  have hnt : (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body).1 ≠ some .timeOut := by
    rw [hrun]; simp
  have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body
  rw [hrun] at hmeta
  have hbe : post.be = s.be := hmeta.2.2.1
  have hww_post := FunSpec.at_lookup hww s hcode values body callee ret hl hAe hnt
  have hnk_post := FunSpec.at_lookup hnk s hcode values body callee ret hl hAe hnt
  rw [hrun] at hww_post hnk_post
  obtain ⟨hApost, hhp_le, hsp_le, hfr, _⟩ := hww_post (Or.inl ⟨value, rfl⟩)
  obtain ⟨p, l, rfl, hnib, hl_le, hin_fresh⟩ := hnk_post value rfl
  have hl64 : l.toNat ≤ 64 := hl_le (by rw [hklen_eq]; exact hklen_le)
  have hag : AllocatorGrows s post := ⟨hhp_le, hsp_le⟩
  have hgap_al : (globN s "frame_mem_ptr") % 8 = 0 ∧ (globN s "scratch_ptr" - globN s "frame_mem_ptr") % 8 = 0 :=
    ⟨hfm_al, by omega⟩
  have hfresh_al : (globN s "heap_ptr") % 8 = 0 ∧ (heapLimit - globN s "heap_ptr") % 8 = 0 := by
    have hhl8 : heapLimit % 8 = 0 := by decide
    exact ⟨hp_al, by omega⟩
  have hm_unhit : IvlUnhit s post (locN s "m", 16) := by
    have hm_lo : sourceBase ≤ locN s "m" := by
      rcases hm.1 with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact h1
      · have : sourceBase ≤ scratchStart := by decide
        omega
    apply ivlUnhit_of_frameOutside hfr ?_ hfresh_al (disj_allocated_heapFree hA.2 hm.1) (by simp)
    intro j hj
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with (rfl | rfl | rfl) | rfl
    · exact buf_keep_cond hF hm_lo hm.2.2.2.1 "keccak_pad" 136 (by decide) (by decide) (by decide) (by decide)
    · exact buf_keep_cond hF hm_lo hm.2.2.2.1 "keccak_st" 200 (by decide) (by decide) (by decide) (by decide)
    · exact buf_keep_cond hF hm_lo hm.2.2.2.1 "mpt_hash_scratch" 40 (by decide) (by decide) (by decide) (by decide)
    · exact Or.inl ⟨hgap_al.1, hgap_al.2, disj_allocated_freeGap hA.2 hm.1⟩
  have hm_memW : memW post (locN s "m") = memW s (locN s "m") :=
    memW_eq_of_ivlUnhit hm_unhit hm.2.1.1 (ivl_allocated_bound hA.2 hm.1) ⟨by omega, by omega⟩
  have hext_unhit : ∀ o ∈ nodeExtents s Nm, o.2 ≠ 0 → IvlUnhit s post o := by
    intro o ho ho0
    have ho_info : Allocated s o ∧ sourceBase ≤ o.1 := by
      unfold nodeExtents at ho
      rcases List.mem_flatMap.mp ho with ⟨n, hn, hmem⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      obtain ⟨_, hal_n, hin_n, _, _, _, hkey_n, _⟩ := hm.2.2.2.2.1.1 n hn
      rcases hmem with rfl | rfl
      · exact ⟨hal_n, hin_n.1⟩
      · unfold nodePath at ho0 ⊢
        split_ifs at ho0 ⊢ with hp
        · rcases hkey_n hp.1 with h0 | ⟨_, hal_p, hin_p, _⟩
          · exact absurd h0 hp.2
          · exact ⟨hal_p, hin_p.1⟩
        · exact absurd rfl ho0
    obtain ⟨hal_o, ho_lo⟩ := ho_info
    apply ivlUnhit_of_frameOutside hfr ?_ hfresh_al (disj_allocated_heapFree hA.2 hal_o) ho0
    intro j hj
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hj
    have ho_disj_fix := (hm.2.2.2.2.2.2 o ho).2.2
    rcases hj with (rfl | rfl | rfl) | rfl
    · exact buf_keep_cond hF ho_lo ho_disj_fix "keccak_pad" 136 (by decide) (by decide) (by decide) (by decide)
    · exact buf_keep_cond hF ho_lo ho_disj_fix "keccak_st" 200 (by decide) (by decide) (by decide) (by decide)
    · exact buf_keep_cond hF ho_lo ho_disj_fix "mpt_hash_scratch" 40 (by decide) (by decide) (by decide) (by decide)
    · exact Or.inl ⟨hgap_al.1, hgap_al.2, disj_allocated_freeGap hA.2 hal_o⟩
  have hNm_post : NodeHeap post Nm :=
    nodeHeap_congr_unhit hA.1 hApost.1 hbe hag hm.2.2.2.2.1 hext_unhit
  have hkey_in : KeyIn post Nm p.toNat l.toNat := by
    by_cases hl0 : l.toNat = 0
    · exact Or.inl hl0
    · right
      have hin_hp : Inside (p.toNat, l.toNat) sourceBase (globN post "heap_ptr") :=
        ⟨Nat.le_trans hp_lo hin_fresh.1, hin_fresh.2⟩
      have hin_lim : Inside (p.toNat, l.toNat) sourceBase heapLimit :=
        ⟨hin_hp.1, Nat.le_trans hin_fresh.2 hApost.2.2.1⟩
      refine ⟨hnib, Or.inl hin_hp, hin_lim, ?_⟩
      intro n hn
      obtain ⟨_, hal_n, hin_n, hw_n, _⟩ := hm.2.2.2.2.1.1 n hn
      have hn_old_in : Inside (nodeIvl s n) sourceBase (globN s "heap_ptr") := by
        rcases hal_n with h1 | h2
        · exact h1
        · have : heapLimit ≤ scratchStart := by decide
          have hhi_lim : n + nodeSize (memW s n) ≤ heapLimit := hin_n.2
          have hlo_sp : globN s "scratch_ptr" ≤ n := h2.1
          have hsz_pos : 32 ≤ nodeSize (memW s n) := by unfold nodeSize; split_ifs <;> omega
          omega
      have hsz_n : 32 ≤ nodeSize (memW s n) := by unfold nodeSize; split_ifs <;> omega
      have hu_n : IvlUnhit s post (n, nodeSize (memW s n)) :=
        hext_unhit _ (by unfold nodeExtents; exact List.mem_flatMap.2 ⟨n, hn, by simp [nodeIvl]⟩) (by dsimp only; omega)
      have hhi_n : n + nodeSize (memW s n) ≤ 2 ^ 64 := by
        have : heapLimit ≤ 2 ^ 64 := by decide
        have : n + nodeSize (memW s n) ≤ heapLimit := hin_n.2
        omega
      have hwm : memW post n = memW s n :=
        memW_eq_of_ivlUnhit hu_n hw_n.1 hhi_n ⟨by omega, by omega⟩
      have hivl_eq : nodeIvl post n = nodeIvl s n := by simp [nodeIvl, hwm]
      rw [hivl_eq]
      exact Or.inr (Or.inr (Or.inr (Nat.le_trans hn_old_in.2 hin_fresh.1)))
  let res := setVarHOLFinite (ofString "nk") (.rStruct [.val (.word p), .val (.word l)]) { post with locals := s.locals }
  have hres_A : ArenaReady res := localsFree_arenaReady post _ _ hApost
  have hres_vlen : locN res "vlen" < 2 ^ 40 := by
    have : locN res "vlen" = locN s "vlen" := by
      simp [res, locN, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "nk" ≠ ofString "vlen" by decide]
    rw [this]; exact hvlen_lt
  have hres_m : locN res "m" = locN s "m" := by
    simp [res, locN, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "nk" ≠ ofString "m" by decide]
  have hres_nk : res.locals.lookup (ofString "nk") = some (.rStruct [.val (.word p), .val (.word l)]) := by
    simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  refine ⟨hres_A, hres_vlen, p, l, hres_nk, hl64, Nm, hNm_post, ?_, hkey_in⟩
  change RootIn Nm (memW post (locN res "m"))
  rw [hres_m, hm_memW]
  exact hm.2.2.2.2.2.1

private theorem root_dec_init {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (hs : AfterNk s)
    (hv : evalAt s (.load .one (.op .add [.var .local (ofString "m"), .const 0])) = some v) :
    AfterRoot (setVarHOLFinite (ofString "root") v s) := by
  obtain ⟨w, rfl, hw⟩ := evalAt_loadL s "m" 0 v hv
  obtain ⟨hA, hvlen, p, l, hnk, hl64, Nd, hNd, hroot, hkey⟩ := hs
  refine ⟨localsFree_arenaReady s _ _ hA, ?_, p, l, ?_, hl64, Nd, hNd, ?_, hkey⟩
  · rw [locN_setVar_ne s "vlen" (ofString "root") _ (by decide)]
    exact hvlen
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hnk,
      show ofString "root" ≠ ofString "nk" by decide]
  · rw [locN_setVar_same, hw]
    simpa using hroot

private theorem delete_entry :
    CallEntryOn AfterRoot MptReady (ofString "_mpt_delete_node")
      [.var .local (ofString "root"),
       .rfield 0 (.var .local (ofString "nk")),
       .rfield 1 (.var .local (ofString "nk")),
       .const 0] := by
  intro F s values body callee ret hcode hP hargs hl
  obtain ⟨hA, _, p, l, hnk, hl64, Nd, hNd, hroot, hkey⟩ := hP
  obtain ⟨v1, v2, v3, v4, he1, he2, he3, he4, hc1, hc2, hc3, hc4⟩ :=
    callee_param_four_exp s (ofString "_mpt_delete_node")
      (ofString "node") (ofString "key") (ofString "klen") (ofString "level")
      .one .one .one .one _ _ (by rw [hcode]; exact lookup__mpt_delete_node)
      _ _ _ _ values body callee ret hargs hl
  have he2' : v2 = .val (.word p) := by
    simp [evalAt, evalHOLExact, hnk] at he2; exact he2.symm
  have he3' : v3 = .val (.word l) := by
    simp [evalAt, evalHOLExact, hnk] at he3; exact he3.symm
  have he4' : v4 = .val (.word 0) := by
    simp [evalAt, evalHOLExact] at he4; exact he4.symm
  subst he2'; subst he3'; subst he4'
  have hnode : locN (callEntryStateHOLFinite s callee) "node" = locN s "root" := by
    simp only [evalAt, evalHOLExact] at he1
    simp only [locN, callEntryStateHOLFinite, hc1, he1]
  have hkey_loc : locN (callEntryStateHOLFinite s callee) "key" = p.toNat := by
    simp [locN, callEntryStateHOLFinite, hc2]
  have hklen_loc : locN (callEntryStateHOLFinite s callee) "klen" = l.toNat := by
    simp [locN, callEntryStateHOLFinite, hc3]
  have hlevel_loc : locN (callEntryStateHOLFinite s callee) "level" = 0 := by
    simp [locN, callEntryStateHOLFinite, hc4]
  refine ⟨localsFree_arenaReady s _ _ hA, ?_, Nd, hNd, ?_, ?_, ?_⟩
  · rw [hlevel_loc, hklen_loc]; omega
  · rw [hnode]; exact hroot
  · change KeyIn s Nd (locN (callEntryStateHOLFinite s callee) "key" + locN (callEntryStateHOLFinite s callee) "level")
      (locN (callEntryStateHOLFinite s callee) "klen" - locN (callEntryStateHOLFinite s callee) "level")
    rw [hkey_loc, hklen_loc, hlevel_loc, Nat.add_zero, Nat.sub_zero]
    exact hkey
  · rw [hklen_loc]; exact hl64

private theorem insert_entry :
    CallEntryOn AfterRoot MptInsertReady (ofString "_mpt_insert_node")
      [.var .local (ofString "root"),
       .rfield 0 (.var .local (ofString "nk")),
       .rfield 1 (.var .local (ofString "nk")),
       .const 0,
       .var .local (ofString "vptr"),
       .var .local (ofString "vlen")] := by
  intro F s values body callee ret hcode hP hargs hl
  obtain ⟨hA, hvlen, p, l, hnk, hl64, Nd, hNd, hroot, hkey⟩ := hP
  obtain ⟨v1, v2, v3, v4, v5, v6, he1, he2, he3, he4, _, he6, hc1, hc2, hc3, hc4, _, hc6⟩ :=
    callee_param_six_exp s (ofString "_mpt_insert_node")
      (ofString "node") (ofString "key") (ofString "klen") (ofString "level")
      (ofString "vptr") (ofString "vlen")
      .one .one .one .one .one .one _ _ (by rw [hcode]; exact lookup__mpt_insert_node)
      _ _ _ _ _ _ values body callee ret hargs hl
  have he2' : v2 = .val (.word p) := by
    simp [evalAt, evalHOLExact, hnk] at he2; exact he2.symm
  have he3' : v3 = .val (.word l) := by
    simp [evalAt, evalHOLExact, hnk] at he3; exact he3.symm
  have he4' : v4 = .val (.word 0) := by
    simp [evalAt, evalHOLExact] at he4; exact he4.symm
  subst he2'; subst he3'; subst he4'
  have hnode : locN (callEntryStateHOLFinite s callee) "node" = locN s "root" := by
    simp only [evalAt, evalHOLExact] at he1
    simp only [locN, callEntryStateHOLFinite, hc1, he1]
  have hkey_loc : locN (callEntryStateHOLFinite s callee) "key" = p.toNat := by
    simp [locN, callEntryStateHOLFinite, hc2]
  have hklen_loc : locN (callEntryStateHOLFinite s callee) "klen" = l.toNat := by
    simp [locN, callEntryStateHOLFinite, hc3]
  have hlevel_loc : locN (callEntryStateHOLFinite s callee) "level" = 0 := by
    simp [locN, callEntryStateHOLFinite, hc4]
  have hvlen_loc : locN (callEntryStateHOLFinite s callee) "vlen" = locN s "vlen" := by
    simp only [evalAt, evalHOLExact] at he6
    simp only [locN, callEntryStateHOLFinite, hc6, he6]
  refine ⟨⟨localsFree_arenaReady s _ _ hA, ?_, Nd, hNd, ?_, ?_, ?_⟩, ?_⟩
  · rw [hlevel_loc, hklen_loc]; omega
  · rw [hnode]; exact hroot
  · change KeyIn s Nd (locN (callEntryStateHOLFinite s callee) "key" + locN (callEntryStateHOLFinite s callee) "level")
      (locN (callEntryStateHOLFinite s callee) "klen" - locN (callEntryStateHOLFinite s callee) "level")
    rw [hkey_loc, hklen_loc, hlevel_loc, Nat.add_zero, Nat.sub_zero]
    exact hkey
  · rw [hklen_loc]; exact hl64
  · rw [hvlen_loc]; exact hvlen

theorem gbody_mpt_set_proof
    (hdel : TerminatingFunBoundedOn MptReady (ofString "_mpt_delete_node") K.«_mpt_delete_node»)
    (hins : TerminatingFunBoundedOn MptInsertReady (ofString "_mpt_insert_node") K.«_mpt_insert_node»)
    (hnk_fb : TerminatingFunBoundedOn GuestInv (ofString "mpt_nibble_key") K.«mpt_nibble_key»)
    (hww : WritesWithin (fun s => [(globN s "keccak_pad", 136), (globN s "keccak_st", 200), (globN s "mpt_hash_scratch", 40)])
      ["heap_ptr"] (ofString "mpt_nibble_key"))
    (hnk : RetNibbles (ofString "mpt_nibble_key")) :
    TerminatingFunBoundedOn MptSetReady (ofString "mpt_set") K.«mpt_set» := by
  refine ⟨_, _, _, lookup_mpt_set, ?_⟩
  simp only [sourceFunctionEntry, Guest.Software.guestFn_mpt_set,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.decCall_on hnk_fb _ _ _
      (callEntryOn_of_imp localsFree_guestInv (fun s h => h.1.1.1) _ _)
      (nk_resume hww hnk)
      (dec_guard _ _ _ root_dec_init
        (TerminatingProgBoundedOn.seq_guestInv_after
          (TerminatingProgBoundedOn.ite_on
            (TerminatingProgBoundedOn.call_on hdel _ _ delete_entry)
            (TerminatingProgBoundedOn.call_on hins _ _ insert_entry))
          (fun s h => h.1.1)
          (TerminatingProgBoundedOn.seq_guestInv
            (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
            (TerminatingProgBoundedOn.of_clock (fun s => clock_return s _)))))) ?_
  unfold K.«mpt_set»
  simp only [Nat.max_def]
  split <;> omega

end InitECandidate.Solver.Wave8GuestInv.P3MptSet
