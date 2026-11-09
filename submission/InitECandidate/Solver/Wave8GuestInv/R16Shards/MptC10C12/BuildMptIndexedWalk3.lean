import InitECandidate.Solver.Wave8GuestInv.R16Shards.MptC10C12.BuildMptIndexedWalk2
import InitECandidate.Solver.Wave8GuestInv.R16Shards.PayloadWorldHelpers
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestUniformClockBound
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc
open InitECandidate.Solver.Wave8GuestInv.Fast_C08WkShard03
namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.MptC10C12
set_option linter.unusedVariables false
private def BmiAfterNewStrong : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => BuildMptAfterNew s ∧ BmiWkInvE s
private theorem decCallResume_heap_mark_bmi_strong
    (hro : ReadOnlyFn (ofString "heap_mark")) :
    DecCallResumeOn BuildMptIndexedReadyStrong
      (fun s => BuildMptAfterMark s ∧ BmiAfterMarkC s)
      (ofString "mark") (ofString "heap_mark") [] := by
  intro F state values body callee ret value post hcode hP hargs hl hrun
  exact ⟨decCallResume_heap_mark_bmi hro state values body callee ret value post
      hcode hP.1 hargs hl hrun,
    decCallResume_heap_mark_bmi2 hro state values body callee ret value post
      hcode (strong_bmiReadyG hP) hargs hl hrun⟩
private theorem decCallResume_mpt_new_bmi_strong
    (hwk : WorldKeeps WorldOK (fun _ => [])
      ["heap_ptr"] R10Shards.P26_P28.stdKeep
      (RetAvoids (fun _ _ w => [(w, 16)])) (ofString "mpt_new"))
    (hrt : Returns ArenaReady (fun s post m => FreshBlock s post m 16 ∧
      memW post m = locN s "root_node" ∧ memW post (m + 8) = locN s "secured")
      (ofString "mpt_new")) :
    DecCallResumeOn (fun s => BuildMptAfterMark s ∧ BmiAfterMarkC s) BmiAfterNewStrong
      (ofString "m") (ofString "mpt_new") [.const 0, .const 0] := by
  intro F state values body callee ret value post hcode hP hargs hl hrun
  exact ⟨decCallResume_mpt_new_bmi hwk hrt state values body callee ret value post
      hcode hP.1 hargs hl hrun,
    decCallResume_mpt_new_bmi2w hwk hrt state values body callee ret value post
      hcode hP.2 hargs hl hrun⟩
private theorem bmiAfterNewStrong_set_counter_loopInv2 {F : Type}
    {s : PanSemStateFiniteExact 64 F} (h : BmiAfterNewStrong s) (w : BitVec 64) :
    BuildMptLoopInv2 (setVarHOLFinite (ofString "i") (.val (.word w)) s) := by
  obtain ⟨hweak, s0, S0, Nd0, hw⟩ := h
  set t := setVarHOLFinite (ofString "i") (.val (.word w)) s
  have hloop : BuildMptLoopInv t := buildMptAfterNew_set_counter hweak w
  have hmark_s : locN s "mark" = locN s0 "mark" := hw.2.1
  have hm_s : locN s "m" = locN s0 "mark" := hw.2.2.1
  have hn_s : locN s "n" = locN s0 "n" := hw.2.2.2.2.2.1
  have hsa_s : locN s "slice_arr" = locN s0 "slice_arr" := hw.2.2.2.2.2.2.1
  obtain ⟨S, Nd, Nm, hWT, hmObj, _, hdN, _, hdSlice, _⟩ :=
    hw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hloc : ∀ name : String, ofString name ≠ ofString "i" → locN t name = locN s name :=
    fun name hne => locN_setVar_ne s name (ofString "i") (.val (.word w)) hne
  refine ⟨hloop, ?_, S, Nd, Nm,
    (worldTypedWith_build_locals s t.locals t.clock S Nd).2 hWT, ?_, ?_, ?_⟩
  · rw [hloc "mark" (by decide), hloc "m" (by decide), hmark_s, hm_s]
  · rw [hloc "m" (by decide), hm_s]
    exact hmObj
  · rw [hloc "m" (by decide), hm_s]
    exact hdN
  · rw [hloc "slice_arr" (by decide), hloc "n" (by decide), hloc "m" (by decide),
      hsa_s, hn_s, hm_s]
    exact hdSlice
private abbrev bmiSetR {F : Type} (t : PanSemStateFiniteExact 64 F) : List Ivl :=
  [bufferRegion t ("keccak_pad", 136), bufferRegion t ("keccak_st", 200),
    bufferRegion t ("mpt_hash_scratch", 40)]
private abbrev bmiSetRC11 {F : Type} (s : PanSemStateFiniteExact 64 F) : List Ivl :=
  [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
   (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
   (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40)]
private theorem bmiSetRC11_eq {F : Type} (s : PanSemStateFiniteExact 64 F) :
    bmiSetRC11 s = bmiSetR s := by
  have e1 : (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136) =
      bufferRegion s ("keccak_pad", 136) := by
    unfold bufferRegion; split_ifs with h <;> simp_all
  have e2 : (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200) =
      bufferRegion s ("keccak_st", 200) := by
    unfold bufferRegion; split_ifs with h <;> simp_all
  have e3 : (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40) =
      bufferRegion s ("mpt_hash_scratch", 40) := by
    unfold bufferRegion; split_ifs with h <;> simp_all
  simp only [bmiSetRC11, bmiSetR, e1, e2, e3]
private theorem mptObjStep_c11_to_bmiSetR {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (h : MptObjStep bmiSetRC11 ["heap_ptr", "scratch_ptr"] R10Shards.P26_P28.stdKeep s post) :
    MptObjStep bmiSetR ["heap_ptr", "scratch_ptr"] R10Shards.P26_P28.stdKeep s post := by
  refine ⟨h.1, h.2.1, h.2.2.1, ?_, ?_⟩
  · intro r hr hnz k hk hno
    refine h.2.2.2.1 r hr hnz k hk (fun i hi => ?_)
    have hi' : i ∈ bmiSetR s := by
      change i ∈ bmiSetRC11 s at hi
      rwa [bmiSetRC11_eq s] at hi
    exact hno i hi'
  · intro S Nd Nm hWT hm hd hR
    refine h.2.2.2.2 S Nd Nm hWT hm ?_ ?_
    · change IvlsDisj ((locN s "m", 16) :: bmiSetRC11 s ++ nodeExtents s Nm) (nodeExtents s Nd)
      rw [bmiSetRC11_eq s]; exact hd
    · change IvlsDisj (bmiSetRC11 s) (worldTypedIvls s S Nd ++ mptObjIvls s Nm (locN s "m"))
      rw [bmiSetRC11_eq s]; exact hR
private theorem bmiSetR_in_globalBuffers {F : Type} (s : PanSemStateFiniteExact 64 F) :
    ∀ i ∈ bmiSetR s, ∃ gn ∈ globalBuffers,
      gn.1 ∉ typedRecords.map Prod.fst ∧ i = bufferRegion s gn := by
  intro i hi
  simp only [bmiSetR, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl
  · exact ⟨("keccak_pad", 136), by decide, by decide, rfl⟩
  · exact ⟨("keccak_st", 200), by decide, by decide, rfl⟩
  · exact ⟨("mpt_hash_scratch", 40), by decide, by decide, rfl⟩
private theorem buildMptLoopInv2_decClock {F : Type}
    {s : PanSemStateFiniteExact 64 F} (h : BuildMptLoopInv2 s) :
    BuildMptLoopInv2 (decClockHOLFinite s) := by
  simpa [decClockHOLFinite] using
    localsOnly_buildMptLoopInv2 s s.locals (s.clock - 1) (fun _ _ => rfl) h
private theorem bmi3_cov_of_right {i j : Ivl} (hr : i.1 + i.2 ≤ j.1) : BmiCov i j := by
  intro a _ ha2 ⟨hc1, _⟩
  omega
private theorem bmi3_cov_of_disj_z0 {i j : Ivl} (hd : Disj i j) (hz0 : j.2 = 0 → j.1 = 0) :
    BmiCov i j := by
  by_cases hz : j.2 = 0
  · have h1 : j.1 = 0 := hz0 hz
    intro a _ _ ⟨_, hc2⟩
    omega
  · exact bmi_cov_of_disj hd hz
private theorem bmi3_gb_snd_ne (gs : String × Nat) (hg : gs ∈ globalBuffers) : gs.2 ≠ 0 := by
  unfold globalBuffers at hg
  simp only [List.mem_cons, List.not_mem_nil] at hg
  repeat (first
    | exact hg.elim
    | (rcases hg with rfl | hg)
    | exact (by decide))
private theorem bmi3_lst_zero {F : Type} (s : PanSemStateFiniteExact 64 F) (l esz : Nat)
    {j : Ivl} (hj : j ∈ lstObjects s l esz) (h0 : j.2 = 0) : j.1 = 0 := by
  unfold lstObjects at hj
  split at hj
  · rcases List.mem_cons.mp hj with rfl | hj
    · rfl
    · rcases List.mem_cons.mp hj with rfl | hj
      · rfl
      · exact absurd hj (by simp)
  · rcases List.mem_cons.mp hj with rfl | hj
    · exact absurd h0 (by simp)
    · rcases List.mem_cons.mp hj with rfl | hj
      · have hcap : esz * memW s (l + 16) = 0 := h0
        show (if esz * memW s (l + 16) = 0 then (0 : Nat) else memW s l) = 0
        rw [if_pos hcap]
      · exact absurd hj (by simp)
private theorem bmi3_obj_zero (bo p len : Nat)
    (h0 : ((if bo = 0 ∨ p = 0 ∨ len = 0 then (0, 0) else (p, len)) : Ivl).2 = 0) :
    ((if bo = 0 ∨ p = 0 ∨ len = 0 then (0, 0) else (p, len)) : Ivl).1 = 0 := by
  split at h0
  · rename_i hb
    rw [if_pos hb]
  · rename_i hb
    exact absurd h0 (fun hc => hb (Or.inr (Or.inr hc)))
private theorem bmi3_fixed_zero {F : Type} (s : PanSemStateFiniteExact 64 F)
    {j : Ivl} (hj : j ∈ fixedObjects s) (h0 : j.2 = 0) : j.1 = 0 := by
  unfold fixedObjects at hj
  simp only [List.mem_append] at hj
  rcases hj with ((hj | hj) | hj) | hbal
  · obtain ⟨gn, hgn, rfl⟩ := List.mem_map.mp hj
    by_cases hz : globN s gn.1 = 0
    · exact hz
    · rw [if_neg hz] at h0
      have h2 : gn.2 = 0 := h0
      exact absurd h2 (bmi3_gb_snd_ne gn hgn)
  · rcases List.mem_cons.mp hj with rfl | hj
    · have hc : 32 * globN s "journal_cap" = 0 := h0
      have hz : globN s "journal_cap" = 0 := by omega
      rw [if_pos hz]
    · exact absurd hj (by simp)
  · unfold blockOutObjects at hj
    simp only [List.mem_append] at hj
    rcases hj with (hj | hj) | hj
    · rcases List.mem_cons.mp hj with rfl | hj
      · exact bmi3_obj_zero _ _ _ h0
      · rcases List.mem_cons.mp hj with rfl | hj
        · exact bmi3_obj_zero _ _ _ h0
        · rcases List.mem_cons.mp hj with rfl | hj
          · exact bmi3_obj_zero _ _ _ h0
          · exact absurd hj (by simp)
    · split at hj
      · rcases List.mem_cons.mp hj with rfl | hj
        · rfl
        · rcases List.mem_cons.mp hj with rfl | hj
          · rfl
          · exact absurd hj (by simp)
      · rcases List.mem_cons.mp hj with rfl | hj
        · exact bmi3_obj_zero _ _ _ h0
        · rcases List.mem_cons.mp hj with rfl | hj
          · exact bmi3_obj_zero _ _ _ h0
          · exact absurd hj (by simp)
    · split at hj
      · rcases List.mem_cons.mp hj with rfl | hj
        · rfl
        · rcases List.mem_cons.mp hj with rfl | hj
          · rfl
          · exact absurd hj (by simp)
      · rcases List.mem_cons.mp hj with rfl | hj
        · exact bmi3_obj_zero _ _ _ h0
        · rcases List.mem_cons.mp hj with rfl | hj
          · exact bmi3_obj_zero _ _ _ h0
          · exact absurd hj (by simp)
  · obtain ⟨ad, _, hj⟩ := List.mem_flatMap.mp hbal
    rcases List.mem_cons.mp hj with rfl | hj
    · exact absurd h0 (by simp)
    · rcases List.mem_append.mp hj with hj | hj
      · rcases List.mem_append.mp hj with hj | hj
        · rcases List.mem_append.mp hj with hj | hj
          · exact bmi3_lst_zero s _ 40 hj h0
          · exact bmi3_lst_zero s _ 16 hj h0
        · exact bmi3_lst_zero s _ 24 hj h0
      · obtain ⟨l, _, hj⟩ := List.mem_flatMap.mp hj
        exact bmi3_lst_zero s l 40 hj h0
private theorem bmi3_nodeExtents_zero {F : Type} (s : PanSemStateFiniteExact 64 F) (Ns : List Nat)
    {j : Ivl} (hj : j ∈ nodeExtents s Ns) (h0 : j.2 = 0) : j.1 = 0 := by
  obtain ⟨n, _, hjn⟩ := List.mem_flatMap.mp hj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hjn
  rcases hjn with rfl | rfl
  · exfalso
    dsimp only [nodeIvl, nodeSize] at h0
    split at h0
    · omega
    · split at h0
      · omega
      · split at h0 <;> omega
  · dsimp only [nodePath] at h0 ⊢
    split at h0
    · rename_i hc
      exact absurd h0 hc.2
    · rename_i hc
      rw [if_neg hc]
private theorem bmi3_htabFp_nz {F : Type} {s : PanSemStateFiniteExact 64 F} {t : Nat}
    (hwf : HtabWF s t) {j : Ivl} (hj : j ∈ htabFootprint s t) : j.2 ≠ 0 := by
  have hk1 : 1 ≤ hdr s t 0 := hwf.2.2.1
  have hst : hdr s t 1 = (hdr s t 0 + 7) / 8 * 8 := hwf.2.2.2.2.1
  have hnc : 2 ≤ hdr s t 10 := hwf.2.2.2.2.2.1
  simp only [htabFootprint, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl
  · dsimp only; omega
  · dsimp only; rw [hst]
    have h1 : 8 ≤ (hdr s t 0 + 7) / 8 * 8 := by omega
    have h2 : 3 ≤ hdr s t 10 + 1 := by omega
    exact ne_of_gt (Nat.mul_pos (by omega) (by omega))
  · dsimp only; omega
  · dsimp only; omega
private theorem bmi3_owned_mpt_zero {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd Nm : List Nat} (hWT : WorldTypedWith s S Nd) {m : Nat}
    {j : Ivl} (hj : j ∈ worldOwned s S Nd ++ mptObjIvls s Nm m) (h0 : j.2 = 0) : j.1 = 0 := by
  rcases List.mem_append.mp hj with hj | hj
  · unfold worldOwned at hj
    rcases List.mem_append.mp hj with hj | hj
    · rcases List.mem_append.mp hj with hj | hj
      · obtain ⟨t, ht, hjt⟩ := List.mem_flatMap.mp hj
        exact absurd h0 (bmi3_htabFp_nz (hWT.1.2.1 t ht).1 hjt)
      · exact bmi3_fixed_zero s hj h0
    · exact bmi3_nodeExtents_zero s Nd hj h0
  · rcases List.mem_cons.mp hj with rfl | hj
    · exact absurd h0 (by simp)
    · exact bmi3_nodeExtents_zero s Nm hj h0
private theorem bmi3_buf_zero {F : Type} (s : PanSemStateFiniteExact 64 F)
    (gn : String × Nat) (hsz : gn.2 ≠ 0) (h0 : (bufferRegion s gn).2 = 0) :
    (bufferRegion s gn).1 = 0 := by
  by_cases hz : globN s gn.1 = 0
  · simp [bufferRegion, hz]
  · simp [bufferRegion, hz] at h0
    exact absurd h0 hsz
private theorem bmi3_loopInv2_after_mptSet {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)}
    (h : BuildMptLoopInv2 s)
    (hm_callee : callee.lookup (ofString "m") = s.locals.lookup (ofString "m"))
    (hstep : MptObjStep bmiSetR ["heap_ptr", "scratch_ptr"] R10Shards.P26_P28.stdKeep
      (callEntryStateHOLFinite s callee) post) :
    BuildMptLoopInv2 { post with locals := s.locals } := by
  obtain ⟨hloop, hmm, S, Nd, Nm, hWT, hmObj, hdN, hdW⟩ := h
  obtain ⟨hready, hinv, hin_mark, hmark_le, hlocs⟩ := hloop
  let t : PanSemStateFiniteExact 64 F := { post with locals := s.locals }
  have hstep_c : MptObjStep bmiSetR ["heap_ptr", "scratch_ptr"] R10Shards.P26_P28.stdKeep s t :=
    mptSetStep_caller_bmi hm_callee hstep
  have hcross_s : IvlsDisj ((locN s "m", 16) :: bmiSetR s ++ nodeExtents s Nm)
      (nodeExtents s Nd) := by
    intro o ho j hj
    rcases List.mem_cons.mp ho with rfl | ho
    · exact hdN _ (by simp) j hj
    · rcases List.mem_append.mp ho with ho | ho
      · obtain ⟨gn, hg, hu, rfl⟩ := bmiSetR_in_globalBuffers s o ho
        exact bufferRegion_disj hWT gn hg hu j (by
          simp only [worldTypedIvls, List.mem_append]
          exact Or.inr hj)
      · exact hdN o (List.mem_cons_of_mem _ ho) j hj
  have hR_s : IvlsDisj (bmiSetR s) (worldTypedIvls s S Nd ++ mptObjIvls s Nm (locN s "m")) := by
    intro o ho j hj
    obtain ⟨gn, hg, hu, rfl⟩ := bmiSetR_in_globalBuffers s o ho
    rcases List.mem_append.mp hj with hj | hj
    · exact bufferRegion_disj hWT gn hg hu j hj
    · apply Disj.flip
      have hf : bufferRegion s gn ∈ fixedObjects s :=
        List.mem_append.mpr (Or.inl (List.mem_append.mpr
          (Or.inl (List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨gn, hg, rfl⟩))))))
      rcases List.mem_cons.mp hj with rfl | hj
      · exact hmObj.2.2.2.1 _ hf
      · exact (hmObj.2.2.2.2.2.2 j hj).2.2 _ hf
  obtain ⟨S', Nd', Nm', _, hWT', hmObj', hdN', hog, hfr⟩ :=
    hstep_c.2.2.2.2 S Nd Nm hWT hmObj hcross_s hR_s
  have hW_t : WorldOK t := ⟨hstep_c.1, S', (worldTyped_iff_with t S').2 ⟨Nd', hWT'⟩⟩
  have hinv_t : BuildMptInv t :=
    ⟨hstep_c.1, ⟨hinv.2.1.1, hinv.2.1.2.trans hstep_c.2.1⟩, S', Nd', Nm', hWT', hmObj', hdN'⟩
  have hbuf_t : ∀ gn ∈ ([("mpt_hash_scratch", 40), ("mpt_key_scratch", 16),
      ("keccak_pad", 136), ("keccak_st", 200)] : List (String × Nat)),
      bufferRegion t gn = bufferRegion s gn := by
    intro gn hgn
    have hgk : s.globals.lookup (ofString gn.1) = t.globals.lookup (ofString gn.1) := by
      apply hstep_c.2.2.1 (ofString gn.1)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hgn
      rcases hgn with rfl | rfl | rfl | rfl <;> decide
    have hglob : globN t gn.1 = globN s gn.1 := by
      simp only [globN, ← hgk]
    simp [bufferRegion, hglob]
  have hcov_keep : ∀ j ∈ worldOwned s S Nd ++ mptObjIvls s Nm (locN s "m") ++
      bmiSetR s ++ [freeGap s],
      BmiCov (locN s "slice_arr", 16 * locN s "n") j := by
    intro j hj
    rcases List.mem_append.mp hj with hj | hj
    · rcases List.mem_append.mp hj with hj | hj
      · exact bmi3_cov_of_disj_z0 (hdW _ (by simp) j hj)
          (bmi3_owned_mpt_zero hWT hj)
      · have hj' : j ∈ ([("mpt_hash_scratch", 40), ("mpt_key_scratch", 16),
            ("keccak_pad", 136), ("keccak_st", 200)].map (bufferRegion s)) := by
          simp only [bmiSetR, List.mem_cons, List.not_mem_nil, or_false] at hj
          rcases hj with rfl | rfl | rfl <;> simp
        exact bmi3_cov_of_disj_z0 (hready.2.2.2.2.2.1 _ (by simp) j hj') (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
          rcases hj with rfl | rfl | rfl <;>
            exact bmi3_buf_zero s _ (by decide))
    · simp only [List.mem_singleton] at hj
      subst j
      apply bmi3_cov_of_right
      have h1 := hin_mark.2
      have h2 := hready.1.1.2.2.1
      have h3 := hready.1.1.2.2.2.1
      have : heapLimit ≤ scratchStart := by decide
      dsimp only [freeGap]
      omega
  have hcov_fresh : BmiCov (locN s "slice_arr", 16 * locN s "n") (heapFree s) := by
    apply bmi3_cov_of_right
    have h1 := hin_mark.2
    dsimp only [heapFree]
    omega
  have hu : P3MptSet.IvlUnhit s t (locN s "slice_arr", 16 * locN s "n") :=
    bmi_unhit_of_cov hfr hcov_keep hcov_fresh hready.2.2.2.2.1.1 (by omega)
  have hready_t : BuildMptIndexedReady t :=
    buildMptIndexedReady_of_unhit hready hW_t (fun _ _ => rfl) hstep_c.2.1 hbuf_t hu
  have hdW_t : IvlsDisj [(locN t "slice_arr", 16 * locN t "n")]
      (worldOwned t S' Nd' ++ mptObjIvls t Nm' (locN t "m")) := by
    intro sl hsl o ho
    simp only [List.mem_singleton] at hsl
    subst sl
    change Disj (locN s "slice_arr", 16 * locN s "n") o
    rcases hog o ho with rfl | ⟨j, hj, hinj⟩ | hfresh
    · exact Or.inr (Or.inl rfl)
    · rcases hdW (locN s "slice_arr", 16 * locN s "n") (by simp) j hj with h0 | hj0 | hleft | hright
      · exact Or.inl h0
      · exact Or.inr (Or.inl (by
          have h1 : j.1 ≤ o.1 := hinj.1
          have h2 : o.1 + o.2 ≤ j.1 + j.2 := hinj.2
          omega))
      · exact Or.inr (Or.inr (Or.inl (by
          have h1 : j.1 ≤ o.1 := hinj.1
          change locN s "slice_arr" + 16 * locN s "n" ≤ j.1 at hleft
          change locN s "slice_arr" + 16 * locN s "n" ≤ o.1
          omega)))
      · exact Or.inr (Or.inr (Or.inr (by
          have h2 : o.1 + o.2 ≤ j.1 + j.2 := hinj.2
          change j.1 + j.2 ≤ locN s "slice_arr" at hright
          change o.1 + o.2 ≤ locN s "slice_arr"
          omega)))
    · exact Or.inr (Or.inr (Or.inl (by
        have h1 : locN s "slice_arr" + 16 * locN s "n" ≤ locN s "mark" := hin_mark.2
        have h2 : globN s "heap_ptr" ≤ o.1 := hfresh.1
        change locN s "slice_arr" + 16 * locN s "n" ≤ o.1
        omega)))
  exact ⟨⟨hready_t, hinv_t, hin_mark, hmark_le.trans hstep_c.2.1, hlocs⟩,
    hmm, S', Nd', Nm', hWT', hmObj', hdN', hdW_t⟩
private abbrev bmiSetArgs : List (ExpHOL 64) :=
  [.var .local (ofString "m"),
   .var .global (ofString "mpt_key_scratch"),
   .var .local (ofString "klen"),
   .load .one (.op .add [.var .local (ofString "slice_arr"),
     .panop .mul [.var .local (ofString "i"), .const 16]]),
   .load .one (.op .add [.var .local (ofString "slice_arr"),
     .panop .mul [.var .local (ofString "i"), .const 16],
     .const 8])]
private theorem callEntryOn_mpt_set_bmi3 :
    CallEntryOn (fun s => BuildMptLoopInv2 s ∧ locN s "klen" ≤ 32 ∧ locN s "i" < locN s "n")
      MptSetReady (ofString "mpt_set") bmiSetArgs := by
  intro F s values body callee ret hcode hP hargs hl
  obtain ⟨hP2, hklen_le, hlt⟩ := hP
  obtain ⟨hready, hinv, _, _, hlocs⟩ := hP2.1
  obtain ⟨v1, v2, v3, v4, v5, he1, he2, he3, he4, he5, hc1, hc2, hc3, hc4, hc5⟩ :=
    callee_param_five_exp s (ofString "mpt_set")
      (ofString "m") (ofString "key") (ofString "klen") (ofString "vptr") (ofString "vlen")
      .one .one .one .one .one _ _
      (by rw [hcode]; exact P3MptSet.lookup_mpt_set)
      _ _ _ _ _ values body callee ret hargs hl
  have hm : callee.lookup (ofString "m") = s.locals.lookup (ofString "m") :=
    hc1.trans (by simpa only [evalAt, evalHOLExact] using he1.symm)
  have hklen : callee.lookup (ofString "klen") = s.locals.lookup (ofString "klen") :=
    hc3.trans (by simpa only [evalAt, evalHOLExact] using he3.symm)
  obtain ⟨_, hsl8⟩ := evalAt_slice_word_bmi s
    (hready.2.1 "slice_arr" (by simp))
    (hlocs "i" (by simp))
    hlt hready.2.2.2.1 hready.1.1 hready.2.2.2.2.1
  obtain ⟨wvlen, rfl, hwvlen⟩ := hsl8 v5 he5
  let entry := callEntryStateHOLFinite s callee
  have hinv_e : BuildMptInv entry :=
    localsOnly_buildMptInv s callee (s.clock - 1)
      (fun name hname => by
        simp only [List.mem_singleton] at hname
        subst name
        exact hm) hinv
  have hklen_e : locN entry "klen" ≤ 32 := by
    have : locN entry "klen" = locN s "klen" := by
      simp only [entry, callEntryStateHOLFinite, locN, hklen]
    omega
  have hvlen_e : locN entry "vlen" < 2 ^ 40 := by
    have : locN entry "vlen" = wvlen.toNat := by
      simp [entry, callEntryStateHOLFinite, locN, hc5]
    rw [this, hwvlen]
    exact hready.2.2.2.2.2.2 (locN s "i") hlt
  exact buildMptInv_mptSetReady hinv_e hklen_e hvlen_e
private abbrev bmiLoopCond : ExpHOL 64 :=
  .cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))
private abbrev bmiLoopBody : ProgHOL 64 :=
  .decCall (ofString "klen") .one (ofString "rlp_encode_word")
    [.var .global (ofString "mpt_key_scratch"), .var .local (ofString "i")]
    (.seq
      (.call (some (none, none)) (ofString "mpt_set") bmiSetArgs)
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])))
private theorem bmi3_loop_body_bound
    (hrlp : TerminatingFunBoundedOn GuestInv (ofString "rlp_encode_word") K.«rlp_encode_word»)
    (hset : TerminatingFunBoundedOn MptSetReady (ofString "mpt_set") K.«mpt_set»)
    (hwk_rlp : WorldKeeps WorldOK (fun s => [(locN s "dst", 9)])
      [] R10Shards.P26_P28.stdKeep NoExtra (ofString "rlp_encode_word")) :
    TerminatingProgBoundedOn
      (fun s => BuildMptLoopInv2 s ∧ LoopActive bmiLoopCond s)
      bmiLoopBody
      ((K.«rlp_encode_word» + 1) + (K.«mpt_set» + 1)) := by
  refine TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.decCall_on hrlp (ofString "klen") .one
      [.var .global (ofString "mpt_key_scratch"), .var .local (ofString "i")]
      (callEntryOn_of_imp (P := fun s => BuildMptLoopInv2 s ∧ LoopActive bmiLoopCond s)
        localsFree_guestInv (fun _ h => h.1.1.1.1.1.1) _ _)
      (bmi_rlp_resume_strong hwk_rlp)
      (TerminatingProgBoundedOn.seq_guestInv_after
        (TerminatingProgBoundedOn.call_on hset none bmiSetArgs callEntryOn_mpt_set_bmi3)
        (fun _ h => h.1.1.1.1.1.1)
        (TerminatingProgBoundedOn.of_clock (fun s => clock_assign s _ _ _))))
    (by omega)
private theorem bmi3_loop_body_step_core
    (hmk_set : MptKeeps MptSetReady bmiSetRC11 ["heap_ptr", "scratch_ptr"]
      R10Shards.P26_P28.stdKeep (ofString "mpt_set"))
    (hwk_rlp : WorldKeeps WorldOK (fun s => [(locN s "dst", 9)])
      [] R10Shards.P26_P28.stdKeep NoExtra (ofString "rlp_encode_word"))
    {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode)
    (hP : BuildMptLoopInv2 s)
    (hact : LoopActive bmiLoopCond s)
    (hflow : (evaluateHOLFiniteState s bmiLoopBody).1 = none ∨
      (evaluateHOLFiniteState s bmiLoopBody).1 = some .continue) :
    BuildMptLoopInv2 (evaluateHOLFiniteState s bmiLoopBody).2 ∧
      buildMptLoopRank (evaluateHOLFiniteState s bmiLoopBody).2 < buildMptLoopRank s := by
  rcases hrun : evaluateHOLFiniteState s bmiLoopBody with ⟨r, post⟩
  rw [hrun] at hflow
  dsimp only at hflow ⊢
  have hnone : r = none := by
    have hrun0 := hrun
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hrun0
    rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        [.var .global (ofString "mpt_key_scratch"), .var .local (ofString "i")] with _ | values
    · rw [hargs] at hrun0; obtain ⟨rfl, _⟩ := Prod.mk.inj hrun0; simp at hflow
    · rw [hargs] at hrun0; dsimp only at hrun0
      rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "rlp_encode_word") values with
        _ | ⟨b1, c1, ret1⟩
      · rw [hl] at hrun0; obtain ⟨rfl, _⟩ := Prod.mk.inj hrun0; simp at hflow
      · rw [hl] at hrun0; dsimp only at hrun0
        by_cases hz : s.clock = 0
        · rw [if_pos hz] at hrun0; obtain ⟨rfl, _⟩ := Prod.mk.inj hrun0; simp at hflow
        · rw [if_neg hz] at hrun0
          rcases hb1 : evaluateHOLFiniteState (callEntryStateHOLFinite s c1) b1 with ⟨br1, bp1⟩
          rw [hb1] at hrun0
          cases br1 with
          | none => obtain ⟨rfl, _⟩ := Prod.mk.inj hrun0; simp at hflow
          | some br1' =>
            cases br1' with
            | returned v1 =>
              dsimp only at hrun0
              split at hrun0
              · set u := setVarHOLFinite (ofString "klen") v1 { bp1 with locals := s.locals }
                rcases hcu : evaluateHOLFiniteState u
                    (.seq (.call (some (none, none)) (ofString "mpt_set") bmiSetArgs)
                      (.assign .local (ofString "i")
                        (.op .add [.var .local (ofString "i"), .const 1]))) with ⟨cr, cp⟩
                rw [hcu] at hrun0
                obtain ⟨rfl, _⟩ := Prod.mk.inj hrun0
                rcases hflow with h | h
                · exact h
                · rw [evaluateHOLFiniteState_seq_line780] at hcu
                  rcases hc2 : evaluateHOLFiniteState u
                      (.call (some (none, none)) (ofString "mpt_set") bmiSetArgs) with ⟨r2, m2⟩
                  rw [hc2] at hcu
                  cases r2 with
                  | none =>
                    dsimp only at hcu
                    rw [evaluateHOLFiniteState_assign] at hcu
                    repeat' split at hcu
                    all_goals (obtain ⟨rfl, _⟩ := Prod.mk.inj hcu; simp at h)
                  | some r2' =>
                    dsimp only at hcu
                    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hcu
                    dsimp only at h ⊢
                    rw [evaluateHOLFiniteState_call] at hc2
                    rcases ha2 : evalListHOLFinite u
                        (h := fun a => Classical.propDecidable (u.memaddrs a)) bmiSetArgs with
                      _ | vs2
                    · rw [ha2] at hc2; dsimp only at hc2
                      have heq := (Prod.mk.inj hc2).1; rw [← heq] at h; simp at h
                    · rw [ha2] at hc2; dsimp only at hc2
                      rcases hl2 : lookupCodeHOLFinite u.code.lookup (ofString "mpt_set") vs2 with
                        _ | ⟨b2, c2, ret2⟩
                      · rw [hl2] at hc2; dsimp only at hc2
                        have heq := (Prod.mk.inj hc2).1; rw [← heq] at h; simp at h
                      · rw [hl2] at hc2; dsimp only at hc2
                        split at hc2
                        · have heq := (Prod.mk.inj hc2).1; rw [← heq] at h; simp at h
                        · rcases hb2 : evaluateHOLFiniteState (callEntryStateHOLFinite u c2) b2 with
                            ⟨br2, bp2⟩
                          rw [hb2] at hc2
                          cases br2 with
                          | none =>
                            dsimp only at hc2
                            have heq := (Prod.mk.inj hc2).1; rw [← heq] at h; simp at h
                          | some br2' =>
                            cases br2' with
                            | returned v2 =>
                              dsimp only at hc2
                              split at hc2 <;>
                                (have heq := (Prod.mk.inj hc2).1; rw [← heq] at h; simp at h)
                            | _ =>
                              dsimp only [emptyLocalsHOLFinite] at hc2
                              have heq := (Prod.mk.inj hc2).1; rw [← heq] at h; simp at h
              · obtain ⟨rfl, _⟩ := Prod.mk.inj hrun0; simp at hflow
            | _ => simp [emptyLocalsHOLFinite] at hrun0; obtain ⟨rfl, _⟩ := hrun0; simp at hflow
  subst hnone
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hrun
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .global (ofString "mpt_key_scratch"), .var .local (ofString "i")] with _ | values
  · rw [hargs] at hrun; simp at hrun
  · rw [hargs] at hrun; dsimp only at hrun
    rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "rlp_encode_word") values with
      _ | ⟨b1, c1, ret1⟩
    · rw [hl] at hrun; simp at hrun
    · rw [hl] at hrun; dsimp only at hrun
      by_cases hz : s.clock = 0
      · rw [if_pos hz] at hrun; simp at hrun
      · rw [if_neg hz] at hrun
        have hmeta1 := (evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s c1) b1).1
        rcases hb1 : evaluateHOLFiniteState (callEntryStateHOLFinite s c1) b1 with ⟨br1, bp1⟩
        rw [hb1] at hrun hmeta1
        dsimp only at hmeta1
        cases br1 with
        | none => simp at hrun
        | some br1' =>
          cases br1' with
          | returned v1 =>
            dsimp only at hrun
            split at hrun
            · set u := setVarHOLFinite (ofString "klen") v1 { bp1 with locals := s.locals }
              have hu_inv : BuildMptLoopInv2 u ∧ locN u "klen" ≤ 32 ∧ locN u "i" < locN u "n" :=
                bmi_rlp_resume_strong hwk_rlp s values b1 c1 ret1 v1 bp1
                  hcode ⟨hP, hact⟩ hargs hl hb1
              have hu_code : u.code = originalRuntimeCode := hmeta1.trans hcode
              have hi_u_eq : locN u "i" = locN s "i" := by
                simp [u, setVarHOLFinite, locN, HolFiniteMapExact.lookup_update, FUPDATE,
                  show ofString "klen" ≠ ofString "i" by decide]
              have hn_u_eq : locN u "n" = locN s "n" := by
                simp [u, setVarHOLFinite, locN, HolFiniteMapExact.lookup_update, FUPDATE,
                  show ofString "klen" ≠ ofString "n" by decide]
              rcases hseq : evaluateHOLFiniteState u
                  (.seq (.call (some (none, none)) (ofString "mpt_set") bmiSetArgs)
                    (.assign .local (ofString "i")
                      (.op .add [.var .local (ofString "i"), .const 1]))) with ⟨sr, sp⟩
              rw [hseq] at hrun
              dsimp only at hrun
              obtain ⟨hsr, hpost_eq⟩ := Prod.mk.inj hrun
              subst hsr
              rw [evaluateHOLFiniteState_seq_line780] at hseq
              rcases hc2 : evaluateHOLFiniteState u
                  (.call (some (none, none)) (ofString "mpt_set") bmiSetArgs) with ⟨r2, m2⟩
              rw [hc2] at hseq
              cases r2 with
              | some _ => simp at hseq
              | none =>
                dsimp only at hseq
                have hm2_inv : BuildMptLoopInv2 m2 ∧ locN m2 "i" = locN u "i" ∧
                    locN m2 "n" = locN u "n" := by
                  rw [evaluateHOLFiniteState_call] at hc2
                  rcases ha2 : evalListHOLFinite u
                      (h := fun a => Classical.propDecidable (u.memaddrs a)) bmiSetArgs with
                    _ | vs2
                  · rw [ha2] at hc2; simp at hc2
                  · rw [ha2] at hc2; dsimp only at hc2
                    rcases hl2 : lookupCodeHOLFinite u.code.lookup (ofString "mpt_set") vs2 with
                      _ | ⟨b2, c2, ret2⟩
                    · rw [hl2] at hc2; simp at hc2
                    · rw [hl2] at hc2; dsimp only at hc2
                      by_cases hz2 : u.clock = 0
                      · rw [if_pos hz2] at hc2; simp at hc2
                      · rw [if_neg hz2] at hc2
                        have hPc2 : MptSetReady (callEntryStateHOLFinite u c2) :=
                          callEntryOn_mpt_set_bmi3 u vs2 b2 c2 ret2 hu_code hu_inv ha2 hl2
                        obtain ⟨v_m, _, _, _, _, he_m, _, _, _, _, hc_m, _, _, _, _⟩ :=
                          callee_param_five_exp u (ofString "mpt_set")
                            (ofString "m") (ofString "key") (ofString "klen")
                            (ofString "vptr") (ofString "vlen")
                            .one .one .one .one .one _ _
                            (by rw [hu_code]; exact P3MptSet.lookup_mpt_set)
                            _ _ _ _ _ vs2 b2 c2 ret2 ha2 hl2
                        have hm_cal : c2.lookup (ofString "m") = u.locals.lookup (ofString "m") :=
                          hc_m.trans (by simpa only [evalAt, evalHOLExact] using he_m.symm)
                        rcases hb2 : evaluateHOLFiniteState (callEntryStateHOLFinite u c2) b2 with
                          ⟨br2, bp2⟩
                        rw [hb2] at hc2
                        cases br2 with
                        | none => simp at hc2
                        | some br2' =>
                          cases br2' with
                          | returned v2 =>
                            dsimp only at hc2
                            split at hc2
                            · obtain ⟨_, hm2_eq⟩ := Prod.mk.inj hc2
                              have hspec2 := FunSpec.at_lookup hmk_set u hu_code vs2 b2 c2 ret2
                                hl2 hPc2 (by rw [hb2]; simp)
                              rw [hb2] at hspec2
                              have hstep2 := mptObjStep_c11_to_bmiSetR
                                (hspec2 (Or.inl ⟨v2, rfl⟩))
                              rw [← hm2_eq]
                              exact ⟨bmi3_loopInv2_after_mptSet hu_inv.1 hm_cal hstep2, rfl, rfl⟩
                            · simp at hc2
                          | _ => simp at hc2
                obtain ⟨wi, hwi⟩ := hm2_inv.1.1.2.2.2.2 "i" (by simp)
                have hlt_m2 : locN m2 "i" < locN m2 "n" := by
                  rw [hm2_inv.2.1, hm2_inv.2.2]; exact hu_inv.2.2
                have hasgn : evaluateHOLFiniteState m2
                    (.assign .local (ofString "i")
                      (.op .add [.var .local (ofString "i"), .const 1])) =
                    (none, setVarHOLFinite (ofString "i") (.val (.word (wi + 1))) m2) := by
                  rw [evaluateHOLFiniteState_assign]
                  simp [evalHOLExact, evalListHOLExact, hwi, wordOpHOL, wordOp,
                    valueIsWord, valueWord, isValidValueHOLExact, lookupKvarHOLExact,
                    shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite]
                rw [hasgn] at hseq
                obtain ⟨_, hsp_eq⟩ := Prod.mk.inj hseq
                subst hsp_eq
                have hsp_inv : BuildMptLoopInv2
                    (setVarHOLFinite (ofString "i") (.val (.word (wi + 1))) m2) :=
                  bmi_inv2_set_counter hm2_inv.1 (wi + 1)
                have hsp_rank : buildMptLoopRank
                    (setVarHOLFinite (ofString "i") (.val (.word (wi + 1))) m2) <
                    buildMptLoopRank m2 := by
                  apply buildMptLoopRank_decreases wi hwi hlt_m2 hm2_inv.1.1.1.2.2.1
                  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                      show ofString "i" ≠ ofString "n" by decide]
                rw [← hpost_eq]
                refine ⟨?_, ?_⟩
                · refine localsOnly_buildMptLoopInv2 _ _ _ (fun name hname => ?_) hsp_inv
                  apply resVarEq_lookup_ne
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hname
                  rcases hname with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
                · have hri : locN
                      { setVarHOLFinite (ofString "i") (.val (.word (wi + 1))) m2 with
                        locals := HolFiniteMapExact.resVarEq
                          (setVarHOLFinite (ofString "i") (.val (.word (wi + 1))) m2).locals
                          (ofString "klen", s.locals.lookup (ofString "klen")) } "i" =
                      locN (setVarHOLFinite (ofString "i") (.val (.word (wi + 1))) m2) "i" := by
                    simp only [locN, resVarEq_lookup_ne _ (ofString "klen") (ofString "i") _ (by decide)]
                  have hrn : locN
                      { setVarHOLFinite (ofString "i") (.val (.word (wi + 1))) m2 with
                        locals := HolFiniteMapExact.resVarEq
                          (setVarHOLFinite (ofString "i") (.val (.word (wi + 1))) m2).locals
                          (ofString "klen", s.locals.lookup (ofString "klen")) } "n" =
                      locN (setVarHOLFinite (ofString "i") (.val (.word (wi + 1))) m2) "n" := by
                    simp only [locN, resVarEq_lookup_ne _ (ofString "klen") (ofString "n") _ (by decide)]
                  have hr_m2 : buildMptLoopRank m2 = buildMptLoopRank s := by
                    dsimp only [buildMptLoopRank]
                    rw [hm2_inv.2.1, hm2_inv.2.2, hi_u_eq, hn_u_eq]
                  dsimp only [buildMptLoopRank] at hsp_rank ⊢
                  rw [hri, hrn]
                  omega
            · simp at hrun
          | _ => simp [emptyLocalsHOLFinite] at hrun
private theorem bmi3_loop_step
    (hmk_set : MptKeeps MptSetReady bmiSetRC11 ["heap_ptr", "scratch_ptr"]
      R10Shards.P26_P28.stdKeep (ofString "mpt_set"))
    (hwk_rlp : WorldKeeps WorldOK (fun s => [(locN s "dst", 9)])
      [] R10Shards.P26_P28.stdKeep NoExtra (ofString "rlp_encode_word"))
    {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode)
    (hP : BuildMptLoopInv2 s)
    (hact : LoopActive bmiLoopCond s)
    (hflow : (evaluateHOLFiniteState (decClockHOLFinite s) bmiLoopBody).1 = none ∨
      (evaluateHOLFiniteState (decClockHOLFinite s) bmiLoopBody).1 = some .continue) :
    BuildMptLoopInv2 (evaluateHOLFiniteState (decClockHOLFinite s) bmiLoopBody).2 ∧
      buildMptLoopRank (evaluateHOLFiniteState (decClockHOLFinite s) bmiLoopBody).2 <
        buildMptLoopRank s := by
  have hc := bmi3_loop_body_step_core hmk_set hwk_rlp (decClockHOLFinite s) hcode
    (buildMptLoopInv2_decClock hP) (loopActive_decClock hact) hflow
  exact ⟨hc.1, hc.2⟩
private theorem bmi3_while_hoare
    (hmk_set : MptKeeps MptSetReady bmiSetRC11 ["heap_ptr", "scratch_ptr"]
      R10Shards.P26_P28.stdKeep (ofString "mpt_set"))
    (hwk_rlp : WorldKeeps WorldOK (fun s => [(locN s "dst", 9)])
      [] R10Shards.P26_P28.stdKeep NoExtra (ofString "rlp_encode_word")) :
    Hoare BuildMptLoopInv2 (.while bmiLoopCond bmiLoopBody)
      (fun r t => r = none → BuildMptLoopInv t) := by
  refine ⟨fun {F} s hcode hP _ hr => ?_⟩
  rcases hrun : evaluateHOLFiniteState s (.while bmiLoopCond bmiLoopBody) with ⟨r, post⟩
  rw [hrun] at hr
  dsimp only at hr
  subst hr
  suffices ∀ (k : Nat) (st : PanSemStateFiniteExact 64 F),
      st.clock = k → st.code = originalRuntimeCode → BuildMptLoopInv2 st →
      evaluateHOLFiniteState st (.while bmiLoopCond bmiLoopBody) = (none, post) →
      BuildMptLoopInv post from
    this s.clock s rfl hcode hP hrun
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro st hk st_code hPst hst_run
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at hst_run
    split at hst_run
    · rename_i w hw
      by_cases hwnz : w ≠ 0
      · rw [if_pos hwnz] at hst_run
        by_cases hz : st.clock = 0
        · rw [if_pos hz] at hst_run; simp at hst_run
        · rw [if_neg hz] at hst_run
          dsimp only at hst_run
          have hrem := evaluateHOLFiniteState_clock_le (decClockHOLFinite st) bmiLoopBody
          have hmeta := (evaluateHOLFiniteState_metadata (decClockHOLFinite st) bmiLoopBody).1
          have hact : LoopActive bmiLoopCond st := ⟨w, hw, hwnz⟩
          rcases bRun : evaluateHOLFiniteState (decClockHOLFinite st) bmiLoopBody with ⟨r1, mid⟩
          rw [bRun] at hst_run hrem hmeta
          dsimp only at hst_run hmeta
          have hclk_lt : mid.clock < k := by
            change mid.clock ≤ st.clock - 1 at hrem
            omega
          cases r1 with
          | none =>
            have hstep := bmi3_loop_step hmk_set hwk_rlp st st_code hPst hact
              (by rw [bRun]; exact Or.inl rfl)
            rw [bRun] at hstep
            exact ih mid.clock hclk_lt mid rfl (hmeta.trans st_code) hstep.1 hst_run
          | some r1' =>
            cases r1' with
            | «continue» =>
              have hstep := bmi3_loop_step hmk_set hwk_rlp st st_code hPst hact
                (by rw [bRun]; exact Or.inr rfl)
              rw [bRun] at hstep
              exact ih mid.clock hclk_lt mid rfl (hmeta.trans st_code) hstep.1 hst_run
            | «break» =>
              exfalso
              have hnb : InitECandidate.Solver.GuestUniformClockBound.noTopBreak bmiLoopBody =
                  true := by decide
              have hno := InitECandidate.Solver.GuestUniformClockBound.evaluate_noTopBreak
                bmiLoopBody hnb (decClockHOLFinite st)
              rw [bRun] at hno
              exact hno rfl
            | _ => simp at hst_run
      · rw [if_neg hwnz] at hst_run
        obtain ⟨_, rfl⟩ := Prod.mk.inj hst_run
        exact hPst.1
    · simp at hst_run
theorem gbody_build_mpt_indexed_strong :
    (TerminatingFunBoundedOn GuestInv (ofString "heap_mark") K.«heap_mark») →
    (TerminatingFunBoundedOn GuestInv (ofString "heap_release") K.«heap_release») →
    (TerminatingFunBoundedOn GuestInv (ofString "mpt_new") K.«mpt_new») →
    (TerminatingFunBoundedOn MptObjReady (ofString "mpt_root") K.«mpt_root») →
    (TerminatingFunBoundedOn MptSetReady (ofString "mpt_set") K.«mpt_set») →
    (TerminatingFunBoundedOn GuestInv (ofString "rlp_encode_word") K.«rlp_encode_word») →
    (ReadOnlyFn (ofString "heap_mark")) →
    (WorldKeeps WorldOK (fun _ => [])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoids (fun _ _ w => [(w, 16)])) (ofString "mpt_new")) →
    (Returns ArenaReady (fun s post m => FreshBlock s post m 16 ∧
        memW post m = locN s "root_node" ∧ memW post (m + 8) = locN s "secured")
      (ofString "mpt_new")) →
    (MptKeeps MptSetReady
      (fun s =>
        [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
         (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
         (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40)])
      ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (ofString "mpt_set")) →
    (WorldKeeps WorldOK (fun s => [(locN s "dst", 9)])
      []
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "rlp_encode_word")) →
    TerminatingFunBoundedOn BuildMptIndexedReadyStrong
      (ofString "build_mpt_indexed") K.«build_mpt_indexed» := by
  intro hmark hrelease hnew hroot hset hrlp hro_mark hwk_new hrt_new hmk_set hwk_rlp
  refine ⟨_, _, _, lookup_build_mpt_indexed_strong, ?_⟩
  simp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_build_mpt_indexed,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  have hwhile : TerminatingProgBoundedOn BuildMptLoopInv2
      (.while bmiLoopCond bmiLoopBody)
      ((2 ^ 64 + 1) * ((K.«rlp_encode_word» + 1) + (K.«mpt_set» + 1) + 1)) :=
    TerminatingProgBoundedOn.while_rank_active
      buildMptLoopRank
      (fun _ hP => buildMptLoopInv2_decClock hP)
      (bmi3_loop_body_bound hrlp hset hwk_rlp)
      (fun _ _ hP _ => buildMptLoopRank_le hP.1)
      (fun s hc hP hact hflow => bmi3_loop_step hmk_set hwk_rlp s hc hP hact hflow)
  have hloop_and_tail : TerminatingProgBoundedOn BuildMptLoopInv2
      (.seq (.while bmiLoopCond bmiLoopBody)
        (.seq
          (.call (some (none, none)) (ofString "mpt_root")
            [.var .local (ofString "m"), .var .local (ofString "out")])
          (.seq
            (.call (some (none, none)) (ofString "heap_release")
              [.var .local (ofString "mark")])
            (.return (.const 0)))))
      ((2 ^ 64 + 1) * ((K.«rlp_encode_word» + 1) + (K.«mpt_set» + 1) + 1) +
        ((K.«mpt_root» + 1) + (K.«heap_release» + 1))) :=
    R16Shards.TerminatingProgBoundedOn.seq_hoare_trans
      hwhile
      (bmi3_while_hoare hmk_set hwk_rlp)
      (buildMptIndexed_tail_bound hroot hrelease)
  have hdec_i : TerminatingProgBoundedOn BmiAfterNewStrong
      (.dec (ofString "i") .one (.const 0)
        (.seq (.while bmiLoopCond bmiLoopBody)
          (.seq
            (.call (some (none, none)) (ofString "mpt_root")
              [.var .local (ofString "m"), .var .local (ofString "out")])
            (.seq
              (.call (some (none, none)) (ofString "heap_release")
                [.var .local (ofString "mark")])
              (.return (.const 0))))))
      ((2 ^ 64 + 1) * ((K.«rlp_encode_word» + 1) + (K.«mpt_set» + 1) + 1) +
        ((K.«mpt_root» + 1) + (K.«heap_release» + 1))) :=
    R16Shards.dec_eval_on (ofString "i") .one (.const 0)
      (fun s v hP he => by
        have hv : v = .val (.word 0) := evalAt_const s 0 v he
        subst hv
        exact bmiAfterNewStrong_set_counter_loopInv2 hP 0)
      hloop_and_tail
  refine @TerminatingProgBoundedOn.mono_bound BuildMptIndexedReadyStrong _ _ K.«build_mpt_indexed»
    (TerminatingProgBoundedOn.decCall_on hmark (ofString "mark") .one []
      (callEntryOn_of_imp (P := BuildMptIndexedReadyStrong)
        localsFree_guestInv (fun _ h => h.1.1.1.1) _ _)
      (decCallResume_heap_mark_bmi_strong hro_mark)
      (TerminatingProgBoundedOn.decCall_on hnew (ofString "m") .one [.const 0, .const 0]
        (callEntryOn_of_imp (P := fun s => BuildMptAfterMark s ∧ BmiAfterMarkC s)
          localsFree_guestInv (fun _ h => h.1.1.1.1.1) _ _)
        (decCallResume_mpt_new_bmi_strong hwk_new hrt_new)
        hdec_i))
    ?_
  unfold K.«build_mpt_indexed»
  omega
end InitECandidate.Solver.Wave8GuestInv.R16Shards.MptC10C12
