import InitECandidate.Solver.Wave8GuestInv.R16Shards.MptC10C12.BuildMptIndexedWalk4
import InitECandidate.Solver.Wave8GuestInv.R16Shards.PayloadWorldHelpers
import InitECandidate.Solver.Wave8GuestInv.ContractParts.ExecBlockAndCalleeClosureR32

/-! Wave 8 R32 (BmiBoundStrongR32): the clock bound of `build_mpt_indexed`
at `BuildMptIndexedReadyStrong` with no premise.

`MptC10C12.gbody_build_mpt_indexed_strong` takes the bound of `mpt_root` at
the weak guard `MptObjReady`. That bound has no proof in the tree: the weak
`_node_rlp_fill` leaf at `NodeRlpReady` is open. `mpt_root` is bounded at
`NrfStrong.MptObjReadyStrong` (`NrfStrong.gbody_mpt_root_strong`), so this
module replays the composition with the `mpt_root` call entered at the
strong guard.

The strong guard needs the 1-byte value-pointer invariant of the fresh
trie, which is carried by the world-effect loop invariant of
`BuildMptIndexedWalk4` (`BmiLoopInv`), not by `BuildMptLoopInv2` of
`BuildMptIndexedWalk3`. Both are private to their files, so the private
parts of the two files are copied here unchanged, and the bound is proved
with the conjunction of the two invariants.

Results: `gbody_build_mpt_indexed_rootStrong` (the `mpt_root` premise at the
strong guard, the other ten premises as before), `fb_mpt_root_strong` and
`fb_build_mpt_indexed_strong` (no premise). -/

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

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.MptC10C12.BmiBound

set_option linter.unusedVariables false

/-! ## Copy of the private part of BuildMptIndexedWalk3 -/
private def BmiAfterNewStrong : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => BuildMptAfterNew s ∧ BmiWkInvE s
private theorem decCallResume_heap_mark_bmi_strong
    (hro : ReadOnlyFn (ofString "heap_mark")) :
    DecCallResumeOn BuildMptIndexedReadyStrong
      (fun s => BuildMptAfterMark s ∧ BmiAfterMarkC s)
      (ofString "mark") (ofString "heap_mark") [] := by
  intro F state values body callee ret value post hcode hP hargs hl hrun
  have hdisjE : BmiWorldDisjE state := by
    obtain ⟨S, Nd, hr⟩ := strong_bmiReadyG hP
    exact ⟨S, Nd, hr.2.1, hr.2.2.2.1⟩
  exact ⟨(decCallResume_heap_mark_bmi hro state values body callee ret value post
      hcode ⟨hP.1, hdisjE⟩ hargs hl hrun).1,
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
  have hdisjE : BmiWorldDisjE state := by
    obtain ⟨S, Nd, hr, _, _⟩ := hP.2
    exact ⟨S, Nd, hr.2.1, hr.2.2.2.1⟩
  exact ⟨(decCallResume_mpt_new_bmi hwk hrt state values body callee ret value post
      hcode ⟨hP.1, hdisjE⟩ hargs hl hrun).1,
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
    CallEntryOn
      (fun s => BuildMptLoopInv2 s ∧ locN s "klen" ≤ 32 ∧ locN s "i" < locN s "n" ∧
        ∃ w, s.locals.lookup (ofString "klen") = some (.val (.word w)))
      MptSetReady (ofString "mpt_set") bmiSetArgs := by
  intro F s values body callee ret hcode hP hargs hl
  obtain ⟨hP2, hklen_le, hlt, _⟩ := hP
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
              have hu_inv : BuildMptLoopInv2 u ∧ locN u "klen" ≤ 32 ∧ locN u "i" < locN u "n" ∧
                  ∃ w, u.locals.lookup (ofString "klen") = some (.val (.word w)) :=
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
                  rw [hm2_inv.2.1, hm2_inv.2.2]; exact hu_inv.2.2.1
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

/-! ## Copy of the private part of BuildMptIndexedWalk4 -/

private abbrev bmi4Rl {F : Type} (s0 : PanSemStateFiniteExact 64 F) : List Ivl :=
  bmiWkRti s0 ++ [(globN s0 "heap_ptr", heapLimit - globN s0 "heap_ptr")]
private abbrev bmi4RlpArgs : List (ExpHOL 64) :=
  [.var .global (ofString "mpt_key_scratch"), .var .local (ofString "i")]
private abbrev bmi4SetArgs : List (ExpHOL 64) :=
  [.var .local (ofString "m"), .var .global (ofString "mpt_key_scratch"), .var .local (ofString "klen"),
   .load .one (.op .add [.var .local (ofString "slice_arr"), .panop .mul [.var .local (ofString "i"), .const 16]]),
   .load .one (.op .add [.var .local (ofString "slice_arr"), .panop .mul [.var .local (ofString "i"), .const 16], .const 8])]
private abbrev bmi4LoopCond : ExpHOL 64 :=
  .cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))
private abbrev bmi4LoopBody : ProgHOL 64 :=
  .decCall (ofString "klen") .one (ofString "rlp_encode_word") bmi4RlpArgs
    (.seq (.call (some (none, none)) (ofString "mpt_set") bmi4SetArgs)
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])))
private abbrev bmi4Tail : ProgHOL 64 :=
  .seq (.call (some (none, none)) (ofString "mpt_root") [.var .local (ofString "m"), .var .local (ofString "out")])
    (.seq (.call (some (none, none)) (ofString "heap_release") [.var .local (ofString "mark")]) (.return (.const 0)))

private theorem lookup_mpt_root_bmi4 :
    originalRuntimeCode.lookup (ofString "mpt_root") =
      some ([(ofString "m", .one), (ofString "out", .one)],
        sourceFnBody Guest.Software.guestFn_mpt_root, .one) :=
  lookup_of_guestAst_getElem 291 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_mpt_root) rfl

private theorem bmi4_buf_in_fixedObjects {F : Type} (s : PanSemStateFiniteExact 64 F)
    (gs : String × Nat) (hgb : gs ∈ globalBuffers) : bufferRegion s gs ∈ fixedObjects s := by
  unfold fixedObjects; repeat apply List.mem_append_left
  exact List.mem_map.2 ⟨gs, hgb, rfl⟩

private theorem bmi4_slice_disj_rti {F : Type} (s : PanSemStateFiniteExact 64 F)
    (S Nd : List Nat) (h : BmiReadyG s S Nd) :
    IvlsDisj [(locN s "slice_arr", 16 * locN s "n")] (bmiWkRti s) := by
  intro o ho j hj; simp only [List.mem_singleton] at ho; subst o
  have hbuf := h.1.2.2.2.2.2.1
  simp only [bmiWkRti, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl
  · exact Disj.flip (h.2.2.2.2.1 _ (by simp) _ List.mem_cons_self)
  · exact hbuf _ (by simp) _ (List.mem_map.2 ⟨("keccak_pad", 136), by simp, rfl⟩)
  · exact hbuf _ (by simp) _ (List.mem_map.2 ⟨("keccak_st", 200), by simp, rfl⟩)
  · exact hbuf _ (by simp) _ (List.mem_map.2 ⟨("mpt_hash_scratch", 40), by simp, rfl⟩)
  · exact hbuf _ (by simp) _ (List.mem_map.2 ⟨("mpt_key_scratch", 16), by simp, rfl⟩)

private theorem bmi4_eff_mono {F : Type} {s0 t : PanSemStateFiniteExact 64 F}
    (heff : R16Shards.WorldEff s0 t (bmi4Rl s0) [] (bmiWkGw : List String)) :
    R16Shards.WorldEff s0 t (bmiWkRti s0) [] ["heap_ptr", "scratch_ptr"] := by
  refine heff.mono ?_ (fun _ h => h) (fun _ h => h)
  intro iv hiv hpos; rcases List.mem_append.1 hiv with hrti | htl
  · exact Or.inl ⟨iv, hrti, le_rfl, le_rfl⟩
  · simp only [List.mem_singleton] at htl; subst htl
    exact Or.inr (Or.inr (Or.inr ⟨le_rfl, by dsimp only at hpos ⊢; omega⟩))

private theorem bmi4_glob_eq {F : Type} {s0 t : PanSemStateFiniteExact 64 F}
    (heff : R16Shards.WorldEff s0 t (bmi4Rl s0) [] (bmiWkGw : List String)) (g : String)
    (hne1 : ofString g ≠ ofString "heap_ptr") (hne2 : ofString g ≠ ofString "scratch_ptr") :
    globN t g = globN s0 g := by
  apply globN_eq_of_lookup; apply heff.gw_kept; intro hm
  simp only [bmiWkGw, List.map, List.mem_cons, List.not_mem_nil, or_false] at hm
  exact hm.elim hne1 hne2

private theorem bmi4_world_from_eff {F : Type} {s0 t : PanSemStateFiniteExact 64 F}
    {S0 Nd0 : List Nat}
    (hready0 : BmiReadyG s0 S0 Nd0)
    (heff0 : R16Shards.WorldEff s0 t (bmi4Rl s0) [] (bmiWkGw : List String)) :
    WorldTypedWith t S0 Nd0 ∧
    nodeExtents t Nd0 = nodeExtents s0 Nd0 ∧
    (∀ u ∈ S0, htabFootprint t u = htabFootprint s0 u) ∧
    fixedObjects t = fixedObjects s0 := by
  have heff := bmi4_eff_mono heff0
  have hAs : ArenaReady s0 := hready0.1.1.1
  have hAp : ArenaReady t := heff.arena
  have hag : AllocatorGrows s0 t := ⟨heff.hp_lo, heff.sp_hi⟩
  have hDisjR := hready0.2.2.1
  obtain ⟨hT, hJ, hF, hTr⟩ := hready0.2.1
  have hcore : ∀ g ∈ coreWorldGlobals, globN t g = globN s0 g :=
    fun g hg => globN_eq_of_lookup (heff.gw_kept (ofString g) (bmiRoot_gw_sub g hg))
  have hlow : memW t 8 = memW s0 8 ∧ memW t 16 = memW s0 16 :=
    ⟨mem_low_eq_of_domain_writes heff.out_dom hAs.1 (by rw [Fast_C08WkShard03.sourceBase_val]; omega),
     mem_low_eq_of_domain_writes heff.out_dom hAs.1 (by rw [Fast_C08WkShard03.sourceBase_val]; omega)⟩
  let keep0 : List Ivl := bmiWkRti s0 ++ [freeGap s0]
  have hfr_pos : ∀ a : BitVec 64, t.memory a ≠ s0.memory a →
      (∃ j ∈ keep0, Fast_C08WkShard03.CellHitsPos a.toNat j) ∨
        Fast_C08WkShard03.CellHitsPos a.toNat (heapFree s0) := by
    intro a hne
    rcases heff.cell_frame a hne with ⟨ivl, hivl, hhit⟩ | ⟨gs, hgs, _⟩ | hfg | hhf
    · exact Or.inl ⟨ivl, List.mem_append_left _ hivl, hhit⟩
    · simp at hgs
    · exact Or.inl ⟨freeGap s0, List.mem_append_right _ List.mem_cons_self, hfg⟩
    · exact Or.inr hhf
  have hu_wti_aligned : ∀ i ∈ worldTypedIvls s0 S0 Nd0, Allocated s0 i →
      i.1 % 8 = 0 → i.2 % 8 = 0 → IvlUnhit s0 t i := by
    intro i hi hal hi1 hi2
    refine ivlUnhit_of_cellHitsPos hi1 hi2 hfr_pos (fun j hj => ?_)
      (disj_allocated_heapFree hAs.2 hal)
    rcases List.mem_append.1 hj with hjR | hjG
    · exact Disj.flip (hDisjR j hjR i hi)
    · simp only [List.mem_singleton] at hjG
      subst hjG
      exact disj_allocated_freeGap hAs.2 hal
  have hu_fix_wti : ∀ i ∈ worldTypedIvls s0 S0 Nd0, i ∈ fixedObjects s0 →
      i.2 ≠ 0 → IvlUnhit s0 t i := by
    intro i hwti hfi hpos
    rcases hF.1 i hfi with h0 | ⟨hal, hw⟩
    · exact absurd h0 hpos
    · exact hu_wti_aligned i hwti hal hw.1 hw.2.1
  have hu_tab : ∀ u ∈ S0, ∀ i ∈ htabFootprint s0 u, IvlUnhit s0 t i := by
    intro u hu i hi
    have hal := ((hT.2.1 u hu).2 i hi).1
    have hw := ((hT.2.1 u hu).1.1 i hi).2
    refine hu_wti_aligned i ?_ hal hw.1 hw.2.1
    unfold worldTypedIvls
    apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
    apply List.mem_append.2; left; apply List.mem_append.2; left
    exact List.mem_flatMap.2 ⟨u, hu, hi⟩
  have hu_ws : globN s0 "ws" ≠ 0 → IvlUnhit s0 t (globN s0 "ws", 40) := fun hnz =>
    hu_fix_wti _
      (by unfold worldTypedIvls; apply List.mem_append.2; left; apply List.mem_append.2; left
          apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; right
          exact List.mem_map.2 ⟨("ws", 40), by simp [typedRecords], by simp [hnz]⟩)
      (by simpa [hnz] using typedRecord_mem_fixedObjects s0 (r := ("ws", 40)) (by simp [typedRecords]))
      (by simp)
  have hu_bs : globN s0 "bs" ≠ 0 → IvlUnhit s0 t (globN s0 "bs", 80) := fun hnz =>
    hu_fix_wti _
      (by unfold worldTypedIvls; apply List.mem_append.2; left; apply List.mem_append.2; left
          apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; right
          exact List.mem_map.2 ⟨("bs", 80), by simp [typedRecords], by simp [hnz]⟩)
      (by simpa [hnz] using typedRecord_mem_fixedObjects s0 (r := ("bs", 80)) (by simp [typedRecords]))
      (by simp)
  have hu_ts : globN s0 "ts" ≠ 0 → IvlUnhit s0 t (globN s0 "ts", 72) := fun hnz =>
    hu_fix_wti _
      (by unfold worldTypedIvls; apply List.mem_append.2; left; apply List.mem_append.2; left
          apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; right
          exact List.mem_map.2 ⟨("ts", 72), by simp [typedRecords], by simp [hnz]⟩)
      (by simpa [hnz] using typedRecord_mem_fixedObjects s0 (r := ("ts", 72)) (by simp [typedRecords]))
      (by simp)
  have hu_bo : globN s0 "bo" ≠ 0 → IvlUnhit s0 t (globN s0 "bo", 88) := fun hnz =>
    hu_fix_wti _
      (by unfold worldTypedIvls; apply List.mem_append.2; left; apply List.mem_append.2; left
          apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; right
          exact List.mem_map.2 ⟨("bo", 88), by simp [typedRecords], by simp [hnz]⟩)
      (by simpa [hnz] using typedRecord_mem_fixedObjects s0 (r := ("bo", 88)) (by simp [typedRecords]))
      (by simp)
  have hu_jr : globN s0 "journal_cap" ≠ 0 →
      IvlUnhit s0 t (globN s0 "journal", 32 * globN s0 "journal_cap") := fun hcnz =>
    hu_fix_wti _
      (by unfold worldTypedIvls; apply List.mem_append.2; left; apply List.mem_append.2; left
          apply List.mem_append.2; left; apply List.mem_append.2; right; simp [hcnz])
      (by unfold fixedObjects; apply List.mem_append.2; left; apply List.mem_append.2; left
          apply List.mem_append.2; right; simp [hcnz])
      (by dsimp only; omega)
  have hu_bo_lst : ∀ i ∈ blockOutObjects s0, i.2 = 24 → IvlUnhit s0 t i := fun i hi h24 =>
    hu_fix_wti i
      (by unfold worldTypedIvls; apply List.mem_append.2; left; apply List.mem_append.2; left
          apply List.mem_append.2; right; exact hi)
      (by unfold fixedObjects; apply List.mem_append.2; left; apply List.mem_append.2; right; exact hi)
      (by omega)
  have hu_bal : ∀ i ∈ balObjects s0, i.2 ≠ 0 → IvlUnhit s0 t i := fun i hi hpos =>
    hu_fix_wti i
      (by unfold worldTypedIvls; apply List.mem_append.2; left; apply List.mem_append.2; right; exact hi)
      (by unfold fixedObjects; exact List.mem_append.2 (Or.inr hi))
      hpos
  have hu_nd_rec : ∀ n ∈ Nd0, IvlUnhit s0 t (nodeIvl s0 n) := fun n hn => by
    have hal := (hTr.1.1 n hn).2.1
    have hw := (hTr.1.1 n hn).2.2.2.1
    refine hu_wti_aligned _ ?_ hal hw.1 hw.2.1
    unfold worldTypedIvls; refine List.mem_append.2 (Or.inr ?_)
    unfold nodeExtents; exact List.mem_flatMap.2 ⟨n, hn, by simp [nodeIvl]⟩
  have hu_nd_byte : ∀ n ∈ Nd0, (memW s0 n = 1 ∨ memW s0 n = 2) → memW s0 (n + 40) ≠ 0 →
      ∀ k, k < memW s0 (n + 40) → memB t (memW s0 (n + 32) + k) = memB s0 (memW s0 (n + 32) + k) := by
    intro n hn h12 hlen0 k hk
    have h264 : heapLimit ≤ 2 ^ 64 := by decide
    rcases (hTr.1.1 n hn).2.2.2.2.2.2.1 h12 with h0 | ⟨_, hal_p, hin_p, _⟩
    · exact absurd h0 hlen0
    · have hp_wti : (memW s0 (n + 32), memW s0 (n + 40)) ∈ worldTypedIvls s0 S0 Nd0 := by
        unfold worldTypedIvls; refine List.mem_append.2 (Or.inr ?_)
        unfold nodeExtents; exact List.mem_flatMap.2 ⟨n, hn, by simp [nodePath, h12, hlen0]⟩
      by_contra hne_b
      have ha_lt : memW s0 (n + 32) + k < 2 ^ 64 := by have := hin_p.2; dsimp at this; omega
      rcases heff.byte_frame _ ha_lt hne_b with ⟨ivl, hivl, hin_ivl⟩ | ⟨gs, hgs, _⟩ | hfg | hhf
      · have hdj := hDisjR ivl hivl _ hp_wti
        unfold InIvl at hin_ivl; rcases hdj with h0 | h0 | h1 | h2 <;> (dsimp at *; omega)
      · simp at hgs
      · have hdj := disj_allocated_freeGap hAs.2 hal_p
        unfold InIvl at hfg; rcases hdj with h0 | h0 | h1 | h2 <;> (dsimp at *; omega)
      · have hdj := disj_allocated_heapFree hAs.2 hal_p
        unfold InIvl at hhf; rcases hdj with h0 | h0 | h1 | h2 <;> (dsimp at *; omega)
  have hbo_eq := (Fast_C08WkShard03.blockOutObjects_eq_of_bo_unhit hAs.2 hF (hcore "bo" (by decide))
    (fun hbo k hk hnz => hT.2.2.2.2.2.2.2.2.2.2.1 hbo k hk hnz) hu_bo hu_bo_lst).1
  have hu_bal_all : ∀ i ∈ balObjects s0, IvlUnhit s0 t i := fun i hi => by
    by_cases hz : i.2 = 0
    · have hi0 : i = (0, 0) := bmiWk_fixedObjects_zero_len_eq s0 i
        (by unfold fixedObjects; exact List.mem_append.2 (Or.inr hi)) hz
      rw [hi0]; intro a _ ⟨_, hc⟩; dsimp at hc; omega
    · exact hu_bal i hi hz
  have hbal_eq := (balObjects_eq_of_unhit hAs.2 hT hF (hcore "bal_accounts" (by decide))
    hu_tab hu_bal_all hlow).1
  obtain ⟨hF_post, hfix_new⟩ := fixedTyped_of_freshBufsOK hAs hAp hag hF
    (hcore "journal" (by decide)) (hcore "journal_cap" (by decide)) hbo_eq hbal_eq heff.fresh_bufs
  obtain ⟨hWT_post, _, hne_eq, hfp_eq⟩ := worldTypedWith_congr_w1 hAs hAp hag hcore
    ⟨hT, hJ, hF, hTr⟩ hu_tab hu_ws hu_bs hu_ts hu_bo hu_jr hu_bo_lst hu_bal hu_nd_rec hu_nd_byte
    hlow hF_post hfix_new
  have hfix_eq : fixedObjects t = fixedObjects s0 := by
    unfold fixedObjects
    rw [hbo_eq, hbal_eq, hcore "journal" (by decide), hcore "journal_cap" (by decide)]
    congr 3
    apply List.map_congr_left
    intro gn hgn
    have hne : ofString gn.1 ≠ ofString "heap_ptr" ∧ ofString gn.1 ≠ ofString "scratch_ptr" := by
      revert gn hgn; decide
    rw [bmi4_glob_eq heff0 gn.1 hne.1 hne.2]
  exact ⟨hWT_post, hne_eq, hfp_eq, hfix_eq⟩

private theorem bmi4_slice_eq {F : Type} {s0 t : PanSemStateFiniteExact 64 F} {S0 Nd0 : List Nat}
    (hready0 : BmiReadyG s0 S0 Nd0)
    (heff0 : R16Shards.WorldEff s0 t (bmi4Rl s0) [] (bmiWkGw : List String)) :
    WordsOK t (locN s0 "slice_arr", 16 * locN s0 "n") ∧
    (∀ i, i < locN s0 "n" →
      memW t (locN s0 "slice_arr" + 16 * i) = memW s0 (locN s0 "slice_arr" + 16 * i) ∧
      memW t (locN s0 "slice_arr" + 16 * i + 8) = memW s0 (locN s0 "slice_arr" + 16 * i + 8)) := by
  have heff := bmi4_eff_mono heff0
  have hAs : ArenaReady s0 := hready0.1.1.1
  have hin := hready0.1.2.2.2.1; have hw_s0 := hready0.1.2.2.2.2.1
  have hal_sl : Allocated s0 (locN s0 "slice_arr", 16 * locN s0 "n") := Or.inl hin
  refine ⟨P3MptSet.wordsOK_transfer hAs.1 heff.arena.1 hw_s0, fun i hi => ?_⟩
  let keep0 : List Ivl := bmiWkRti s0 ++ [freeGap s0]
  have hfr_pos : ∀ a : BitVec 64, t.memory a ≠ s0.memory a →
      (∃ j ∈ keep0, Fast_C08WkShard03.CellHitsPos a.toNat j) ∨
        Fast_C08WkShard03.CellHitsPos a.toNat (heapFree s0) := fun a hne => by
    rcases heff.cell_frame a hne with ⟨ivl, hivl, hhit⟩ | ⟨gs, hgs, _⟩ | hfg | hhf
    · exact Or.inl ⟨ivl, List.mem_append_left _ hivl, hhit⟩
    · simp at hgs
    · exact Or.inl ⟨freeGap s0, List.mem_append_right _ List.mem_cons_self, hfg⟩
    · exact Or.inr hhf
  have hdj_sl := bmi4_slice_disj_rti s0 S0 Nd0 hready0
  have hu_sl : IvlUnhit s0 t (locN s0 "slice_arr", 16 * locN s0 "n") := by
    refine ivlUnhit_of_cellHitsPos hw_s0.1 (by omega) hfr_pos (fun j hj => ?_)
      (disj_allocated_heapFree hAs.2 hal_sl)
    rcases List.mem_append.1 hj with hjR | hjG
    · exact hdj_sl _ List.mem_cons_self j hjR
    · simp only [List.mem_singleton] at hjG; subst hjG; exact disj_allocated_freeGap hAs.2 hal_sl
  have hfit : locN s0 "slice_arr" + 16 * locN s0 "n" ≤ 2 ^ 64 := by
    have : heapLimit ≤ 2 ^ 64 := by decide
    have := hAs.2.2.1; rcases hin with ⟨h1, h2⟩; omega
  have ha8 : locN s0 "slice_arr" % 8 = 0 := hw_s0.1
  exact ⟨memW_eq_of_ivlUnhit hu_sl (by omega) hfit ⟨by omega, by omega⟩,
         memW_eq_of_ivlUnhit hu_sl (by omega) hfit ⟨by omega, by omega⟩⟩

private def BmiMptInv {F : Type} (s0 : PanSemStateFiniteExact 64 F) (S0 Nd0 : List Nat)
    (t : PanSemStateFiniteExact 64 F) : Prop :=
  let mark := globN s0 "heap_ptr"
  mark + 16 ≤ globN t "heap_ptr" ∧
  ∃ Nm, WorldTypedWith t S0 Nd0 ∧ MptObjInWithStrong t S0 Nm mark ∧
    IvlsDisj ((mark, 16) :: nodeExtents t Nm) (nodeExtents t Nd0) ∧
    (∀ o ∈ nodeExtents t Nm, 0 < o.2 → mark ≤ o.1 ∧ o.1 + o.2 ≤ globN t "heap_ptr")

private theorem bmi4_mptInv_locals_clock {F : Type}
    {s0 t : PanSemStateFiniteExact 64 F} {S0 Nd0 : List Nat} (h : BmiMptInv s0 S0 Nd0 t)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    BmiMptInv s0 S0 Nd0 { t with locals := L, clock := k } := by
  obtain ⟨hm16, Nm, hWT, hmObj, hdN, hspan⟩ := h
  exact ⟨hm16, Nm, (worldTypedWith_build_locals t L k S0 Nd0).2 hWT, hmObj, hdN, hspan⟩

private theorem bmi4_mptInv_after_new {F : Type}
    {s0 s1 mid : PanSemStateFiniteExact 64 F} {S0 Nd0 : List Nat} (hready0 : BmiReadyG s0 S0 Nd0)
    (heff_mid : R16Shards.WorldEff s0 mid (bmi4Rl s0) [] (bmiWkGw : List String))
    (hmid_hp : globN mid "heap_ptr" = globN s0 "heap_ptr" + 16)
    (hFB : Wave8Contracts.M26.FreshBlock s1 mid (globN s0 "heap_ptr") 16)
    (hmem0 : memW mid (globN s0 "heap_ptr") = 0) : BmiMptInv s0 S0 Nd0 mid := by
  set mark := globN s0 "heap_ptr"
  obtain ⟨hWT, hne_eq, hfp_eq, hfix_eq⟩ := bmi4_world_from_eff hready0 heff_mid
  have hAs0 : ArenaOK s0 := hready0.1.1.1.2
  have hmark_lim : mark + 16 ≤ heapLimit := by have := heff_mid.arena.2.2.1; omega
  have hdisj_own : ∀ j ∈ worldOwned s0 S0 Nd0, Disj (mark, 16) j := fun j hj => by
    rcases bmiWk_worldOwned_zero_or_inside hready0.2.1 j hj with rfl | h1 | h2
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inr h1.2))
    · have hss : heapLimit ≤ scratchStart := by decide
      have hsp_lo : scratchStart ≤ globN s0 "scratch_ptr" := by
        have := hAs0.2.2.1; have := hAs0.2.2.2.1; omega
      exact Or.inr (Or.inr (Or.inl (le_trans hmark_lim (le_trans hss (le_trans hsp_lo h2.1)))))
  refine ⟨by omega, [], hWT, ⟨⟨Or.inl ⟨hAs0.1, by omega⟩, hFB.2.2, ?_, ?_, by simp [NodeHeap],
    Or.inl hmem0, by simp [nodeExtents]⟩, by simp [NodeHeapValuePtrOK, NodeValuesSafe]⟩, ?_,
    by simp [nodeExtents]⟩
  · intro u hu i hi; rw [hfp_eq u hu] at hi
    exact hdisj_own i (List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.2 ⟨u, hu, hi⟩)))
  · rw [hfix_eq]; intro f hf; exact hdisj_own f (List.mem_append_left _ (List.mem_append_right _ hf))
  · rw [hne_eq]; intro o ho p hp
    simp only [nodeExtents, List.flatMap_nil, List.mem_cons, List.not_mem_nil, or_false] at ho
    subst ho; exact hdisj_own p (List.mem_append_right _ hp)

private theorem bmi4_hbe_mono_rl {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {R1 R2 : List Ivl} {gw : List String}
    (h : HeapByteEff s post R1 gw) (hsub : ∀ iv ∈ R1, iv ∈ R2) :
    HeapByteEff s post R2 gw :=
    ⟨h.arena, h.memaddrs, h.hp_le, h.fp_eq, h.sp_le, h.be, h.globals, h.out_dom,
   fun a hne => (h.cell_frame a hne).imp_left (fun ⟨iv, hiv, hc⟩ => ⟨iv, hsub iv hiv, hc⟩),
   fun b hb hne => (h.byte_frame b hb hne).imp_left (fun ⟨iv, hiv, hi⟩ => ⟨iv, hsub iv hiv, hi⟩)⟩

private theorem bmi4_mptInv_after_rlp {F : Type}
    {s0 cur cpost : PanSemStateFiniteExact 64 F} {S0 Nd0 : List Nat} (hready0 : BmiReadyG s0 S0 Nd0)
    (heff_cur : R16Shards.WorldEff s0 cur (bmi4Rl s0) [] (bmiWkGw : List String))
    (heff_post : R16Shards.WorldEff s0 cpost (bmi4Rl s0) [] (bmiWkGw : List String))
    (hinv : BmiMptInv s0 S0 Nd0 cur)
    (hbre : M11.ByteRegionEffect cur cpost [bufferRegion cur ("mpt_key_scratch", 16)]) :
    BmiMptInv s0 S0 Nd0 cpost := by
  set mark := globN s0 "heap_ptr"
  obtain ⟨hm16, Nm, _, ⟨⟨hm_al, hm_w, hm_tab, hm_fix, hm_nh, hm_root, hm_ext⟩, hm_vs⟩, hdN, hspan⟩ := hinv
  obtain ⟨hWT_post, hne_post, hfp_post, hfix_post⟩ := bmi4_world_from_eff hready0 heff_post
  obtain ⟨⟨_, _, hF_cur, _⟩, hne_cur, hfp_cur, hfix_cur⟩ := bmi4_world_from_eff hready0 heff_cur
  have hg_eq : ∀ g, globN cpost g = globN cur g := fun g => by simp [globN, hbre.globals]
  have hag : AllocatorGrows cur cpost :=
    ⟨by rw [hg_eq "heap_ptr"], by rw [hg_eq "scratch_ptr"]⟩
  have hfix_ks : bufferRegion cur ("mpt_key_scratch", 16) ∈ fixedObjects cur :=
    bmi4_buf_in_fixedObjects cur ("mpt_key_scratch", 16) (by decide)
  have hu_obj : ∀ o ∈ mptObjIvls cur Nm mark, o.2 ≠ 0 → P3MptSet.IvlUnhit cur cpost o := by
    intro o ho hpos a _ hhit
    apply hbre.cell_frame a
    intro x hx hcx
    simp only [List.mem_singleton] at hx
    subst hx
    have hdj : Disj o (bufferRegion cur ("mpt_key_scratch", 16)) := by
      rcases List.mem_cons.1 ho with rfl | ho'
      · exact hm_fix _ hfix_ks
      · exact (hm_ext o ho').2.2 _ hfix_ks
    have hks_sz : (bufferRegion cur ("mpt_key_scratch", 16)).2 = 16 := by
      have hnz : globN cur "mpt_key_scratch" ≠ 0 := by
        rw [bmi4_glob_eq heff_cur "mpt_key_scratch" (by decide) (by decide)]
        exact hready0.2.2.2.2.2.2.1
      simp [bufferRegion, hnz]
    have hks_al : (bufferRegion cur ("mpt_key_scratch", 16)).1 % 8 = 0 := by
      rcases hF_cur.1 _ hfix_ks with h0 | ⟨_, hw⟩
      · omega
      · exact hw.1
    obtain ⟨_, _⟩ := hhit; obtain ⟨_, _⟩ := hcx
    rcases hdj with h0 | h0 | h | h <;> (dsimp at *; omega)
  have hu_m : P3MptSet.IvlUnhit cur cpost (mark, 16) :=
    hu_obj _ List.mem_cons_self (by simp)
  have hm_hi : mark + 16 ≤ 2 ^ 64 :=
    P3MptSet.ivl_allocated_bound heff_cur.arena.2 hm_al
  have hm_root_eq : memW cpost mark = memW cur mark :=
    P3MptSet.memW_eq_of_ivlUnhit hu_m hm_w.1 hm_hi ⟨by omega, by omega⟩
  have hm_nh_post : NodeHeap cpost Nm :=
    P3MptSet.nodeHeap_congr_unhit heff_cur.arena.1 heff_post.arena.1 hbre.be hag hm_nh
      (fun o ho hpos => hu_obj o (List.mem_cons_of_mem _ ho) hpos)
  have hne_nm_eq : nodeExtents cpost Nm = nodeExtents cur Nm := by
    unfold nodeExtents
    apply List.flatMap_congr
    intro nd hnd
    obtain ⟨_, _, hin_nd, hw_nd, _⟩ := hm_nh.1 nd hnd
    have hhi_nd : nd + nodeSize (memW cur nd) ≤ 2 ^ 64 := by
      have : heapLimit ≤ 2 ^ 64 := by decide
      have : nd + nodeSize (memW cur nd) ≤ heapLimit := hin_nd.2
      omega
    have hsz_ge : 32 ≤ nodeSize (memW cur nd) := by unfold nodeSize; split_ifs <;> omega
    have hu_nd : P3MptSet.IvlUnhit cur cpost (nd, nodeSize (memW cur nd)) :=
      hu_obj _ (List.mem_cons_of_mem _
        (by unfold nodeExtents; exact List.mem_flatMap.2 ⟨nd, hnd, by simp [nodeIvl]⟩))
        (by dsimp only; omega)
    have hw0 : memW cpost nd = memW cur nd :=
      P3MptSet.memW_eq_of_ivlUnhit hu_nd hw_nd.1 hhi_nd ⟨by omega, by omega⟩
    have hni_eq : nodeIvl cpost nd = nodeIvl cur nd := by simp [nodeIvl, hw0]
    have hnp_eq : nodePath cpost nd = nodePath cur nd := by
      unfold nodePath; rw [hw0]
      by_cases h12 : memW cur nd = 1 ∨ memW cur nd = 2
      · have h56 : 56 ≤ nodeSize (memW cur nd) := by
          unfold nodeSize; rcases h12 with h1 | h2
          · simp [h1]
          · simp [h2]
        have hnd8 : nd % 8 = 0 := hw_nd.1
        have hw32 : memW cpost (nd + 32) = memW cur (nd + 32) :=
          P3MptSet.memW_eq_of_ivlUnhit hu_nd (by omega) hhi_nd ⟨by omega, by omega⟩
        have hw40 : memW cpost (nd + 40) = memW cur (nd + 40) :=
          P3MptSet.memW_eq_of_ivlUnhit hu_nd (by omega) hhi_nd ⟨by omega, by omega⟩
        rw [hw32, hw40]
      · simp [h12]
    rw [hni_eq, hnp_eq]
  have hhbe0 : HeapByteEff cur cpost [bufferRegion cur ("mpt_key_scratch", 16)] ([] : List String) :=
    HeapByteEff.of_m11_bre heff_cur.arena hbre
  have hhbe : HeapByteEff cur cpost
      (nodeCacheIvls Nm ++ keccakBufIvls cur ++ [bufferRegion cur ("mpt_key_scratch", 16)])
      ([] : List String) :=
    bmi4_hbe_mono_rl hhbe0 (fun iv hiv => List.mem_append_right _ hiv)
  have hkc_eq : keccakBufIvls cpost = keccakBufIvls cur := by
    unfold keccakBufIvls bufferRegion; simp [hg_eq]
  have hm_vs_post : NodeHeapValuePtrOK cpost Nm := by
    unfold NodeHeapValuePtrOK; rw [hg_eq "scratch_ptr"]
    refine nodeValuesSafe_of_heapByteEff heff_cur.arena hm_nh hhbe hkc_eq ?_ ?_ hm_vs
    · intro e he _ o ho
      simp only [List.mem_singleton] at he; subst he
      exact Disj.flip ((hm_ext o ho).2.2 _ hfix_ks)
    · intro o ho
      exact ⟨Disj.flip ((hm_ext o ho).2.2 _ (bmi4_buf_in_fixedObjects cur ("keccak_pad", 136) (by decide))),
             Disj.flip ((hm_ext o ho).2.2 _ (bmi4_buf_in_fixedObjects cur ("keccak_st", 200) (by decide)))⟩
  refine ⟨by rw [hg_eq "heap_ptr"]; exact hm16, Nm, hWT_post, ⟨⟨hag.allocated hm_al,
    P3MptSet.wordsOK_transfer heff_cur.arena.1 heff_post.arena.1 hm_w, ?_, ?_, hm_nh_post,
    by rw [hm_root_eq]; exact hm_root, ?_⟩, hm_vs_post⟩, ?_, ?_⟩
  · intro u hu iv hiv; rw [hfp_post u hu, ← hfp_cur u hu] at hiv; exact hm_tab u hu iv hiv
  · rw [hfix_post, ← hfix_cur]; exact hm_fix
  · rw [hne_nm_eq]
    intro o ho
    refine ⟨(hm_ext o ho).1, ?_, ?_⟩
    · intro u hu iv hiv; rw [hfp_post u hu, ← hfp_cur u hu] at hiv; exact (hm_ext o ho).2.1 u hu iv hiv
    · rw [hfix_post, ← hfix_cur]; exact (hm_ext o ho).2.2
  · rw [hne_nm_eq, hne_post, ← hne_cur]; exact hdN
  · rw [hne_nm_eq, hg_eq "heap_ptr"]; exact hspan

private theorem bmi4_mptObjReadyStrong {F : Type}
    {s0 entry : PanSemStateFiniteExact 64 F} {S0 Nd0 : List Nat}
    (heff_e : R16Shards.WorldEff s0 entry (bmi4Rl s0) [] (bmiWkGw : List String))
    (hinv_e : BmiMptInv s0 S0 Nd0 entry) (hm_loc : locN entry "m" = globN s0 "heap_ptr") :
    MptObjReadyStrong entry := by
  obtain ⟨_, Nm, hWT, hmObj, hdN, _⟩ := hinv_e; rw [← hm_loc] at hmObj hdN
  refine ⟨heff_e.arena, S0, (worldTyped_iff_with entry S0).2 ⟨Nd0, hWT⟩, ⟨Nm, hmObj⟩,
    (fun i hi => by simp at hi), ⟨Nd0, hWT.2.2.2, fun o ho j hj => ?_⟩, Nm, Nd0, hmObj, hWT.2.2.2,
    fun o ho j hj => hdN o (by simpa using ho) j hj⟩
  simp only [List.mem_singleton] at ho; subst o; exact hdN _ List.mem_cons_self j hj

private theorem bmi4_mptSetReadyStrong {F : Type}
    {s0 entry : PanSemStateFiniteExact 64 F} {S0 Nd0 : List Nat} {idx : Nat}
    (hready0 : BmiReadyG s0 S0 Nd0)
    (heff_e : R16Shards.WorldEff s0 entry (bmi4Rl s0) [] (bmiWkGw : List String))
    (hinv_e : BmiMptInv s0 S0 Nd0 entry) (hm_loc : locN entry "m" = globN s0 "heap_ptr")
    (hklen : locN entry "klen" ≤ 32) (hidx : idx < locN s0 "n")
    (hvptr : locN entry "vptr" = memW s0 (locN s0 "slice_arr" + 16 * idx))
    (hvlen : locN entry "vlen" = memW s0 (locN s0 "slice_arr" + 16 * idx + 8)) :
    MptSetReadyStrong entry := by
  have hobj := bmi4_mptObjReadyStrong heff_e hinv_e hm_loc
  obtain ⟨hm16, Nm, hWT, hmObj, hdN, hspan⟩ := hinv_e
  have hmObj' : MptObjInWithStrong entry S0 Nm (locN entry "m") := by rwa [hm_loc]
  refine ⟨hobj, hklen, by rw [hvlen]; exact hready0.1.2.2.2.2.2.2 idx hidx, S0, Nm, hmObj', ?_⟩
  intro _ _
  have hvptr_hi : locN entry "vptr" + 8 ≤ globN s0 "heap_ptr" := by
    rw [hvptr]; exact hready0.2.2.2.2.2.2.2.1 idx hidx
  have hkc_eq : keccakBufIvls entry = keccakBufIvls s0 := by
    unfold keccakBufIvls bufferRegion
    rw [bmi4_glob_eq heff_e "keccak_pad" (by decide) (by decide),
        bmi4_glob_eq heff_e "keccak_st" (by decide) (by decide)]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro nd hnd
    have hsz : 32 ≤ nodeSize (memW entry nd) := by unfold nodeSize; split_ifs <;> omega
    have hne_mem : nodeIvl entry nd ∈ nodeExtents entry Nm := by
      unfold nodeExtents; exact List.mem_flatMap.2 ⟨nd, hnd, by simp [nodeIvl]⟩
    have hnd_lo := (hspan (nodeIvl entry nd) hne_mem (by dsimp [nodeIvl]; omega)).1
    dsimp [nodeIvl] at hnd_lo; unfold InIvl; dsimp only; omega
  · intro iv hiv hpos; rw [hkc_eq] at hiv; rw [hvptr]
    exact hready0.2.2.2.2.2.2.2.2 idx hidx iv hiv hpos
  · unfold InIvl freeGap; dsimp only
    have hfmp := heff_e.fmp_eq; have hss : heapLimit ≤ scratchStart := by decide
    have h1 := hready0.1.1.1.2.2.1; have h2 := hready0.1.1.1.2.2.2.1; omega
  · unfold InIvl heapFree; dsimp only; have := heff_e.hp_lo; omega

private theorem bmi4_mptRm_in_rl {F : Type} {s0 entry : PanSemStateFiniteExact 64 F}
    (heff_e : R16Shards.WorldEff s0 entry (bmi4Rl s0) [] (bmiWkGw : List String))
    (hm_loc : locN entry "m" = globN s0 "heap_ptr") :
    ∀ i ∈ bmiWkMptRm entry, 0 < i.2 →
      ∃ j ∈ bmi4Rl s0, 0 < j.2 ∧ j.1 ≤ i.1 ∧ i.1 + i.2 ≤ j.1 + j.2 := by
  intro i hi hpos
  have hkp := bmi4_glob_eq heff_e "keccak_pad" (by decide) (by decide)
  have hks := bmi4_glob_eq heff_e "keccak_st" (by decide) (by decide)
  have hmh := bmi4_glob_eq heff_e "mpt_hash_scratch" (by decide) (by decide)
  simp only [bmiWkMptRm, bmiWkKeccakR, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · refine ⟨(globN s0 "heap_ptr", heapLimit - globN s0 "heap_ptr"),
      List.mem_append_right _ List.mem_cons_self, ?_, by dsimp only; omega, ?_⟩ <;>
      (have := heff_e.arena.2.2.1; dsimp only at hpos ⊢; omega)
  · refine ⟨(globN s0 "keccak_pad", if globN s0 "keccak_pad" = 0 then 0 else 136),
      List.mem_append_left _ (by simp [bmiWkRti]), ?_, ?_, ?_⟩
    · unfold bufferRegion at hpos; rw [← hkp]; dsimp only at hpos ⊢; omega
    · unfold bufferRegion; rw [← hkp]
    · unfold bufferRegion; rw [← hkp]
  · refine ⟨(globN s0 "keccak_st", if globN s0 "keccak_st" = 0 then 0 else 200),
      List.mem_append_left _ (by simp [bmiWkRti]), ?_, ?_, ?_⟩
    · unfold bufferRegion at hpos; rw [← hks]; dsimp only at hpos ⊢; omega
    · unfold bufferRegion; rw [← hks]
    · unfold bufferRegion; rw [← hks]
  · refine ⟨(globN s0 "mpt_hash_scratch", if globN s0 "mpt_hash_scratch" = 0 then 0 else 40),
      List.mem_append_left _ (by simp [bmiWkRti]), ?_, ?_, ?_⟩
    · unfold bufferRegion at hpos; rw [← hmh]; dsimp only at hpos ⊢; omega
    · unfold bufferRegion; rw [← hmh]
    · unfold bufferRegion; rw [← hmh]

private theorem bmi4_we_of_mpt_set_eff {F : Type}
    {s0 entry cpost : PanSemStateFiniteExact 64 F} {S0 Nd0 : List Nat}
    (heff_e : R16Shards.WorldEff s0 entry (bmi4Rl s0) [] (bmiWkGw : List String))
    (hinv_e : BmiMptInv s0 S0 Nd0 entry) (hm_loc : locN entry "m" = globN s0 "heap_ptr")
    (heff_set : MptEffStrong mptSetR_sc mptSetB_sc ["heap_ptr", "scratch_ptr"] entry cpost)
    (hcpost_eq : cpost = (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_mpt_set)).2) :
    R16Shards.WorldEff s0 cpost (bmi4Rl s0) [] (bmiWkGw : List String) := by
  obtain ⟨hm16, Nm, _, ⟨⟨hm_al, hm_w, _, hm_fix, hm_nh, hm_root, hm_ext⟩, hm_vs⟩, _, hspan⟩ := hinv_e
  rw [← hm_loc] at hm_al hm_w hm_root hm_ext
  have hB_fix : ∀ gs ∈ mptSetB_sc, bufferRegion entry gs ∈ fixedObjects entry := by
    intro gs hgs
    refine bmi4_buf_in_fixedObjects entry gs ?_
    simp only [mptSetB_sc, List.mem_cons, List.not_mem_nil, or_false] at hgs
    rcases hgs with rfl | rfl | rfl <;> decide
  obtain ⟨hcell5, hbyte5⟩ := heff_set.write_frame Nm hm_al hm_w hm_nh hm_vs hm_root
    (fun o ho => ⟨(hm_ext o ho).1, fun gs hgs => (hm_ext o ho).2.2 _ (hB_fix gs hgs)⟩)
    (fun gs hgs => by rw [hm_loc]; exact hm_fix _ (hB_fix gs hgs))
  have hspan_obj : ∀ o ∈ mptObjIvls entry Nm (locN entry "m"), 0 < o.2 →
      locN entry "m" ≤ o.1 ∧ o.1 + o.2 ≤ globN entry "heap_ptr" := by
    intro o ho hpos
    rcases List.mem_cons.1 ho with rfl | ho'
    · exact ⟨le_rfl, by dsimp only; omega⟩
    · rw [hm_loc]; exact hspan o ho' hpos
  have hmemR : ∀ ivl ∈ mptSetR_sc entry, ivl ∈ bmiWkMptRm entry := by
    intro ivl hivl; simp only [bmiWkMptRm, bmiWkKeccakR_eq_mptSetR_sc]
    exact List.mem_cons_of_mem _ hivl
  have hmemB : ∀ gs ∈ mptSetB_sc, bufferRegion entry gs ∈ bmiWkMptRm entry := by
    intro gs hgs
    simp only [mptSetB_sc, List.mem_cons, List.not_mem_nil, or_false] at hgs
    rcases hgs with rfl | rfl | rfl <;>
      simp [bufferRegion, bmiWkMptRm, bmiWkKeccakR]
  have hmeta := evaluateHOLFiniteState_metadata entry (sourceFnBody Guest.Software.guestFn_mpt_set)
  rw [← hcpost_eq] at hmeta
  refine bmiWk_we_callee_mpt (Rm := bmiWkMptRm) (Wown := []) heff_e
    (bmi4_mptRm_in_rl heff_e hm_loc) (by simp) heff_set.arena heff_set.grows.1 heff_set.grows.2
    ?_ ?_ (fun k hk => heff_set.gw_kept k (by simpa [bmiWkGw] using hk))
    (hmeta.1.trans heff_e.code) ⟨hmeta.2.1, hmeta.2.2.1, hmeta.2.2.2.2⟩ heff_set.dom_wr
  · intro a hne
    rcases hcell5 a hne with ⟨ivl, hivl, hc⟩ | ⟨gs, hgs, hc⟩ | ⟨o, ho, hc⟩ | hfg | hhf
    · exact Or.inl ⟨ivl, hmemR ivl hivl, hc.1, hc.2.1, hc.2.2⟩
    · exact Or.inl ⟨bufferRegion entry gs, hmemB gs hgs, hc.1, hc.2.1, hc.2.2⟩
    · obtain ⟨hlo, hhi⟩ := hspan_obj o ho hc.1
      exact Or.inl ⟨(locN entry "m", globN entry "heap_ptr" - locN entry "m"),
        List.mem_cons_self, by dsimp only; omega, by dsimp only; have := hc.2.1; omega,
        by dsimp only; have := hc.2.2; omega⟩
    · obtain ⟨h0, h1, h2⟩ := hfg; dsimp [freeGap] at h0 h1 h2
      exact Or.inr (Or.inr (Or.inl ⟨h0, h1, by omega⟩))
    · obtain ⟨h0, h1, h2⟩ := hhf; dsimp [heapFree] at h0 h1 h2
      exact Or.inr (Or.inr (Or.inr ⟨h0, h1, by omega⟩))
  · intro b hb64 hne
    rcases hbyte5 b hb64 hne with ⟨ivl, hivl, hi⟩ | ⟨gs, hgs, hi⟩ | ⟨o, ho, hi⟩ | hfg | hhf
    · exact Or.inl ⟨ivl, hmemR ivl hivl, by dsimp [InIvl] at hi; omega, hi.1, hi.2⟩
    · exact Or.inl ⟨bufferRegion entry gs, hmemB gs hgs, by dsimp [InIvl] at hi; omega, hi.1, hi.2⟩
    · obtain ⟨hlo, hhi⟩ := hspan_obj o ho (by dsimp [InIvl] at hi; omega)
      exact Or.inl ⟨(locN entry "m", globN entry "heap_ptr" - locN entry "m"),
        List.mem_cons_self, by dsimp only; omega, by dsimp [InIvl] at hi ⊢; omega,
        by dsimp [InIvl] at hi ⊢; omega⟩
    · exact Or.inr (Or.inr (Or.inl ⟨by dsimp [InIvl, freeGap] at hfg; omega, hfg.1,
        by dsimp [InIvl, freeGap] at hfg; omega⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨by dsimp [InIvl, heapFree] at hhf; omega, hhf.1,
        by dsimp [InIvl, heapFree] at hhf; omega⟩))

private theorem bmi4_mptInv_after_set {F : Type}
    {s0 entry cpost : PanSemStateFiniteExact 64 F} {S0 Nd0 : List Nat} (hready0 : BmiReadyG s0 S0 Nd0)
    (heff_e : R16Shards.WorldEff s0 entry (bmi4Rl s0) [] (bmiWkGw : List String))
    (heff_post : R16Shards.WorldEff s0 cpost (bmi4Rl s0) [] (bmiWkGw : List String))
    (hinv_e : BmiMptInv s0 S0 Nd0 entry) (hm_loc : locN entry "m" = globN s0 "heap_ptr")
    (heff_set : MptEffStrong mptSetR_sc mptSetB_sc ["heap_ptr", "scratch_ptr"] entry cpost) :
    BmiMptInv s0 S0 Nd0 cpost := by
  set mark := globN s0 "heap_ptr"
  obtain ⟨hm16, Nm, hWT_e, ⟨⟨hm_al, hm_w, hm_tab, hm_fix, hm_nh, hm_root, hm_ext⟩, hm_vs⟩, hdN, hspan⟩ := hinv_e
  obtain ⟨hWT_post, hne_post, hfp_post, hfix_post⟩ := bmi4_world_from_eff hready0 heff_post
  obtain ⟨_, hne_e, hfp_e, hfix_e⟩ := bmi4_world_from_eff hready0 heff_e
  have hB_fix : ∀ gs ∈ mptSetB_sc, bufferRegion entry gs ∈ fixedObjects entry := fun gs hgs => by
    refine bmi4_buf_in_fixedObjects entry gs ?_
    simp only [mptSetB_sc, List.mem_cons, List.not_mem_nil, or_false] at hgs
    rcases hgs with rfl | rfl | rfl <;> decide
  have hR_fix : ∀ ivl ∈ mptSetR_sc entry, ivl ∈ fixedObjects entry := fun ivl hivl => by
    simp only [mptSetR_sc, List.mem_cons, List.not_mem_nil, or_false] at hivl
    rcases hivl with rfl | rfl | rfl
    · exact hB_fix ("keccak_pad", 136) (by simp [mptSetB_sc])
    · exact hB_fix ("keccak_st", 200) (by simp [mptSetB_sc])
    · exact hB_fix ("mpt_hash_scratch", 40) (by simp [mptSetB_sc])
  have hm_al' : Allocated entry (locN entry "m", 16) := by rwa [hm_loc]
  have hm_w' : WordsOK entry (locN entry "m", 16) := by rwa [hm_loc]
  have hm_root' : RootIn Nm (memW entry (locN entry "m")) := by rwa [hm_loc]
  have hdisj_R_obj : IvlsDisj (mptSetR_sc entry) (mptObjIvls entry Nm (locN entry "m")) := fun ivl hivl o ho => by
    rw [hm_loc] at ho
    rcases List.mem_cons.1 ho with rfl | ho'
    · exact Disj.flip (hm_fix ivl (hR_fix ivl hivl))
    · exact Disj.flip ((hm_ext o ho').2.2 ivl (hR_fix ivl hivl))
  obtain ⟨Nm', hNH_Nm', hVS_Nm', hRoot_Nm', hExt_Nm'⟩ :=
    heff_set.obj_pres Nm hm_al' hm_w' hm_nh hm_vs hm_root'
      (fun o ho => ⟨by rw [hm_loc]; exact (hm_ext o ho).1, fun gs hgs => (hm_ext o ho).2.2 _ (hB_fix gs hgs)⟩)
      (fun gs hgs => by rw [hm_loc]; exact hm_fix _ (hB_fix gs hgs)) hdisj_R_obj
  rw [hm_loc] at hRoot_Nm'
  refine ⟨le_trans hm16 heff_set.grows.1, Nm', hWT_post,
    ⟨⟨heff_set.grows.allocated hm_al, P3MptSet.wordsOK_transfer heff_e.arena.1 heff_post.arena.1 hm_w,
      ?_, ?_, hNH_Nm', hRoot_Nm', ?_⟩, hVS_Nm'⟩, ?_, ?_⟩
  · intro u hu i hi; rw [hfp_post u hu, ← hfp_e u hu] at hi; exact hm_tab u hu i hi
  · rw [hfix_post, ← hfix_e]; exact hm_fix
  · intro o ho
    rcases hExt_Nm' o ho with rfl | ⟨j, hj, hin_j⟩ | hin_fr
    · exact ⟨Or.inl rfl, fun _ _ _ _ => Or.inl rfl, fun _ _ => Or.inl rfl⟩
    · refine ⟨R13MptKeepsTwin.disj_inside_left hin_j (hm_ext j hj).1, ?_, ?_⟩
      · intro u hu i hi; rw [hfp_post u hu, ← hfp_e u hu] at hi
        exact R13MptKeepsTwin.disj_inside_left hin_j ((hm_ext j hj).2.1 u hu i hi)
      · rw [hfix_post, ← hfix_e]; intro f hf
        exact R13MptKeepsTwin.disj_inside_left hin_j ((hm_ext j hj).2.2 f hf)
    · refine ⟨R13MptKeepsTwin.disj_fresh_heap_allocated heff_e.arena.2 heff_post.arena.2 hin_fr (Or.inr hm_al), ?_, ?_⟩
      · intro u hu i hi; rw [hfp_post u hu, ← hfp_e u hu] at hi
        exact R13MptKeepsTwin.disj_fresh_heap_allocated heff_e.arena.2 heff_post.arena.2 hin_fr
          (Or.inr (((hWT_e.1.2.1 u hu).2 i hi).1))
      · rw [hfix_post, ← hfix_e]; intro f hf
        exact R13MptKeepsTwin.disj_fresh_heap_allocated heff_e.arena.2 heff_post.arena.2 hin_fr
          ((hWT_e.2.2.1.1 f hf).elim Or.inl (fun h => Or.inr h.1))
  · rw [hne_post, ← hne_e]; intro o ho p hp
    have hp_al : p.2 = 0 ∨ Allocated entry p := by
      unfold nodeExtents at hp; obtain ⟨n, hn, hnp⟩ := List.mem_flatMap.1 hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hnp
      rcases hnp with rfl | rfl
      · exact Or.inr (hWT_e.2.2.2.1.1 n hn).2.1
      · unfold nodePath; split
        · rename_i hcond
          rcases (hWT_e.2.2.2.1.1 n hn).2.2.2.2.2.2.1 hcond.1 with h0 | ⟨_, hal, _⟩
          · exact absurd h0 hcond.2
          · exact Or.inr hal
        · exact Or.inl rfl
    rcases List.mem_cons.1 ho with rfl | ho_ne
    · exact hdN _ List.mem_cons_self p hp
    · rcases hExt_Nm' o ho_ne with rfl | ⟨j, hj, hin_j⟩ | hin_fr
      · exact Or.inl rfl
      · exact R13MptKeepsTwin.disj_inside_left hin_j (hdN j (List.mem_cons_of_mem _ hj) p hp)
      · exact R13MptKeepsTwin.disj_fresh_heap_allocated heff_e.arena.2 heff_post.arena.2 hin_fr hp_al
  · intro o ho hpos
    rcases hExt_Nm' o ho with rfl | ⟨j, hj, hin_j⟩ | hin_fr
    · simp at hpos
    · have hj_sp := hspan j hj (by dsimp [Inside] at hin_j; omega)
      have := heff_set.grows.1; dsimp [Inside] at hin_j; omega
    · have := heff_e.hp_lo; dsimp [Inside] at hin_fr; omega

private structure BmiLoopInv {F : Type} (s0 : PanSemStateFiniteExact 64 F) (S0 Nd0 : List Nat)
    (t : PanSemStateFiniteExact 64 F) : Prop where
  mptInv   : BmiMptInv s0 S0 Nd0 t
  wmark_lk : ∃ w : BitVec 64, t.locals.lookup (ofString "mark") = some (.val (.word w)) ∧ w.toNat = globN s0 "heap_ptr"
  wm_lk    : ∃ w : BitVec 64, t.locals.lookup (ofString "m") = some (.val (.word w)) ∧ w.toNat = globN s0 "heap_ptr"
  wsa_lk   : ∃ w : BitVec 64, t.locals.lookup (ofString "slice_arr") = some (.val (.word w)) ∧ w.toNat = locN s0 "slice_arr"
  wn_lk    : ∃ w : BitVec 64, t.locals.lookup (ofString "n") = some (.val (.word w)) ∧ w.toNat = locN s0 "n"
  wout_lk  : ∃ w : BitVec 64, t.locals.lookup (ofString "out") = some (.val (.word w)) ∧ w.toNat = locN s0 "out"
  wi_lk    : ∃ w : BitVec 64, t.locals.lookup (ofString "i") = some (.val (.word w))

private theorem bmiLoopInv_decClock {F : Type} {s0 t : PanSemStateFiniteExact 64 F} {S0 Nd0 : List Nat}
    (h : BmiLoopInv s0 S0 Nd0 t) : BmiLoopInv s0 S0 Nd0 (decClockHOLFinite t) :=
  ⟨bmi4_mptInv_locals_clock h.mptInv t.locals (t.clock - 1),
   h.wmark_lk, h.wm_lk, h.wsa_lk, h.wn_lk, h.wout_lk, h.wi_lk⟩

private theorem bmi4_while_ind {F : Type} {s : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {B : List (String × Nat)} {gw : List String}
    (cond : ExpHOL 64) {body : ProgHOL 64} (Inv : PanSemStateFiniteExact 64 F → Prop)
    (hdec : ∀ t, Inv t → Inv (decClockHOLFinite t))
    (hb : ∀ t (cw : BitVec 64),
      @evalHOLFinite 64 F _ t (fun a => Classical.propDecidable (t.memaddrs a)) cond = some (.val (.word cw)) →
      cw ≠ 0 → R16Shards.WorldEff s (decClockHOLFinite t) Rl B gw → Inv (decClockHOLFinite t) →
      (evaluateHOLFiniteState (decClockHOLFinite t) body).1 ≠ some .timeOut →
      ContOrRes (evaluateHOLFiniteState (decClockHOLFinite t) body).1 →
      R16Shards.WorldEff s (evaluateHOLFiniteState (decClockHOLFinite t) body).2 Rl B gw ∧
      (((evaluateHOLFiniteState (decClockHOLFinite t) body).1 = none ∨
        (evaluateHOLFiniteState (decClockHOLFinite t) body).1 = some .continue) →
        Inv (evaluateHOLFiniteState (decClockHOLFinite t) body).2)) :
    ∀ (k : Nat) (cur : PanSemStateFiniteExact 64 F), cur.clock = k →
      R16Shards.WorldEff s cur Rl B gw → Inv cur →
      (evaluateHOLFiniteState cur (.while cond body)).1 ≠ some .timeOut →
      ContOrRes (evaluateHOLFiniteState cur (.while cond body)).1 →
      R16Shards.WorldEff s (evaluateHOLFiniteState cur (.while cond body)).2 Rl B gw ∧
      ((evaluateHOLFiniteState cur (.while cond body)).1 = none →
        (∀ t, Inv t → (evaluateHOLFiniteState t body).1 ≠ some .break) →
        Inv (evaluateHOLFiniteState cur (.while cond body)).2) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro cur hclk heff hinv hnt hcr
    have hw_eq := evaluateHOLFiniteState_while_fixClockRewrite cur cond body
    rcases hc : @evalHOLFinite 64 F _ cur (fun a => Classical.propDecidable (cur.memaddrs a)) cond with _ | cv
    · rw [hc] at hw_eq; simp only [hw_eq]; exact ⟨heff, fun hnone _ => by simp at hnone⟩
    · rcases cv with ⟨⟨cw⟩⟩ | _ | _ <;>
        try (rw [hc] at hw_eq; simp only [hw_eq]; exact ⟨heff, fun hnone _ => by simp at hnone⟩)
      rw [hc] at hw_eq; dsimp only at hw_eq
      by_cases hw0 : cw = 0
      · subst hw0; rw [if_neg (by simp)] at hw_eq; rw [hw_eq]; exact ⟨heff, fun _ _ => hinv⟩
      · rw [if_pos hw0] at hw_eq
        by_cases hk0 : cur.clock = 0
        · rw [if_pos hk0] at hw_eq; rw [hw_eq] at hnt; exact absurd rfl hnt
        · rw [if_neg hk0] at hw_eq
          have heff_d : R16Shards.WorldEff s (decClockHOLFinite cur) Rl B gw :=
            heff.locals_clock cur.locals (cur.clock - 1)
          have hinv_d : Inv (decClockHOLFinite cur) := hdec cur hinv
          have hrem := evaluateHOLFiniteState_clock_le (decClockHOLFinite cur) body
          rcases hbo : evaluateHOLFiniteState (decClockHOLFinite cur) body with ⟨rb, sb⟩
          rw [hbo] at hw_eq hrem
          have hlt : sb.clock < k := by change sb.clock ≤ cur.clock - 1 at hrem; omega
          cases rb with
          | none =>
            dsimp only at hw_eq
            obtain ⟨heff_b, hinv_b⟩ := hb cur cw hc hw0 heff_d hinv_d
              (by rw [hbo]; simp) (by rw [hbo]; exact Or.inl rfl)
            rw [hbo] at heff_b hinv_b; rw [hw_eq] at hnt hcr ⊢
            exact ih sb.clock hlt sb rfl heff_b (hinv_b (Or.inl rfl)) hnt hcr
          | some r1 =>
            cases r1 with
            | «continue» =>
              dsimp only at hw_eq
              obtain ⟨heff_b, hinv_b⟩ := hb cur cw hc hw0 heff_d hinv_d
                (by rw [hbo]; simp) (by rw [hbo]; exact Or.inr (Or.inr (Or.inl rfl)))
              rw [hbo] at heff_b hinv_b; rw [hw_eq] at hnt hcr ⊢
              exact ih sb.clock hlt sb rfl heff_b (hinv_b (Or.inr rfl)) hnt hcr
            | «break» =>
              dsimp only at hw_eq; rw [hw_eq]
              obtain ⟨heff_b, _⟩ := hb cur cw hc hw0 heff_d hinv_d
                (by rw [hbo]; simp) (by rw [hbo]; exact Or.inr (Or.inl rfl))
              rw [hbo] at heff_b
              exact ⟨heff_b, fun _ hno_brk => absurd (by rw [hbo]) (hno_brk (decClockHOLFinite cur) hinv_d)⟩
            | timeOut => dsimp only at hw_eq; rw [hw_eq] at hnt; exact absurd rfl hnt
            | returned v =>
              dsimp only at hw_eq; rw [hw_eq]
              obtain ⟨heff_b, _⟩ := hb cur cw hc hw0 heff_d hinv_d
                (by rw [hbo]; simp) (by rw [hbo]; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨v, rfl⟩))))
              rw [hbo] at heff_b; exact ⟨heff_b, fun h _ => by simp at h⟩
            | exception eid ev =>
              dsimp only at hw_eq; rw [hw_eq] at hcr ⊢
              have hres_e : Resumes (some (.exception eid ev)) := by
                rcases hcr with h | h | h | hr <;> [cases h; cases h; cases h; exact hr]
              obtain ⟨heff_b, _⟩ := hb cur cw hc hw0 heff_d hinv_d
                (by rw [hbo]; simp) (by rw [hbo]; exact Or.inr (Or.inr (Or.inr hres_e)))
              rw [hbo] at heff_b; exact ⟨heff_b, fun h _ => by simp at h⟩
            | error =>
              dsimp only at hw_eq; rw [hw_eq] at hcr
              rcases hcr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> cases h
            | finalFfi _ =>
              dsimp only at hw_eq; rw [hw_eq] at hcr
              rcases hcr with h | h | h | ⟨⟨_, h⟩ | ⟨_, _, h, _⟩⟩ <;> cases h

private theorem call0_not_brk_cont {F : Type} (u : PanSemStateFiniteExact 64 F)
    (fname : MlS) (args : List (ExpHOL 64)) (r : PanSemResultExact 64) (hr : r = .break ∨ r = .continue) :
    (evaluateHOLFiniteState u (.call (some (none, none)) fname args)).1 ≠ some r := by
  rcases hr with rfl | rfl <;>
  · rw [evaluateHOLFiniteState_call]
    rcases hargs : evalListHOLFinite u (h := fun a => Classical.propDecidable (u.memaddrs a)) args with _ | vs
    · simp
    · dsimp only
      rcases hl : lookupCodeHOLFinite u.code.lookup fname vs with _ | ⟨b, c, ret⟩
      · simp
      · dsimp only
        split
        · simp
        · rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite u c) b with ⟨br, bp⟩
          cases br with
          | none => simp
          | some br' =>
            cases br' with
            | returned v => dsimp only; split <;> simp
            | _ => simp

private theorem bmi4_no_brk_cont {F : Type} (t : PanSemStateFiniteExact 64 F)
    (r : PanSemResultExact 64) (hr : r = .break ∨ r = .continue) :
    (evaluateHOLFiniteState t bmi4LoopBody).1 ≠ some r := by
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
  rcases hargs : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) bmi4RlpArgs with _ | vals
  · rcases hr with rfl | rfl <;> simp
  · dsimp only
    rcases hl : lookupCodeHOLFinite t.code.lookup (ofString "rlp_encode_word") vals with _ | ⟨b1, c1, r1⟩
    · rcases hr with rfl | rfl <;> simp
    · dsimp only
      split
      · rcases hr with rfl | rfl <;> simp
      · rcases hb1 : evaluateHOLFiniteState (callEntryStateHOLFinite t c1) b1 with ⟨br1, bp1⟩
        cases br1 with
        | none => rcases hr with rfl | rfl <;> simp
        | some br1' =>
          cases br1' with
          | returned v1 =>
            dsimp only
            split
            · dsimp only
              rw [evaluateHOLFiniteState_seq_line780]
              rcases hc2 : evaluateHOLFiniteState
                  (setVarHOLFinite (ofString "klen") v1 { bp1 with locals := t.locals })
                  (.call (some (none, none)) (ofString "mpt_set") bmi4SetArgs) with ⟨r2, m2⟩
              cases r2 with
              | none =>
                dsimp only
                rw [evaluateHOLFiniteState_assign]
                rcases hr with rfl | rfl <;> (repeat' split) <;> simp
              | some r2' =>
                dsimp only
                have hnb := call0_not_brk_cont
                  (setVarHOLFinite (ofString "klen") v1 { bp1 with locals := t.locals })
                  (ofString "mpt_set") bmi4SetArgs r hr
                rw [hc2] at hnb
                exact hnb
            · rcases hr with rfl | rfl <;> simp
          | _ => rcases hr with rfl | rfl <;> simp

private theorem call0_none_locals {F : Type} (u : PanSemStateFiniteExact 64 F)
    (fname : MlS) (args : List (ExpHOL 64)) (m2 : PanSemStateFiniteExact 64 F)
    (h : evaluateHOLFiniteState u (.call (some (none, none)) fname args) = (none, m2)) :
    m2.locals = u.locals := by
  rw [evaluateHOLFiniteState_call] at h
  rcases hargs : evalListHOLFinite u (h := fun a => Classical.propDecidable (u.memaddrs a)) args with _ | vs
  · rw [hargs] at h; simp at h
  · rw [hargs] at h; dsimp only at h
    rcases hl : lookupCodeHOLFinite u.code.lookup fname vs with _ | ⟨b, c, ret⟩
    · rw [hl] at h; simp at h
    · rw [hl] at h; dsimp only at h
      split at h
      · simp at h
      · rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite u c) b with ⟨br, bp⟩
        rw [hb] at h
        cases br with
        | none => simp at h
        | some br' =>
          cases br' with
          | returned v =>
            dsimp only at h
            split at h
            · obtain ⟨_, heq⟩ := Prod.mk.inj h
              rw [← heq]
            · simp at h
          | _ => simp [emptyLocalsHOLFinite] at h

private theorem bmi4_mpt_set_callee {F : Type} {s0 u : PanSemStateFiniteExact 64 F} {S0 Nd0 : List Nat}
    (hready0 : BmiReadyG s0 S0 Nd0)
    (heff_u : R16Shards.WorldEff s0 u (bmi4Rl s0) [] (bmiWkGw : List String))
    (hinv_u : BmiMptInv s0 S0 Nd0 u) (wm wklen wsa wi wn : BitVec 64)
    (hwm : u.locals.lookup (ofString "m") = some (.val (.word wm))) (hm_nat : wm.toNat = globN s0 "heap_ptr")
    (hklen : u.locals.lookup (ofString "klen") = some (.val (.word wklen))) (hklen_le : wklen.toNat ≤ 32)
    (hwsa : u.locals.lookup (ofString "slice_arr") = some (.val (.word wsa)))
    (hwsa_nat : wsa.toNat = locN s0 "slice_arr")
    (hwi : u.locals.lookup (ofString "i") = some (.val (.word wi)))
    (hwn : u.locals.lookup (ofString "n") = some (.val (.word wn))) (hwn_nat : wn.toNat = locN s0 "n")
    (hidx : wi.toNat < locN s0 "n")
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (vals : List (ValueHOL 64))
    (hargs : evalListHOLFinite u (h := fun a => Classical.propDecidable (u.memaddrs a)) bmi4SetArgs = some vals)
    (hl : lookupCodeHOLFinite u.code.lookup (ofString "mpt_set") vals =
      some (sourceFnBody Guest.Software.guestFn_mpt_set, callee, .one))
    (hnt : (evaluateHOLFiniteState (callEntryStateHOLFinite u callee)
      (sourceFnBody Guest.Software.guestFn_mpt_set)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState (callEntryStateHOLFinite u callee)
      (sourceFnBody Guest.Software.guestFn_mpt_set)).1) :
    let cpost := (evaluateHOLFiniteState (callEntryStateHOLFinite u callee)
      (sourceFnBody Guest.Software.guestFn_mpt_set)).2
    R16Shards.WorldEff s0 cpost (bmi4Rl s0) [] (bmiWkGw : List String) ∧ BmiMptInv s0 S0 Nd0 cpost := by
  dsimp only
  obtain ⟨v1, v2, v3, v4, v5, he1, he2, he3, he4, he5, hc1, hc2, hc3, hc4, hc5⟩ :=
    callee_param_five_exp u (ofString "mpt_set")
      (ofString "m") (ofString "key") (ofString "klen") (ofString "vptr") (ofString "vlen")
      .one .one .one .one .one _ _ (by rw [heff_u.code]; exact P3MptSet.lookup_mpt_set)
      _ _ _ _ _ vals _ callee .one hargs hl
  have hm_cal : callee.lookup (ofString "m") = u.locals.lookup (ofString "m") :=
    hc1.trans (by simpa only [evalAt, evalHOLExact] using he1.symm)
  have hk_cal : callee.lookup (ofString "klen") = u.locals.lookup (ofString "klen") :=
    hc3.trans (by simpa only [evalAt, evalHOLExact] using he3.symm)
  have hsa_u : locN u "slice_arr" = locN s0 "slice_arr" := by simp [locN, hwsa, hwsa_nat]
  have hi_u : locN u "i" = wi.toNat := by simp [locN, hwi]
  have hn_u : locN u "n" = locN s0 "n" := by simp [locN, hwn, hwn_nat]
  obtain ⟨hsl_w, hsl_eq⟩ := bmi4_slice_eq hready0 heff_u
  have hin_u : Inside (locN u "slice_arr", 16 * locN u "n") sourceBase (globN u "heap_ptr") := by
    rw [hsa_u, hn_u]; exact ⟨hready0.1.2.2.2.1.1, le_trans hready0.1.2.2.2.1.2 heff_u.hp_lo⟩
  obtain ⟨hsl0, hsl8⟩ := evalAt_slice_word_bmi u ⟨wsa, hwsa⟩ ⟨wi, hwi⟩
    (by rw [hi_u, hn_u]; exact hidx) hin_u heff_u.arena (by rwa [hsa_u, hn_u])
  obtain ⟨wv, rfl, hwv⟩ := hsl0 v4 he4; obtain ⟨wvl, rfl, hwvl⟩ := hsl8 v5 he5
  let entry := callEntryStateHOLFinite u callee
  have heff_e := heff_u.locals_clock callee (u.clock - 1)
  have hinv_e := bmi4_mptInv_locals_clock hinv_u callee (u.clock - 1)
  have hm_loc : locN entry "m" = globN s0 "heap_ptr" := by
    simp [entry, callEntryStateHOLFinite, locN, hm_cal, hwm, hm_nat]
  have hklen_loc : locN entry "klen" ≤ 32 := by
    have : locN entry "klen" = wklen.toNat := by simp [entry, callEntryStateHOLFinite, locN, hk_cal, hklen]
    omega
  have hvptr : locN entry "vptr" = memW s0 (locN s0 "slice_arr" + 16 * wi.toNat) := by
    have : locN entry "vptr" = wv.toNat := by simp [entry, callEntryStateHOLFinite, locN, hc4]
    rw [this, hwv, hsa_u, hi_u]; exact (hsl_eq wi.toNat hidx).1
  have hvlen : locN entry "vlen" = memW s0 (locN s0 "slice_arr" + 16 * wi.toNat + 8) := by
    have : locN entry "vlen" = wvl.toNat := by simp [entry, callEntryStateHOLFinite, locN, hc5]
    rw [this, hwvl, hsa_u, hi_u]; exact (hsl_eq wi.toNat hidx).2
  have hready := bmi4_mptSetReadyStrong hready0 heff_e hinv_e hm_loc hklen_loc hidx hvptr hvlen
  have heff_set := FunSpec.at_lookup mk_mpt_set_eff_strong u heff_u.code vals
    (sourceFnBody Guest.Software.guestFn_mpt_set) callee .one hl hready hnt hres
  have heff_c := bmi4_we_of_mpt_set_eff heff_e hinv_e hm_loc heff_set rfl
  exact ⟨heff_c, bmi4_mptInv_after_set hready0 heff_e heff_c hinv_e hm_loc heff_set⟩

private theorem bmi4_rlp_callee {F : Type}
    {s0 t : PanSemStateFiniteExact 64 F} {S0 Nd0 : List Nat}
    (hready0 : BmiReadyG s0 S0 Nd0)
    (heff_t : R16Shards.WorldEff s0 t (bmi4Rl s0) [] (bmiWkGw : List String))
    (hinv_t : BmiLoopInv s0 S0 Nd0 t)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (vals : List (ValueHOL 64))
    (hargs : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) bmi4RlpArgs = some vals)
    (hl : lookupCodeHOLFinite t.code.lookup (ofString "rlp_encode_word") vals =
      some (sourceFnBody Guest.Software.guestFn_rlp_encode_word, callee, .one))
    (hnt : (evaluateHOLFiniteState (callEntryStateHOLFinite t callee)
      (sourceFnBody Guest.Software.guestFn_rlp_encode_word)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState (callEntryStateHOLFinite t callee)
      (sourceFnBody Guest.Software.guestFn_rlp_encode_word)).1) :
    let out := evaluateHOLFiniteState (callEntryStateHOLFinite t callee)
      (sourceFnBody Guest.Software.guestFn_rlp_encode_word)
    ∃ len : BitVec 64,
      out.1 = some (.returned (.val (.word len))) ∧ len.toNat ≤ 9 ∧
      R16Shards.WorldEff s0 out.2 (bmi4Rl s0) [] (bmiWkGw : List String) ∧
      BmiMptInv s0 S0 Nd0 out.2 := by
  dsimp only
  obtain ⟨v1, v2, he1, he2, hc1, hc2⟩ :=
    callee_param_two_exp t (ofString "rlp_encode_word")
      (ofString "dst") (ofString "w") .one .one _ _
      (by rw [heff_t.code]; exact lookup_rlp_encode_word_bmi)
      _ _ vals _ callee .one hargs hl
  obtain ⟨wi, hwi⟩ := hinv_t.wi_lk
  have hks_nz : globN t "mpt_key_scratch" ≠ 0 := by
    rw [bmi4_glob_eq heff_t "mpt_key_scratch" (by decide) (by decide)]
    exact hready0.2.2.2.2.2.2.1
  obtain ⟨wks, hwks⟩ := globalWord_of_globN_pos t "mpt_key_scratch" (by omega)
  unfold GlobalWord at hwks
  have hwks_nat : wks.toNat = globN t "mpt_key_scratch" := by simp [globN, hwks]
  have hd_cal : callee.lookup (ofString "dst") = some (.val (.word wks)) :=
    hc1.trans (by simpa only [evalAt, evalHOLExact, hwks] using he1.symm)
  have hw_cal : callee.lookup (ofString "w") = some (.val (.word wi)) :=
    hc2.trans (by simpa only [evalAt, evalHOLExact, hwi] using he2.symm)
  let entry := callEntryStateHOLFinite t callee
  have heff_e : R16Shards.WorldEff s0 entry (bmi4Rl s0) [] (bmiWkGw : List String) :=
    heff_t.locals_clock callee (t.clock - 1)
  have hdst : entry.locals.lookup (ofString "dst") = some (.val (.word wks)) := hd_cal
  have hw : entry.locals.lookup (ofString "w") = some (.val (.word wi)) := hw_cal
  have hin_ivl : ∃ ivl ∈ [bufferRegion t ("mpt_key_scratch", 16)],
      ivl.1 ≤ wks.toNat ∧ wks.toNat + 9 ≤ ivl.1 + ivl.2 := by
    refine ⟨bufferRegion t ("mpt_key_scratch", 16), List.mem_cons_self, ?_, ?_⟩
    · simp [bufferRegion, hks_nz, hwks_nat]
    · simp [bufferRegion, hks_nz, hwks_nat]
  have hrlp := eval_rlp_encode_word_body_exact entry wks wi
    [bufferRegion t ("mpt_key_scratch", 16)] heff_e.code heff_e.arena.1.memaddrs hdst hw hin_ivl hnt
  rcases hres with ⟨rv, hrv⟩ | ⟨eid, ev, hrv, hev⟩
  · obtain ⟨len, rfl, _, hlen9, _, hbre_e⟩ := hrlp.1 rv hrv
    have hbre_t : M11.ByteRegionEffect t
        (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_rlp_encode_word)).2
        [bufferRegion t ("mpt_key_scratch", 16)] := by
      have h0 := (M11.ByteRegionEffect.refl t [bufferRegion t ("mpt_key_scratch", 16)]).with_locals_clock
        callee (t.clock - 1)
      exact h0.trans hbre_e
    have hhbe := HeapByteEff.of_m11_bre (gw := bmiWkGw) heff_t.arena hbre_t
    have heff_post := bmiWk_we_trans_heapByteEff heff_t hhbe
      (by rw [(evaluateHOLFiniteState_metadata entry _).1]; exact heff_e.code)
      (by rw [(evaluateHOLFiniteState_metadata entry _).2.2.2.2]; rfl)
      (fun iv hiv hpos => by
        simp only [List.mem_singleton] at hiv; subst hiv
        exact Or.inl ⟨(globN s0 "mpt_key_scratch",
            if globN s0 "mpt_key_scratch" = 0 then 0 else 16),
          List.mem_append_left _ (by simp [bmiWkRti]),
          by unfold bufferRegion; rw [bmi4_glob_eq heff_t "mpt_key_scratch" (by decide) (by decide)],
          by unfold bufferRegion
             rw [bmi4_glob_eq heff_t "mpt_key_scratch" (by decide) (by decide)]⟩)
    exact ⟨len, hrv, hlen9, heff_post,
      bmi4_mptInv_after_rlp hready0 heff_t heff_post hinv_t.mptInv hbre_t⟩
  · exfalso
    exact hrlp.2 (.exception eid ev) hrv (fun _ h => by cases h) (Or.inr ⟨eid, ev, rfl, hev⟩)

private theorem bmi4_loop_body_step {F : Type}
    {s0 cur t : PanSemStateFiniteExact 64 F} {S0 Nd0 : List Nat}
    (hready0 : BmiReadyG s0 S0 Nd0)
    (hdec : t = decClockHOLFinite cur)
    (cw : BitVec 64)
    (hc : @evalHOLFinite 64 F _ cur (fun a => Classical.propDecidable (cur.memaddrs a)) bmi4LoopCond =
      some (.val (.word cw)))
    (hw0 : cw ≠ 0)
    (heff_t : R16Shards.WorldEff s0 t (bmi4Rl s0) [] (bmiWkGw : List String))
    (hinv_t : BmiLoopInv s0 S0 Nd0 t)
    (hnt : (evaluateHOLFiniteState t bmi4LoopBody).1 ≠ some .timeOut)
    (hcr : ContOrRes (evaluateHOLFiniteState t bmi4LoopBody).1) :
    R16Shards.WorldEff s0 (evaluateHOLFiniteState t bmi4LoopBody).2 (bmi4Rl s0) [] (bmiWkGw : List String) ∧
    (((evaluateHOLFiniteState t bmi4LoopBody).1 = none ∨
      (evaluateHOLFiniteState t bmi4LoopBody).1 = some .continue) →
      BmiLoopInv s0 S0 Nd0 (evaluateHOLFiniteState t bmi4LoopBody).2) := by
  obtain ⟨wi, hwi⟩ := hinv_t.wi_lk
  obtain ⟨wn, hwn, hwn_nat⟩ := hinv_t.wn_lk
  have hlt : wi.toNat < wn.toNat := by
    have hwi_c : cur.locals.lookup (ofString "i") = some (.val (.word wi)) := by
      rw [hdec] at hwi; exact hwi
    have hwn_c : cur.locals.lookup (ofString "n") = some (.val (.word wn)) := by
      rw [hdec] at hwn; exact hwn
    by_contra hge
    have hnlt : ¬ (wi < wn) := fun h => hge (BitVec.lt_def.mp h)
    simp [evalHOLFinite, evalHOLExact, hwi_c, hwn_c,
      Compiler.Encoders.Asm.wordCmpHOL, hnlt] at hc
    exact hw0 hc.symm
  have hidx : wi.toNat < locN s0 "n" := by rw [← hwn_nat]; exact hlt
  obtain ⟨wm, hwm, hm_nat⟩ := hinv_t.wm_lk
  obtain ⟨wsa, hwsa, hwsa_nat⟩ := hinv_t.wsa_lk
  refine ⟨?_, ?_⟩
  · exact R16Shards.worldEff_decCall_eff heff_t (ofString "klen") .one (ofString "rlp_encode_word")
      bmi4RlpArgs _ _ _ lookup_rlp_encode_word_bmi
      (fun callee vals hargs hl hnt_c hres_c =>
        let ⟨_, _, _, heff_c, _⟩ := bmi4_rlp_callee hready0 heff_t hinv_t callee vals hargs hl hnt_c hres_c
        heff_c)
      (fun callee vals rv cpost hargs hl hrun hsh heff_c hnt_k hcr_k => by
        obtain ⟨len, hlen, hlen9, heff_c', hinv_c⟩ :=
          bmi4_rlp_callee hready0 heff_t hinv_t callee vals hargs hl
            (by rw [hrun]; simp) (by rw [hrun]; exact Or.inl ⟨rv, rfl⟩)
        rw [hrun] at hlen heff_c' hinv_c
        have hrv : rv = .val (.word len) := by
          cases Option.some.inj hlen; rfl
        let u := setVarHOLFinite (ofString "klen") rv { cpost with locals := t.locals }
        have heff_u : R16Shards.WorldEff s0 u (bmi4Rl s0) [] (bmiWkGw : List String) :=
          heff_c'.locals_clock u.locals cpost.clock
        have hinv_u : BmiMptInv s0 S0 Nd0 u := bmi4_mptInv_locals_clock hinv_c u.locals cpost.clock
        have hwm_u : u.locals.lookup (ofString "m") = some (.val (.word wm)) := by
          simp [u, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "klen" ≠ ofString "m" by decide, hwm]
        have hk_u : u.locals.lookup (ofString "klen") = some (.val (.word len)) := by
          simp [u, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hrv]
        have hsa_u : u.locals.lookup (ofString "slice_arr") = some (.val (.word wsa)) := by
          simp [u, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "klen" ≠ ofString "slice_arr" by decide, hwsa]
        have hwi_u : u.locals.lookup (ofString "i") = some (.val (.word wi)) := by
          simp [u, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "klen" ≠ ofString "i" by decide, hwi]
        have hwn_u : u.locals.lookup (ofString "n") = some (.val (.word wn)) := by
          simp [u, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "klen" ≠ ofString "n" by decide, hwn]
        exact R16Shards.worldEff_seq hnt_k hcr_k
          (fun hnt_s hcr_s => R16Shards.worldEff_call0_eff heff_u (ofString "mpt_set") bmi4SetArgs
            _ _ _ P3MptSet.lookup_mpt_set (fun callee2 vals2 hargs2 hl2 hnt2 hres2 =>
              (bmi4_mpt_set_callee hready0 heff_u hinv_u wm len wsa wi wn hwm_u hm_nat hk_u (by omega)
                hsa_u hwsa_nat hwi_u hwn_u hwn_nat hidx callee2 vals2 hargs2 hl2 hnt2 hres2).1)
            hnt_s hcr_s)
          (fun mid hmid heff_m hnt_a hcr_a => R16Shards.worldEff_assign_local heff_m (ofString "i")
            (.op .add [.var .local (ofString "i"), .const 1])))
      hnt hcr
  · intro hflow
    have hnone := hflow.resolve_right (bmi4_no_brk_cont t .continue (Or.inr rfl))
    rcases hrun0 : evaluateHOLFiniteState t bmi4LoopBody with ⟨rb, post⟩
    rw [hrun0] at hnone; dsimp only at hnone ⊢; subst hnone
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hrun0
    rcases hargs : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) bmi4RlpArgs with _ | vals
    · rw [hargs] at hrun0; simp at hrun0
    · rw [hargs] at hrun0; dsimp only at hrun0
      rcases hl : lookupCodeHOLFinite t.code.lookup (ofString "rlp_encode_word") vals with _ | ⟨b1, c1, r1⟩
      · rw [hl] at hrun0; simp at hrun0
      · rw [hl] at hrun0; dsimp only at hrun0
        have hsame1 := lookupCodeHOLFinite_installed_body t.code.lookup (ofString "rlp_encode_word")
          _ _ b1 .one r1 vals c1 (by rw [heff_t.code]; exact lookup_rlp_encode_word_bmi) hl
        subst hsame1
        have hret1 := lookupCodeHOLFinite_installed_return t (ofString "rlp_encode_word")
          _ _ _ .one r1 vals c1 (by rw [heff_t.code]; exact lookup_rlp_encode_word_bmi) hl
        subst hret1
        split at hrun0
        · simp at hrun0
        · rcases hb1 : evaluateHOLFiniteState (callEntryStateHOLFinite t c1)
              (sourceFnBody Guest.Software.guestFn_rlp_encode_word) with ⟨br1, bp1⟩
          rw [hb1] at hrun0
          cases br1 with
          | none => simp at hrun0
          | some br1' =>
            cases br1' with
            | returned v1 =>
              dsimp only at hrun0; split at hrun0
              · obtain ⟨len, hlen, hlen9, heff_bp1, hinv_bp1⟩ :=
                  bmi4_rlp_callee hready0 heff_t hinv_t c1 vals hargs hl
                    (by rw [hb1]; simp) (by rw [hb1]; exact Or.inl ⟨v1, rfl⟩)
                rw [hb1] at hlen heff_bp1 hinv_bp1
                have hv1 : v1 = .val (.word len) := by cases Option.some.inj hlen; rfl
                set u := setVarHOLFinite (ofString "klen") v1 { bp1 with locals := t.locals }
                have heff_u : R16Shards.WorldEff s0 u (bmi4Rl s0) [] (bmiWkGw : List String) :=
                  heff_bp1.locals_clock u.locals bp1.clock
                have hinv_u : BmiMptInv s0 S0 Nd0 u := bmi4_mptInv_locals_clock hinv_bp1 u.locals bp1.clock
                have hwm_u : u.locals.lookup (ofString "m") = some (.val (.word wm)) := by
                  simp [u, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                    show ofString "klen" ≠ ofString "m" by decide, hwm]
                have hk_u : u.locals.lookup (ofString "klen") = some (.val (.word len)) := by
                  simp [u, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hv1]
                have hsa_u : u.locals.lookup (ofString "slice_arr") = some (.val (.word wsa)) := by
                  simp [u, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                    show ofString "klen" ≠ ofString "slice_arr" by decide, hwsa]
                have hwi_u : u.locals.lookup (ofString "i") = some (.val (.word wi)) := by
                  simp [u, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                    show ofString "klen" ≠ ofString "i" by decide, hwi]
                have hwn_u : u.locals.lookup (ofString "n") = some (.val (.word wn)) := by
                  simp [u, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                    show ofString "klen" ≠ ofString "n" by decide, hwn]
                rcases hseq : evaluateHOLFiniteState u
                    (.seq (.call (some (none, none)) (ofString "mpt_set") bmi4SetArgs)
                      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1]))) with ⟨sr, sp⟩
                rw [hseq] at hrun0; dsimp only at hrun0
                obtain ⟨hsr, hpost_eq⟩ := Prod.mk.inj hrun0; subst hsr
                rw [evaluateHOLFiniteState_seq_line780] at hseq
                rcases hc2 : evaluateHOLFiniteState u
                    (.call (some (none, none)) (ofString "mpt_set") bmi4SetArgs) with ⟨r2, m2⟩
                rw [hc2] at hseq
                cases r2 with
                | some _ => simp at hseq
                | none =>
                  dsimp only at hseq
                  have hm2_loc : m2.locals = u.locals := call0_none_locals u _ _ m2 hc2
                  have hm2_inv : BmiMptInv s0 S0 Nd0 m2 := by
                    rw [evaluateHOLFiniteState_call] at hc2
                    rcases ha2 : evalListHOLFinite u (h := fun a => Classical.propDecidable (u.memaddrs a))
                        bmi4SetArgs with _ | vs2
                    · rw [ha2] at hc2; simp at hc2
                    · rw [ha2] at hc2; dsimp only at hc2
                      rcases hl2 : lookupCodeHOLFinite u.code.lookup (ofString "mpt_set") vs2 with _ | ⟨b2, c2, ret2⟩
                      · rw [hl2] at hc2; simp at hc2
                      · rw [hl2] at hc2; dsimp only at hc2
                        have hsame2 := lookupCodeHOLFinite_installed_body u.code.lookup (ofString "mpt_set")
                          _ _ b2 .one ret2 vs2 c2 (by rw [heff_u.code]; exact P3MptSet.lookup_mpt_set) hl2
                        have hret2 := lookupCodeHOLFinite_installed_return u (ofString "mpt_set")
                          _ _ _ .one ret2 vs2 c2 (by rw [heff_u.code]; exact P3MptSet.lookup_mpt_set) hl2
                        subst hret2; split at hc2
                        · simp at hc2
                        · rcases hb2 : evaluateHOLFiniteState (callEntryStateHOLFinite u c2)
                              (sourceFnBody Guest.Software.guestFn_mpt_set) with ⟨br2, bp2⟩
                          have hb2' : evaluateHOLFiniteState (callEntryStateHOLFinite u c2) b2 = (br2, bp2) := by
                            rw [hsame2]; exact hb2
                          rw [hb2'] at hc2; rw [hsame2] at hl2
                          cases br2 with
                          | none => simp at hc2
                          | some br2' =>
                            cases br2' with
                            | returned v2 =>
                              dsimp only at hc2; split at hc2
                              · obtain ⟨_, hm2_eq⟩ := Prod.mk.inj hc2
                                have hset_step := (bmi4_mpt_set_callee hready0 heff_u hinv_u
                                  wm len wsa wi wn hwm_u hm_nat hk_u (by omega) hsa_u hwsa_nat
                                  hwi_u hwn_u hwn_nat hidx c2 vs2 ha2 hl2
                                  (by rw [hb2]; simp) (by rw [hb2]; exact Or.inl ⟨v2, rfl⟩)).2
                                rw [hb2] at hset_step; rw [← hm2_eq]
                                exact bmi4_mptInv_locals_clock hset_step u.locals bp2.clock
                              · simp at hc2
                            | _ => simp [emptyLocalsHOLFinite] at hc2
                  have hwi_m2 : m2.locals.lookup (ofString "i") = some (.val (.word wi)) := by
                    rw [hm2_loc]; exact hwi_u
                  have hasgn : evaluateHOLFiniteState m2
                      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])) =
                      (none, setVarHOLFinite (ofString "i") (.val (.word (wi + 1))) m2) := by
                    rw [evaluateHOLFiniteState_assign]
                    simp [evalHOLExact, evalListHOLExact, hwi_m2, wordOpHOL, wordOp,
                      valueIsWord, valueWord, isValidValueHOLExact, lookupKvarHOLExact,
                      shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite]
                  rw [hasgn] at hseq
                  obtain ⟨_, hsp_eq⟩ := Prod.mk.inj hseq; subst hsp_eq; rw [← hpost_eq]
                  refine ⟨bmi4_mptInv_locals_clock hm2_inv
                    ((setVarHOLFinite (ofString "i") (.val (.word (wi + 1))) m2).locals.resVarEq
                      (ofString "klen", t.locals.lookup (ofString "klen"))) m2.clock,
                    ?_, ?_, ?_, ?_, ?_, ?_⟩
                  · obtain ⟨w, hw, hn⟩ := hinv_t.wmark_lk; refine ⟨w, ?_, hn⟩
                    rw [resVarEq_lookup_ne _ (ofString "klen") (ofString "mark") _ (by decide)]
                    simp [setVarHOLFinite, hm2_loc, u, HolFiniteMapExact.lookup_update, FUPDATE,
                      show ofString "i" ≠ ofString "mark" by decide,
                      show ofString "klen" ≠ ofString "mark" by decide, hw]
                  · refine ⟨wm, ?_, hm_nat⟩
                    rw [resVarEq_lookup_ne _ (ofString "klen") (ofString "m") _ (by decide)]
                    simp [setVarHOLFinite, hm2_loc, HolFiniteMapExact.lookup_update, FUPDATE,
                      show ofString "i" ≠ ofString "m" by decide, hwm_u]
                  · refine ⟨wsa, ?_, hwsa_nat⟩
                    rw [resVarEq_lookup_ne _ (ofString "klen") (ofString "slice_arr") _ (by decide)]
                    simp [setVarHOLFinite, hm2_loc, HolFiniteMapExact.lookup_update, FUPDATE,
                      show ofString "i" ≠ ofString "slice_arr" by decide, hsa_u]
                  · refine ⟨wn, ?_, hwn_nat⟩
                    rw [resVarEq_lookup_ne _ (ofString "klen") (ofString "n") _ (by decide)]
                    simp [setVarHOLFinite, hm2_loc, HolFiniteMapExact.lookup_update, FUPDATE,
                      show ofString "i" ≠ ofString "n" by decide, hwn_u]
                  · obtain ⟨w, hw, hn⟩ := hinv_t.wout_lk; refine ⟨w, ?_, hn⟩
                    rw [resVarEq_lookup_ne _ (ofString "klen") (ofString "out") _ (by decide)]
                    simp [setVarHOLFinite, hm2_loc, u, HolFiniteMapExact.lookup_update, FUPDATE,
                      show ofString "i" ≠ ofString "out" by decide,
                      show ofString "klen" ≠ ofString "out" by decide, hw]
                  · refine ⟨wi + 1, ?_⟩
                    rw [resVarEq_lookup_ne _ (ofString "klen") (ofString "i") _ (by decide)]
                    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
              · simp at hrun0
            | _ => simp [emptyLocalsHOLFinite] at hrun0

private theorem bmi4_mpt_new_callee {F : Type} {s0 s1 : PanSemStateFiniteExact 64 F} {S0 Nd0 : List Nat}
    (hready0 : BmiReadyG s0 S0 Nd0)
    (heff_s1 : R16Shards.WorldEff s0 s1 (bmi4Rl s0) [] (bmiWkGw : List String))
    (hp_eq : globN s1 "heap_ptr" = globN s0 "heap_ptr")
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (vals : List (ValueHOL 64))
    (hargs : evalListHOLFinite s1 (h := fun a => Classical.propDecidable (s1.memaddrs a))
      [.const 0, .const 0] = some vals)
    (hl : lookupCodeHOLFinite s1.code.lookup (ofString "mpt_new") vals =
      some (sourceFnBody Guest.Software.guestFn_mpt_new, callee, .one))
    (hnt : (evaluateHOLFiniteState (callEntryStateHOLFinite s1 callee)
      (sourceFnBody Guest.Software.guestFn_mpt_new)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState (callEntryStateHOLFinite s1 callee)
      (sourceFnBody Guest.Software.guestFn_mpt_new)).1) :
    let out := evaluateHOLFiniteState (callEntryStateHOLFinite s1 callee)
      (sourceFnBody Guest.Software.guestFn_mpt_new)
    ∃ hp : BitVec 64, out.1 = some (.returned (.val (.word hp))) ∧ hp.toNat = globN s0 "heap_ptr" ∧
      R16Shards.WorldEff s0 out.2 (bmi4Rl s0) [] (bmiWkGw : List String) ∧ BmiMptInv s0 S0 Nd0 out.2 := by
  dsimp only
  obtain ⟨v1, v2, he1, he2, hc1, hc2⟩ :=
    callee_param_two_exp s1 (ofString "mpt_new") (ofString "root_node") (ofString "secured") .one .one _ _
      (by rw [heff_s1.code]; exact lookup_mpt_new_bmi) _ _ vals _ callee .one hargs hl
  have hrn_c : callee.lookup (ofString "root_node") = some (.val (.word 0)) :=
    hc1.trans (by simpa only [evalAt, evalHOLExact] using he1.symm)
  have hsec_c : callee.lookup (ofString "secured") = some (.val (.word 0)) :=
    hc2.trans (by simpa only [evalAt, evalHOLExact] using he2.symm)
  let entry := callEntryStateHOLFinite s1 callee
  have heff_e : R16Shards.WorldEff s0 entry (bmi4Rl s0) [] (bmiWkGw : List String) :=
    heff_s1.locals_clock callee (s1.clock - 1)
  obtain ⟨hp, q, hret, hhp_nat, hhp_al, hq_eq, hq_hi, hq_al, hg, hm, hbe, hAR, hAg, hFB, hmem0, _⟩ :=
    R13Shards.mpt_new_resumes_props entry 0 0 heff_e.code heff_e.arena hrn_c hsec_c hres
  have hhp_s0 : hp.toNat = globN s0 "heap_ptr" := by
    change hp.toNat = globN s1 "heap_ptr" at hhp_nat; exact hhp_nat.trans hp_eq
  have hsb_le : sourceBase ≤ hp.toNat := by rw [hhp_s0]; exact hready0.1.1.1.2.1
  have hlim_he : heapLimit ≤ heapEnd := by decide
  have hhlP8 : heapLimit + 8 < 2 ^ 64 := by decide
  have h8b : (8 : BitVec 64).toNat = 8 := by decide
  have h0b : (0 : BitVec 64).toNat = 0 := by decide
  have hp8_nat : (hp + 8).toNat = hp.toNat + 8 := by
    rw [BitVec.toNat_add, h8b]; exact Nat.mod_eq_of_lt (by omega)
  have hp0_nat : (hp + 0).toNat = hp.toNat := by
    rw [BitVec.toNat_add, h0b]; exact Nat.mod_eq_of_lt (by omega)
  have hmeta := evaluateHOLFiniteState_metadata entry (sourceFnBody Guest.Software.guestFn_mpt_new)
  let sa := (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_mpt_new)).2
  have hsa_hp : globN sa "heap_ptr" = q.toNat := by
    unfold globN; rw [hg]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hsa_sp : globN sa "scratch_ptr" = globN entry "scratch_ptr" := by
    unfold globN; rw [hg]
    simp [HolFiniteMapExact.lookup_update, FUPDATE, show ofString "heap_ptr" ≠ ofString "scratch_ptr" by decide]
  have heff_sa := bmiWk_we_callee_mpt (Rm := fun _ => []) (Wown := []) heff_e (by simp) (by simp) hAR
    (by rw [hsa_hp, ← hhp_nat]; omega) (by rw [hsa_sp])
    (fun a hne => by
      rw [hm] at hne; simp only [Wave8Contracts.M26.updW] at hne
      by_cases h1 : a = hp + 8
      · subst h1; exact Or.inr (Or.inr (Or.inr ⟨by rw [← hhp_nat]; omega,
          by rw [hp8_nat, ← hhp_nat]; omega, by rw [hp8_nat]; omega⟩))
      · by_cases h2 : a = hp + 0
        · subst h2; exact Or.inr (Or.inr (Or.inr ⟨by rw [← hhp_nat]; omega,
            by rw [hp0_nat, ← hhp_nat]; omega, by rw [hp0_nat]; omega⟩))
        · rw [if_neg h1, if_neg h2] at hne; exact absurd rfl hne)
    (fun b hb64 hne => by
      unfold memB at hne; rw [hm] at hne; simp only [Wave8Contracts.M26.updW] at hne
      by_cases h1 : panByteAlignHOL (BitVec.ofNat 64 b) = hp + 8
      · have h2 := congrArg BitVec.toNat h1
        simp only [panByteAlignHOL, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceDiv,
          RiscV.panRiscV_log2_eight, BitVec.ofNat_eq_ofNat, BitVec.toNat_add, Nat.reduceMod] at h2
        have : b / 8 * 8 ≤ b ∧ b < b / 8 * 8 + 8 := by omega
        have : b / 8 * 8 = hp.toNat + 8 := by omega
        exact Or.inr (Or.inr (Or.inr ⟨by rw [← hhp_nat]; omega, by rw [← hhp_nat]; omega, by omega⟩))
      · by_cases h2 : panByteAlignHOL (BitVec.ofNat 64 b) = hp + 0
        · have h3 := congrArg BitVec.toNat h2
          simp only [panByteAlignHOL, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceDiv,
            RiscV.panRiscV_log2_eight, BitVec.ofNat_eq_ofNat, BitVec.toNat_add, Nat.reduceMod] at h3
          have : b / 8 * 8 ≤ b ∧ b < b / 8 * 8 + 8 := by omega
          have : b / 8 * 8 = hp.toNat := by omega
          exact Or.inr (Or.inr (Or.inr ⟨by rw [← hhp_nat]; omega, by rw [← hhp_nat]; omega, by omega⟩))
        · rw [if_neg h1, if_neg h2, hbe] at hne; exact absurd rfl hne)
    (fun k hk => by
      have hne : k ≠ ofString "heap_ptr" := fun heq => hk (by simp [heq])
      rw [hg]; simp [HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hne])
    (hmeta.1.trans heff_e.code) ⟨hmeta.2.1, hmeta.2.2.1, hmeta.2.2.2.2⟩
    (fun a hne => by
      rw [hm] at hne; simp only [Wave8Contracts.M26.updW] at hne
      by_cases h1 : a = hp + 8
      · subst h1; rw [heff_e.arena.1.memaddrs, Fast_C08WkShard03.ordinaryDomain_iff]
        exact ⟨by rw [hp8_nat]; omega, by rw [hp8_nat]; omega, by rw [hp8_nat]; omega⟩
      · by_cases h2 : a = hp + 0
        · subst h2; rw [heff_e.arena.1.memaddrs, Fast_C08WkShard03.ordinaryDomain_iff]
          exact ⟨by rw [hp0_nat]; omega, by rw [hp0_nat]; omega, by rw [hp0_nat]; omega⟩
        · rw [if_neg h1, if_neg h2] at hne; exact absurd rfl hne)
  exact ⟨hp, hret, hhp_s0, heff_sa, bmi4_mptInv_after_new hready0 heff_sa
    (by rw [hsa_hp, hq_eq, hhp_s0]) (by rw [← hhp_s0]; exact hFB)
    (by rw [← hhp_s0, hmem0]; simp [entry, callEntryStateHOLFinite, locN, hrn_c])⟩

private theorem bmi4_mpt_root_callee {F : Type} {s0 sw : PanSemStateFiniteExact 64 F} {S0 Nd0 : List Nat}
    (hready0 : BmiReadyG s0 S0 Nd0)
    (heff_sw : R16Shards.WorldEff s0 sw (bmi4Rl s0) [] (bmiWkGw : List String))
    (hinv_sw : BmiLoopInv s0 S0 Nd0 sw)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (vals : List (ValueHOL 64))
    (hargs : evalListHOLFinite sw (h := fun a => Classical.propDecidable (sw.memaddrs a))
      [.var .local (ofString "m"), .var .local (ofString "out")] = some vals)
    (hl : lookupCodeHOLFinite sw.code.lookup (ofString "mpt_root") vals =
      some (sourceFnBody Guest.Software.guestFn_mpt_root, callee, .one))
    (hnt : (evaluateHOLFiniteState (callEntryStateHOLFinite sw callee)
      (sourceFnBody Guest.Software.guestFn_mpt_root)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState (callEntryStateHOLFinite sw callee)
      (sourceFnBody Guest.Software.guestFn_mpt_root)).1) :
    R16Shards.WorldEff s0
      (evaluateHOLFiniteState (callEntryStateHOLFinite sw callee) (sourceFnBody Guest.Software.guestFn_mpt_root)).2
      (bmi4Rl s0) [] (bmiWkGw : List String) := by
  obtain ⟨v1, v2, he1, he2, hc1, hc2⟩ :=
    callee_param_two_exp sw (ofString "mpt_root") (ofString "m") (ofString "out") .one .one _ _
      (by rw [heff_sw.code]; exact lookup_mpt_root_bmi4) _ _ vals _ callee .one hargs hl
  obtain ⟨wm, hwm, hm_nat⟩ := hinv_sw.wm_lk; obtain ⟨wout, hwout, hout_nat⟩ := hinv_sw.wout_lk
  have hm_c : callee.lookup (ofString "m") = some (.val (.word wm)) :=
    hc1.trans (by simpa only [evalAt, evalHOLExact, hwm] using he1.symm)
  have ho_c : callee.lookup (ofString "out") = some (.val (.word wout)) :=
    hc2.trans (by simpa only [evalAt, evalHOLExact, hwout] using he2.symm)
  let entry := callEntryStateHOLFinite sw callee
  have heff_e : R16Shards.WorldEff s0 entry (bmi4Rl s0) [] (bmiWkGw : List String) :=
    heff_sw.locals_clock callee (sw.clock - 1)
  have hinv_e : BmiMptInv s0 S0 Nd0 entry := bmi4_mptInv_locals_clock hinv_sw.mptInv callee (sw.clock - 1)
  have hm_loc : locN entry "m" = globN s0 "heap_ptr" := by simp [entry, callEntryStateHOLFinite, locN, hm_c, hm_nat]
  have hout_loc : locN entry "out" = locN s0 "out" := by simp [entry, callEntryStateHOLFinite, locN, ho_c, hout_nat]
  have heff_rt := wkMptRootFineBody entry wm wout heff_e.code
    (bmi4_mptObjReadyStrong heff_e hinv_e hm_loc) hm_c ho_c hres
  obtain ⟨hm16, Nm, _, ⟨⟨hm_al, hm_w, _, hm_fix, hm_nh, hm_root, hm_ext⟩, hm_vs⟩, _, hspan⟩ := hinv_e
  rw [← hm_loc] at hm_al hm_w hm_root hm_ext
  have hB_fix : ∀ gs ∈ bmiRootB, bufferRegion entry gs ∈ fixedObjects entry := fun gs hgs => by
    refine bmi4_buf_in_fixedObjects entry gs ?_
    simp only [bmiRootB, List.mem_cons, List.not_mem_nil, or_false] at hgs
    rcases hgs with rfl | rfl <;> decide
  obtain ⟨hcell5, hbyte5⟩ := heff_rt.write_frame Nm hm_al hm_w hm_nh hm_vs hm_root
    (fun o ho => ⟨(hm_ext o ho).1, fun gs hgs => (hm_ext o ho).2.2 _ (hB_fix gs hgs)⟩)
    (fun gs hgs => by rw [hm_loc]; exact hm_fix _ (hB_fix gs hgs))
  have hspan_obj : ∀ o ∈ mptObjIvls entry Nm (locN entry "m"), 0 < o.2 →
      locN entry "m" ≤ o.1 ∧ o.1 + o.2 ≤ globN entry "heap_ptr" := fun o ho hpos => by
    rcases List.mem_cons.1 ho with rfl | ho'
    · exact ⟨le_rfl, by dsimp only; omega⟩
    · rw [hm_loc]; exact hspan o ho' hpos
  let rootRm : PanSemStateFiniteExact 64 F → List Ivl :=
    fun e => (locN e "m", globN e "heap_ptr" - locN e "m") :: bmiRootR e
  have hRm_in : ∀ i ∈ rootRm entry, 0 < i.2 →
      ∃ j ∈ bmi4Rl s0, 0 < j.2 ∧ j.1 ≤ i.1 ∧ i.1 + i.2 ≤ j.1 + j.2 := fun i hi hpos => by
    have hkp := bmi4_glob_eq heff_e "keccak_pad" (by decide) (by decide)
    have hks := bmi4_glob_eq heff_e "keccak_st" (by decide) (by decide)
    simp only [rootRm, bmiRootR, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · refine ⟨(globN s0 "heap_ptr", heapLimit - globN s0 "heap_ptr"),
        List.mem_append_right _ List.mem_cons_self, ?_, by dsimp only; omega, ?_⟩ <;>
        (have := heff_e.arena.2.2.1; dsimp only at hpos ⊢; omega)
    · exact ⟨(locN s0 "out", 32), List.mem_append_left _ (by simp [bmiWkRti]),
        by dsimp only; omega, by dsimp only; omega, by dsimp only; omega⟩
    · exact ⟨(globN s0 "keccak_pad", if globN s0 "keccak_pad" = 0 then 0 else 136),
        List.mem_append_left _ (by simp [bmiWkRti]),
        by rw [← hkp]; dsimp only at hpos ⊢; omega, by rw [← hkp], by rw [← hkp]⟩
    · exact ⟨(globN s0 "keccak_st", if globN s0 "keccak_st" = 0 then 0 else 200),
        List.mem_append_left _ (by simp [bmiWkRti]),
        by rw [← hks]; dsimp only at hpos ⊢; omega, by rw [← hks], by rw [← hks]⟩
  have hmemB : ∀ gs ∈ bmiRootB, bufferRegion entry gs ∈ rootRm entry := fun gs hgs => by
    simp only [bmiRootB, List.mem_cons, List.not_mem_nil, or_false] at hgs
    rcases hgs with rfl | rfl <;> simp [rootRm, bmiRootR, bufferRegion]
  have hmeta := evaluateHOLFiniteState_metadata entry (sourceFnBody Guest.Software.guestFn_mpt_root)
  refine bmiWk_we_callee_mpt (Rm := rootRm) (Wown := []) heff_e hRm_in (by simp)
    heff_rt.arena heff_rt.grows.1 heff_rt.grows.2 ?_ ?_
    (fun k hk => heff_rt.gw_kept k (by simpa [bmiWkGw] using hk))
    (hmeta.1.trans heff_e.code) ⟨hmeta.2.1, hmeta.2.2.1, hmeta.2.2.2.2⟩ heff_rt.dom_wr
  · intro a hne
    rcases hcell5 a hne with ⟨ivl, hivl, hc⟩ | ⟨gs, hgs, hc⟩ | ⟨o, ho, hc⟩ | hfg | hhf
    · exact Or.inl ⟨ivl, List.mem_cons_of_mem _ hivl, hc.1, hc.2.1, hc.2.2⟩
    · exact Or.inl ⟨bufferRegion entry gs, hmemB gs hgs, hc.1, hc.2.1, hc.2.2⟩
    · obtain ⟨hlo, hhi⟩ := hspan_obj o ho hc.1
      exact Or.inl ⟨(locN entry "m", globN entry "heap_ptr" - locN entry "m"),
        List.mem_cons_self, by dsimp only; omega, by dsimp only; have := hc.2.1; omega,
        by dsimp only; have := hc.2.2; omega⟩
    · obtain ⟨h0, h1, h2⟩ := hfg; dsimp [freeGap] at h0 h1 h2; exact Or.inr (Or.inr (Or.inl ⟨h0, h1, by omega⟩))
    · obtain ⟨h0, h1, h2⟩ := hhf; dsimp [heapFree] at h0 h1 h2; exact Or.inr (Or.inr (Or.inr ⟨h0, h1, by omega⟩))
  · intro b hb64 hne
    rcases hbyte5 b hb64 hne with ⟨ivl, hivl, hi⟩ | ⟨gs, hgs, hi⟩ | ⟨o, ho, hi⟩ | hfg | hhf
    · exact Or.inl ⟨ivl, List.mem_cons_of_mem _ hivl, by dsimp [InIvl] at hi; omega, hi.1, hi.2⟩
    · exact Or.inl ⟨bufferRegion entry gs, hmemB gs hgs, by dsimp [InIvl] at hi; omega, hi.1, hi.2⟩
    · obtain ⟨hlo, hhi⟩ := hspan_obj o ho (by dsimp [InIvl] at hi; omega)
      exact Or.inl ⟨(locN entry "m", globN entry "heap_ptr" - locN entry "m"),
        List.mem_cons_self, by dsimp only; omega, by dsimp [InIvl] at hi ⊢; omega,
        by dsimp [InIvl] at hi ⊢; omega⟩
    · exact Or.inr (Or.inr (Or.inl ⟨by dsimp [InIvl, freeGap] at hfg; omega, hfg.1,
        by dsimp [InIvl, freeGap] at hfg; omega⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨by dsimp [InIvl, heapFree] at hhf; omega, hhf.1,
        by dsimp [InIvl, heapFree] at hhf; omega⟩))



/-! ## The bound with `mpt_root` called at `MptObjReadyStrong` -/

/-- The world-effect invariant of `BuildMptIndexedWalk4` before the counter
`i` is declared: effect from an entry state `s0`, the strong object
invariant of the fresh trie, and the word locals. -/
private def BmiW4pre : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun {F} s => ∃ (s0 : PanSemStateFiniteExact 64 F) (S0 Nd0 : List Nat), BmiReadyG s0 S0 Nd0 ∧
    R16Shards.WorldEff s0 s (bmi4Rl s0) [] (bmiWkGw : List String) ∧ BmiMptInv s0 S0 Nd0 s ∧
    (∃ w : BitVec 64, s.locals.lookup (ofString "mark") = some (.val (.word w)) ∧
      w.toNat = globN s0 "heap_ptr") ∧
    (∃ w : BitVec 64, s.locals.lookup (ofString "m") = some (.val (.word w)) ∧
      w.toNat = globN s0 "heap_ptr") ∧
    (∃ w : BitVec 64, s.locals.lookup (ofString "slice_arr") = some (.val (.word w)) ∧
      w.toNat = locN s0 "slice_arr") ∧
    (∃ w : BitVec 64, s.locals.lookup (ofString "n") = some (.val (.word w)) ∧
      w.toNat = locN s0 "n") ∧
    (∃ w : BitVec 64, s.locals.lookup (ofString "out") = some (.val (.word w)) ∧
      w.toNat = locN s0 "out")

/-- The loop invariant of `BuildMptIndexedWalk4`, with its entry state hidden. -/
private def BmiW4 : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun {F} s => ∃ (s0 : PanSemStateFiniteExact 64 F) (S0 Nd0 : List Nat), BmiReadyG s0 S0 Nd0 ∧
    R16Shards.WorldEff s0 s (bmi4Rl s0) [] (bmiWkGw : List String) ∧ BmiLoopInv s0 S0 Nd0 s

private theorem decCallResume_mpt_new_bmi_w4
    (hwk : WorldKeeps WorldOK (fun _ => [])
      ["heap_ptr"] R10Shards.P26_P28.stdKeep
      (RetAvoids (fun _ _ w => [(w, 16)])) (ofString "mpt_new"))
    (hrt : Returns ArenaReady (fun s post m => FreshBlock s post m 16 ∧
      memW post m = locN s "root_node" ∧ memW post (m + 8) = locN s "secured")
      (ofString "mpt_new")) :
    DecCallResumeOn (fun s => BuildMptAfterMark s ∧ BmiAfterMarkC s)
      (fun s => BmiAfterNewStrong s ∧ BmiW4pre s)
      (ofString "m") (ofString "mpt_new") [.const 0, .const 0] := by
  intro F state values body callee ret value post hcode hP hargs hl hrun
  refine ⟨decCallResume_mpt_new_bmi_strong hwk hrt state values body callee ret value post
    hcode hP hargs hl hrun, ?_⟩
  obtain ⟨S0, Nd0, hready0, ⟨wmark, hwmark⟩, hmark_eq⟩ := hP.2
  have hmark_nat : wmark.toNat = globN state "heap_ptr" := by
    simpa [locN, hwmark] using hmark_eq
  obtain ⟨wa, hwa⟩ := hready0.1.2.1 "slice_arr" (by simp)
  obtain ⟨wn, hwn⟩ := hready0.1.2.1 "n" (by simp)
  obtain ⟨wo, hwo⟩ := hready0.1.2.1 "out" (by simp)
  have hbody : body = sourceFnBody Guest.Software.guestFn_mpt_new :=
    lookupCodeHOLFinite_installed_body state.code.lookup (ofString "mpt_new") _ _ body _ ret
      values callee (by rw [hcode]; exact lookup_mpt_new_bmi) hl
  have hret : ret = .one :=
    lookupCodeHOLFinite_installed_return state (ofString "mpt_new") _ _ body _ ret
      values callee (by rw [hcode]; exact lookup_mpt_new_bmi) hl
  subst hbody; subst hret
  have heff0 : R16Shards.WorldEff state state (bmi4Rl state) [] (bmiWkGw : List String) :=
    R16Shards.WorldEff.refl state (bmi4Rl state) [] (bmiWkGw : List String) hready0.1.1.1 hcode
  obtain ⟨wm, hretv, hm_nat, heff_c, hinv_c⟩ :=
    bmi4_mpt_new_callee hready0 heff0 rfl callee values hargs hl
      (by rw [hrun]; simp) (by rw [hrun]; exact Or.inl ⟨value, rfl⟩)
  rw [hrun] at hretv heff_c hinv_c
  have hrv : value = .val (.word wm) := by cases Option.some.inj hretv; rfl
  let s2 := setVarHOLFinite (ofString "m") value { post with locals := state.locals }
  refine ⟨state, S0, Nd0, hready0, heff_c.locals_clock s2.locals post.clock,
    bmi4_mptInv_locals_clock hinv_c s2.locals post.clock,
    ⟨wmark, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "m" ≠ ofString "mark" by decide, hwmark], hmark_nat⟩,
    ⟨wm, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hrv], hm_nat⟩,
    ⟨wa, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "m" ≠ ofString "slice_arr" by decide, hwa], by simp [locN, hwa]⟩,
    ⟨wn, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "m" ≠ ofString "n" by decide, hwn], by simp [locN, hwn]⟩,
    ⟨wo, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "m" ≠ ofString "out" by decide, hwo], by simp [locN, hwo]⟩⟩

private theorem bmiW4pre_set_counter {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : BmiW4pre s) (w : BitVec 64) :
    BmiW4 (setVarHOLFinite (ofString "i") (.val (.word w)) s) := by
  obtain ⟨s0, S0, Nd0, hready0, heff, hinv, ⟨wmark, hwmark, hmark_nat⟩, ⟨wm, hwm, hm_nat⟩,
    ⟨wa, hwa, hwa_nat⟩, ⟨wn, hwn, hwn_nat⟩, ⟨wo, hwo, hwo_nat⟩⟩ := h
  let s3 := setVarHOLFinite (ofString "i") (.val (.word w)) s
  exact ⟨s0, S0, Nd0, hready0, heff.locals_clock s3.locals s.clock,
    ⟨bmi4_mptInv_locals_clock hinv s3.locals s.clock,
     ⟨wmark, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
       show ofString "i" ≠ ofString "mark" by decide, hwmark], hmark_nat⟩,
     ⟨wm, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
       show ofString "i" ≠ ofString "m" by decide, hwm], hm_nat⟩,
     ⟨wa, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
       show ofString "i" ≠ ofString "slice_arr" by decide, hwa], hwa_nat⟩,
     ⟨wn, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
       show ofString "i" ≠ ofString "n" by decide, hwn], hwn_nat⟩,
     ⟨wo, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
       show ofString "i" ≠ ofString "out" by decide, hwo], hwo_nat⟩,
     ⟨w, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩⟩⟩

/-- At loop exit both invariants hold: the weak one of `BuildMptIndexedWalk3`
and the strong world-effect one of `BuildMptIndexedWalk4`. -/
private theorem bmi_while_hoare_w4
    (hmk_set : MptKeeps MptSetReady bmiSetRC11 ["heap_ptr", "scratch_ptr"]
      R10Shards.P26_P28.stdKeep (ofString "mpt_set"))
    (hwk_rlp : WorldKeeps WorldOK (fun s => [(locN s "dst", 9)])
      [] R10Shards.P26_P28.stdKeep NoExtra (ofString "rlp_encode_word")) :
    Hoare (fun s => BuildMptLoopInv2 s ∧ BmiW4 s) (.while bmiLoopCond bmiLoopBody)
      (fun r t => r = none → BuildMptLoopInv t ∧ BmiW4 t) := by
  refine ⟨fun {F} s hcode hP hnt hr =>
    ⟨(bmi3_while_hoare hmk_set hwk_rlp).run s hcode hP.1 hnt hr, ?_⟩⟩
  obtain ⟨s0, S0, Nd0, hready0, heff, hinv⟩ := hP.2
  have hw := bmi4_while_ind bmi4LoopCond (BmiLoopInv s0 S0 Nd0)
    (fun _ h => bmiLoopInv_decClock h)
    (fun _ cw hc hw0 heff_d hinv_d hnt_b hcr_b =>
      bmi4_loop_body_step hready0 rfl cw hc hw0 heff_d hinv_d hnt_b hcr_b)
    s.clock s rfl heff hinv hnt (Or.inl hr)
  exact ⟨s0, S0, Nd0, hready0, hw.1,
    hw.2 hr (fun t _ => bmi4_no_brk_cont t .break (Or.inl rfl))⟩

/-- `MptC10C12.NodeValuesSafe` (stated with `keccakBufIvls`) gives
`NrfStrong.NodeValuesSafe` (stated with the two buffer regions). -/
private theorem nodeValuesSafe_nrf {F : Type} {sp0 : Nat} {s : PanSemStateFiniteExact 64 F}
    {Nd : List Nat} (h : NodeValuesSafe sp0 s Nd) : NrfStrong.NodeValuesSafe sp0 s Nd := by
  intro n hn
  obtain ⟨h1, h3⟩ := h n hn
  refine ⟨fun a b c => ?_, fun a b c => ?_⟩
  · obtain ⟨q1, q2, q3, q4⟩ := h1 a b c
    refine ⟨q1, fun gs hgs hpos => q2 (bufferRegion s gs) ?_ hpos, q3, q4⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hgs
    rcases hgs with rfl | rfl <;> simp [keccakBufIvls]
  · obtain ⟨q1, q2, q3, q4⟩ := h3 a b c
    refine ⟨q1, fun gs hgs hpos => q2 (bufferRegion s gs) ?_ hpos, q3, q4⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hgs
    rcases hgs with rfl | rfl <;> simp [keccakBufIvls]

/-- The `MptSetRootKeeps` form of the strong `mpt_root` guard gives the
`NodeRlpFill` form, at which `mpt_root` is bounded. -/
private theorem mptObjReadyStrong_nrf {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : MptObjReadyStrong s) : NrfStrong.MptObjReadyStrong s := by
  obtain ⟨hA, S, hWT, ⟨Nm0, hobj0, hv0⟩, hR, hAv, Nm, Nd, ⟨hobj, hv⟩, hTT, hd⟩ := h
  exact ⟨hA, S, hWT, ⟨Nm0, hobj0, nodeValuesSafe_nrf hv0⟩, hR, hAv, Nm, Nd,
    ⟨hobj, nodeValuesSafe_nrf hv⟩, hTT, hd⟩

private theorem callEntryOn_mpt_root_bmi_strong :
    CallEntryOn (fun s => BuildMptLoopInv s ∧ BmiW4 s) NrfStrong.MptObjReadyStrong
      (ofString "mpt_root") [.var .local (ofString "m"), .var .local (ofString "out")] := by
  intro F s values body callee ret hcode hP hargs hl
  obtain ⟨_, s0, S0, Nd0, hready0, heff, hinv⟩ := hP
  obtain ⟨v1, v2, he1, he2, hc1, hc2⟩ :=
    callee_param_two_exp s (ofString "mpt_root") (ofString "m") (ofString "out") .one .one _ _
      (by rw [hcode]; exact lookup_mpt_root_bmi4) _ _ values body callee ret hargs hl
  obtain ⟨wm, hwm, hm_nat⟩ := hinv.wm_lk
  have hm_c : callee.lookup (ofString "m") = some (.val (.word wm)) :=
    hc1.trans (by simpa only [evalAt, evalHOLExact, hwm] using he1.symm)
  have hstrong : MptObjReadyStrong (callEntryStateHOLFinite s callee) :=
    bmi4_mptObjReadyStrong (heff.locals_clock callee (s.clock - 1))
      (bmi4_mptInv_locals_clock hinv.mptInv callee (s.clock - 1))
      (by simp [callEntryStateHOLFinite, locN, hm_c, hm_nat])
  exact mptObjReadyStrong_nrf hstrong

private theorem buildMptIndexed_tail_bound_strong
    (hroot : TerminatingFunBoundedOn NrfStrong.MptObjReadyStrong (ofString "mpt_root")
      K.«mpt_root»)
    (hrelease : TerminatingFunBoundedOn GuestInv (ofString "heap_release") K.«heap_release») :
    TerminatingProgBoundedOn (fun s => BuildMptLoopInv s ∧ BmiW4 s)
      (.seq
        (.call (some (none, none)) (ofString "mpt_root")
          [.var .local (ofString "m"), .var .local (ofString "out")])
        (.seq
          (.call (some (none, none)) (ofString "heap_release")
            [.var .local (ofString "mark")])
          (.return (.const 0))))
      ((K.«mpt_root» + 1) + (K.«heap_release» + 1)) := by
  exact TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.seq_guestInv_after
      (TerminatingProgBoundedOn.call_on hroot none _ callEntryOn_mpt_root_bmi_strong)
      (fun s h => h.1.1.1.1.1)
      (TerminatingProgBoundedOn.seq_guestInv
        (TerminatingProgBoundedOn.call_guestInv hrelease none
          [.var .local (ofString "mark")])
        (TerminatingProgBoundedOn.of_clock (fun s => clock_return s (.const 0)))))
    (by omega)

/-- `gbody_build_mpt_indexed_strong` with the `mpt_root` premise at the
guard `MptObjReadyStrong` instead of `MptObjReady`. The other ten premises
are unchanged. -/
theorem gbody_build_mpt_indexed_rootStrong :
    (TerminatingFunBoundedOn GuestInv (ofString "heap_mark") K.«heap_mark») →
    (TerminatingFunBoundedOn GuestInv (ofString "heap_release") K.«heap_release») →
    (TerminatingFunBoundedOn GuestInv (ofString "mpt_new") K.«mpt_new») →
    (TerminatingFunBoundedOn NrfStrong.MptObjReadyStrong (ofString "mpt_root") K.«mpt_root») →
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
  have hwhile0 : TerminatingProgBoundedOn BuildMptLoopInv2 (.while bmiLoopCond bmiLoopBody)
      ((2 ^ 64 + 1) * ((K.«rlp_encode_word» + 1) + (K.«mpt_set» + 1) + 1)) :=
    TerminatingProgBoundedOn.while_rank_active buildMptLoopRank
      (fun _ hP => buildMptLoopInv2_decClock hP) (bmi3_loop_body_bound hrlp hset hwk_rlp)
      (fun _ _ hP _ => buildMptLoopRank_le hP.1)
      (fun s hc hP hact hflow => bmi3_loop_step hmk_set hwk_rlp s hc hP hact hflow)
  have hwhile : TerminatingProgBoundedOn (fun s => BuildMptLoopInv2 s ∧ BmiW4 s)
      (.while bmiLoopCond bmiLoopBody)
      ((2 ^ 64 + 1) * ((K.«rlp_encode_word» + 1) + (K.«mpt_set» + 1) + 1)) := by
    intro F state hcode hP
    exact hwhile0 state hcode hP.1
  have hloop_and_tail : TerminatingProgBoundedOn (fun s => BuildMptLoopInv2 s ∧ BmiW4 s)
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
    R16Shards.TerminatingProgBoundedOn.seq_hoare_trans hwhile
      (bmi_while_hoare_w4 hmk_set hwk_rlp)
      (buildMptIndexed_tail_bound_strong hroot hrelease)
  have hdec_i : TerminatingProgBoundedOn (fun s => BmiAfterNewStrong s ∧ BmiW4pre s)
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
    R16Shards.dec_eval_on (P := fun s => BmiAfterNewStrong s ∧ BmiW4pre s)
      (Q := fun s => BuildMptLoopInv2 s ∧ BmiW4 s) (ofString "i") .one (.const 0)
      (fun s v hP he => by
        have hv : v = .val (.word 0) := evalAt_const s 0 v he
        subst hv
        exact ⟨bmiAfterNewStrong_set_counter_loopInv2 hP.1 0, bmiW4pre_set_counter hP.2 0⟩)
      hloop_and_tail
  refine @TerminatingProgBoundedOn.mono_bound BuildMptIndexedReadyStrong _ _
    K.«build_mpt_indexed»
    (TerminatingProgBoundedOn.decCall_on hmark (ofString "mark") .one []
      (callEntryOn_of_imp (P := BuildMptIndexedReadyStrong) localsFree_guestInv
        (fun _ h => h.1.1.1.1) _ _)
      (decCallResume_heap_mark_bmi_strong hro_mark)
      (TerminatingProgBoundedOn.decCall_on hnew (ofString "m") .one [.const 0, .const 0]
        (callEntryOn_of_imp (P := fun s => BuildMptAfterMark s ∧ BmiAfterMarkC s)
          localsFree_guestInv (fun _ h => h.1.1.1.1.1) _ _)
        (decCallResume_mpt_new_bmi_w4 hwk_new hrt_new)
        hdec_i))
    ?_
  unfold K.«build_mpt_indexed»
  omega

/-- The bound of `mpt_root` at `MptObjReadyStrong`, with no premise. -/
theorem fb_mpt_root_strong :
    TerminatingFunBoundedOn NrfStrong.MptObjReadyStrong (ofString "mpt_root") K.«mpt_root» :=
  NrfStrong.gbody_mpt_root_strong Merged.fb_memcpy
    (NrfStrong.gbody_node_hash_strong Merged.fb_alloc PrimShardP10P30.fb_keccak256
      (NrfStrong.gbody_node_rlp_strong
        (NrfStrong.gbody__node_rlp_fill_strong_of Merged.fb__node_needs_rlp
          Merged.fb__node_rlp_begin Merged.fb__node_rlp_finish Merged.fb_scratch_alloc
          Merged.fb_scratch_mark Merged.fb_scratch_release)
        Merged.fb_mpt_fail R11Adapters.ReadOnlyLeaves.«ro_mpt_fail»))

/-- The bound of `build_mpt_indexed` at `BuildMptIndexedReadyStrong`, with no
premise. -/
theorem fb_build_mpt_indexed_strong :
    TerminatingFunBoundedOn BuildMptIndexedReadyStrong
      (ofString "build_mpt_indexed") K.«build_mpt_indexed» :=
  gbody_build_mpt_indexed_rootStrong PrimShardP10P30.fb_heap_mark PrimShardP10P30.fb_heap_release
    R11Adapters.«fb_mpt_new» fb_mpt_root_strong MptC10C12.gbody_mpt_set Merged.fb_rlp_encode_word
    Merged.ro_heap_mark R13Shards.WkShard01.«wk_mpt_new» R13Shards.WkShard01.«rt_mpt_new»
    MptC10C12.«mk_mpt_set» Merged.wk_rlp_encode_word

end InitECandidate.Solver.Wave8GuestInv.R16Shards.MptC10C12.BmiBound
