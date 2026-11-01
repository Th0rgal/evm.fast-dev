import InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptDelete.MptDeleteKind3Push

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
theorem mptBranchCont_run {F : Type} {s u t : PanSemStateFiniteExact 64 F}
    (hs : MptDeleteBranchReady s) (hu : ArenaReady u) (hbe : u.be = s.be)
    (hg : AllocatorGrows s u) {pw iw lw : BitVec 64}
    (hfresh : FreshScratch s u pw.toNat 40)
    (hfr2 : u.locals.lookup (ofString "fr2") = some (.val (.word pw)))
    (hloc : ∀ n : String, ofString n ≠ ofString "fr2" → u.locals.lookup (ofString n) = s.locals.lookup (ofString n))
    (hidx : s.locals.lookup (ofString "idx") = some (.val (.word iw)))
    (hi : iw.toNat < 16)
    (hlev : s.locals.lookup (ofString "level") = some (.val (.word lw)))
    (hlt : locN s "level" < locN s "klen")
    (hfr : FrameOutside s u
      [(globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr")]
      (globN s "heap_ptr", heapLimit - globN s "heap_ptr"))
    (hr : evaluateHOLFiniteState u mptBranchCont = (none, t)) :
    MptDeleteHead t ∧ globN t "scratch_ptr" + 40 ≤ globN s "scratch_ptr" := by
  obtain ⟨ha, _, _, Nd, fs, hn, hst, hres, hlevel, hnode, hkey⟩ := hs
  have hnonzero : locN s "node" ≠ 0 := by
    have hb : 0 < sourceBase := by decide
    have hh := (hn.1 _ hnode.1).2.2.1.1
    change sourceBase ≤ locN s "node" at hh
    omega
  obtain ⟨nw, hnw, hnn⟩ := mptLocN_nonzero hnonzero
  have hnwu : u.locals.lookup (ofString "node") = some (.val (.word nw)) :=
    (hloc "node" (by decide)).trans hnw
  have hiwu : u.locals.lookup (ofString "idx") = some (.val (.word iw)) :=
    (hloc "idx" (by decide)).trans hidx
  have hlwu : u.locals.lookup (ofString "level") = some (.val (.word lw)) :=
    (hloc "level" (by decide)).trans hlev
  obtain ⟨a, h0, hr⟩ := mptSeq_none hr
  obtain ⟨b, h8, hr⟩ := mptSeq_none hr
  obtain ⟨c, h16, hr⟩ := mptSeq_none hr
  obtain ⟨d, h32, hr⟩ := mptSeq_none hr
  obtain ⟨e, htop, hr⟩ := mptSeq_none hr
  have hld : d.locals = u.locals :=
    (mptStore_locals h32).trans ((mptStore_locals h16).trans
      ((mptStore_locals h8).trans (mptStore_locals h0)))
  obtain ⟨topval, htv, hvalid, he⟩ := mptAssign_none htop
  change d.locals.lookup (ofString "fr2") = some topval at htv
  rw [hld, hfr2] at htv
  cases htv
  obtain ⟨tw, htw⟩ := mptValid_word_local hvalid
  rw [hld] at htw
  have htopnat : tw.toNat = locN s "top" := by
    have hh := (hloc "top" (by decide)).symm.trans htw
    exact (mptLocal_word hh).symm
  have heqa := mptStore_word_none (src := .var .local (ofString "top")) (mptAddConst_eval 0 hfr2) htw h0
  simp only [Nat.add_zero] at heqa
  subst a
  have heqb := mptStore_word_none (src := .var .local (ofString "node")) (mptAddConst_eval (s := mptWordWrite u pw.toNat tw) 8 hfr2) hnwu h8
  subst b
  have heqc := mptStore_word_none (mptAddConst_eval (s := mptWordWrite (mptWordWrite u pw.toNat tw) (pw.toNat + 8) nw) 16 hfr2) (show evalAt _ (.const 3) = _ from rfl) h16
  subst c
  have heqd := mptStore_word_none (src := .var .local (ofString "idx")) (mptAddConst_eval (s := mptWordWrite (mptWordWrite (mptWordWrite u pw.toNat tw) (pw.toNat + 8) nw) (pw.toNat + 16) 3) 32 hfr2) hiwu h32
  change d = mptBranchFrame u pw.toNat tw nw iw at heqd
  subst d
  subst e
  obtain ⟨f, hchild, hr⟩ := mptSeq_none hr
  obtain ⟨cv, hcv, _, hf⟩ := mptAssign_none hchild
  have hne : (setVarHOLFinite (ofString "top") (.val (.word pw))
      (mptBranchFrame u pw.toNat tw nw iw)).locals.lookup (ofString "node") = some (.val (.word nw)) := by
    simp only [setVarHOLFinite, HolFiniteMapExact.lookup_update_pointwise]
    simpa +decide [mptBranchFrame, mptWordWrite] using hnwu
  have hie : (setVarHOLFinite (ofString "top") (.val (.word pw))
      (mptBranchFrame u pw.toNat tw nw iw)).locals.lookup (ofString "idx") = some (.val (.word iw)) := by
    simp only [setVarHOLFinite, HolFiniteMapExact.lookup_update_pointwise]
    simpa +decide [mptBranchFrame, mptWordWrite] using hiwu
  obtain ⟨cw, rfl, hcwn⟩ := mptLoad_inv (mptChildAddr_eval hne hie) hcv
  subst f
  obtain ⟨g, hinc, hr⟩ := mptSeq_none hr
  obtain ⟨lv, hlv, _, hgstate⟩ := mptAssign_none hinc
  have hlg : (setVarHOLFinite (ofString "node") (.val (.word cw))
      (setVarHOLFinite (ofString "top") (.val (.word pw))
      (mptBranchFrame u pw.toNat tw nw iw))).locals.lookup (ofString "level") = some (.val (.word lw)) := by
    simp only [setVarHOLFinite, HolFiniteMapExact.lookup_update_pointwise]
    simpa +decide [mptBranchFrame, mptWordWrite] using hlwu
  have hleval := mptAddConst_eval 1 hlg
  have heqlv := Option.some.inj (hlv.symm.trans hleval)
  subst lv
  subst g
  obtain ⟨gv, hgv, _, ht⟩ := mptAssign_none hr
  have hgone := evalAt_const _ 1 gv hgv
  subst gv
  subst t
  let d := mptBranchFrame u pw.toNat tw nw iw
  obtain ⟨had, hnd, hstack, hkeys, htags⟩ := mptBranchFrame_push ha hu hbe hg hfresh hn hst
    htopnat (by rw [hnn]; exact hnode.1) (by rw [hnn]; exact hnode.2) hi hfr
  let t := setVarHOLFinite (ofString "go") (.val (.word 1))
    (setVarHOLFinite (ofString "level") (.val (.word (BitVec.ofNat 64 (lw.toNat + 1))))
    (setVarHOLFinite (ofString "node") (.val (.word cw))
    (setVarHOLFinite (ofString "top") (.val (.word pw)) d)))
  change MptDeleteHead t ∧ globN t "scratch_ptr" + 40 ≤ globN s "scratch_ptr"
  have hlwn := mptLocal_word hlev
  have hlwlt : lw.toNat + 1 < 2 ^ 64 := by
    have hkn : locN s "klen" < 2 ^ 64 := by
      obtain ⟨kw, _, hkw⟩ := mptLocN_nonzero (s := s) (n := "klen") (by omega)
      rw [← hkw]
      exact kw.isLt
    omega
  have htopn : locN t "top" = pw.toNat := by
    simp +decide only [t, locN, setVarHOLFinite, HolFiniteMapExact.lookup_update_pointwise, if_true, if_false]
  have hnoden : locN t "node" = cw.toNat := by
    simp +decide only [t, locN, setVarHOLFinite, HolFiniteMapExact.lookup_update_pointwise, if_true, if_false]
  have hleveln : locN t "level" = locN s "level" + 1 := by
    simp +decide only [t, locN, setVarHOLFinite, HolFiniteMapExact.lookup_update_pointwise,
      if_true, if_false, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlwlt, hlev]
  have hsame (n : String) (hne : n ∈ ["key", "klen", "res"]) : locN t n = locN s n := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hne
    rcases hne with rfl | rfl | rfl
    all_goals simp +decide only [t, d, mptBranchFrame, mptWordWrite, locN, setVarHOLFinite,
      HolFiniteMapExact.lookup_update_pointwise, if_true, if_false, hloc "key" (by decide), hloc "klen" (by decide), hloc "res" (by decide)]
  have hchildroot : RootIn Nd cw.toNat := by
    rw [hcwn]
    exact (hnd.1 _ (by rw [hnn]; exact hnode.1)).2.2.2.2.2.1
      (by change memW d nw.toNat = 3
          rw [htags _ (by rw [hnn]; exact hnode.1), hnn]
          exact hnode.2) iw.toNat hi
  refine ⟨⟨(arenaReady_with_locals d t.locals d.clock).2 had, Nd, pw.toNat :: fs,
    (mptNodeHeap_locals d t.locals d.clock Nd).2 hnd, ?_, ?_, ?_⟩, ?_⟩
  · rw [htopn]
    exact (mptStack_locals d t.locals d.clock Nd _ _).2 hstack
  · rw [hsame "res" (by simp)]
    exact hres
  · intro _
    rw [hleveln, hsame "klen" (by simp), hnoden, hsame "key" (by simp)]
    refine ⟨by omega, hchildroot, ?_⟩
    exact (mptKeyIn_locals d t.locals d.clock Nd _ _).2
      (hkeys _ _ (mptKeyIn_sub hkey (by omega) (by omega)))
  · change globN u "scratch_ptr" + 40 ≤ globN s "scratch_ptr"
    have hp := hfresh.2.2.1
    change globN u "scratch_ptr" ≤ pw.toNat ∧ pw.toNat + 40 ≤ globN s "scratch_ptr" at hp
    omega

end InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptDelete
