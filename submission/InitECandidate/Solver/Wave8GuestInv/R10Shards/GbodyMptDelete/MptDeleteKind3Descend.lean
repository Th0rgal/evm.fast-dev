import InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptDelete.MptDeleteKind3Post

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
def mptBranchDescend : ProgHOL 64 :=
  .dec (ofString "idx") .one (.loadByte (.op .add
    [.var .local (ofString "key"), .var .local (ofString "level")]))
    (.decCall (ofString "fr2") .one (ofString "scratch_alloc") [.const 40] mptBranchCont)

theorem mptBranchDescend_run (h : MptDeleteCallees)
    {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (hc : s.code = originalRuntimeCode) (hs : MptDeleteBranchReady s)
    (hlt : locN s "level" < locN s "klen")
    (hr : evaluateHOLFiniteState s mptBranchDescend = (none, t)) :
    MptDeleteHead t ∧ globN t "scratch_ptr" + 40 ≤ globN s "scratch_ptr" := by
  obtain ⟨v, inner, hv, hcall, ht⟩ := mptDec_none hr
  obtain ⟨aw, haw⟩ := mptByte_addr hv
  obtain ⟨kw, lw, hkw, hlw, _⟩ := mptAddLocals_inv haw
  have hadd : kw + lw = BitVec.ofNat 64 (locN s "key" + locN s "level") := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, mptLocal_word hkw, mptLocal_word hlw]
  have haddr := mptAddLocals_eval hkw hlw
  rw [hadd] at haddr
  obtain ⟨iw, rfl, hiw⟩ := mptByte_inv haddr hv
  have hi : iw.toNat < 16 := by
    rw [hiw]
    obtain ⟨_, _, _, Nd, fs, _, _, _, _, _, hk⟩ := hs
    rcases hk with hz | hk
    · omega
    · simpa only [Nat.add_zero] using hk.1 0 (by omega)
  let si := setVarHOLFinite (ofString "idx") (.val (.word iw)) s
  have hsi : MptDeleteBranchReady si := mptBranchReady_idx iw hs
  obtain ⟨values, body, callee, ret, v, post, mid, hargs, hl, hbody, hcont, hinner⟩ :=
    mptDecCall_none hcall
  obtain ⟨pw, rfl, hpost, hg, hfresh, _, hbe, hframe⟩ :=
    mptScratch_return h (s := si) hc hsi.1 hargs hl hbody
  let u := setVarHOLFinite (ofString "fr2") (.val (.word pw)) { post with locals := si.locals }
  have hufr : u.locals.lookup (ofString "fr2") = some (.val (.word pw)) := by
    simp only [u, setVarHOLFinite, HolFiniteMapExact.lookup_update_pointwise, if_true]
  have huloc : ∀ n : String, ofString n ≠ ofString "fr2" →
      u.locals.lookup (ofString n) = si.locals.lookup (ofString n) := by
    intro n hn
    simp only [u, setVarHOLFinite, HolFiniteMapExact.lookup_update_pointwise, hn, if_false]
  have hilev : si.locals.lookup (ofString "level") = some (.val (.word lw)) := by
    simp +decide only [si, setVarHOLFinite, HolFiniteMapExact.lookup_update_pointwise, if_false]
    exact hlw
  have hiidx : si.locals.lookup (ofString "idx") = some (.val (.word iw)) := by
    simp only [si, setVarHOLFinite, HolFiniteMapExact.lookup_update_pointwise, if_true]
  have hilt : locN si "level" < locN si "klen" := by
    simpa +decide only [si, locN, setVarHOLFinite, HolFiniteMapExact.lookup_update_pointwise, if_false] using hlt
  have hdone := mptBranchCont_run (s := si) (u := u) hsi
    ((arenaReady_with_locals post u.locals post.clock).2 hpost) hbe hg hfresh hufr huloc hiidx hi hilev hilt
    hframe hcont
  subst inner
  subst t
  refine ⟨mptHead_restore (ofString "idx") _ ?_
    (mptHead_restore (ofString "fr2") _ ?_ hdone.1), hdone.2⟩
  all_goals simp +decide only [List.forall_mem_cons, List.forall_mem_nil, and_true]

end InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptDelete
