import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxPhase1Entries
import InitECandidate.Solver.Wave8GuestInv.Expressions
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody.R10.Phase1
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded

theorem resume_encode (h : PtxCallees) :
    DecCallResumeShapeOn TxReadyStrong EncReady (ofString "enc") (.comb [.one,.one])
      (ofString "encode_transaction") [.var .local (ofString "tx")] := by
  intro F s vs body callee ret v post hc hP ha hl hb hsh
  obtain ⟨tv, he, ht⟩ := params_one_value s (ofString "encode_transaction") (ofString "tx")
    .one _ (.comb [.one,.one]) (by rw [hc]; exact lookup_encode_transaction)
    (.var .local (ofString "tx")) vs body callee ret ha hl
  have htx : callee.lookup (ofString "tx") = s.locals.lookup (ofString "tx") := ht.trans he.symm
  have hV := txValid_with_locals s callee (s.clock - 1) htx hP.2.1
  have hs := funSpec_at_lookup h.wk_encode_transaction s hc vs body callee ret hl
    ⟨worldOK_callEntry hP.1.1 callee, hV⟩ (by rw [hb]; simp)
  rw [hb] at hs
  have hstage := stage_after_scratchStep (hs (Or.inl ⟨v,rfl⟩)) (stage0 hP)
    (gs := []) (by simp [ScratchSet]) rfl (by decide) (by decide)
    (boKeep := [0,8,16,24,32,40,48,56,64,72,80]) (by simp) (by decide)
  have hready := txReadyStrong_with_locals {post with locals := s.locals}
    (s.locals.update (ofString "enc",v)) post.clock
    (by simp [HolFiniteMapExact.update, FUPDATE, show ofString "enc" ≠ ofString "tx" from by decide])
    (by simp [HolFiniteMapExact.update, FUPDATE, show ofString "enc" ≠ ofString "index" from by decide]) hstage.1
  obtain ⟨a,b,rfl⟩ := shape_pair_words hsh
  refine ⟨hready, a,b, ?_⟩
  simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]

def SenderAllocated {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  TxReadyStrong s ∧ SenderOK s ∧ ∃ S Nd, WorldTypedWith s S Nd ∧ TxAccessListOK s S Nd ∧
    (∀ j ∈ worldTypedIvls s S Nd, Disj (locN s "sender",24) j) ∧
    Disj (locN s "tx",384) (locN s "sender",24) ∧
    (memW s (locN s "tx") ≠ 0 → 0 < memW s (locN s "tx" + 216) →
      Disj (memW s (locN s "tx" + 208),24 * memW s (locN s "tx" + 216)) (locN s "sender",24))

theorem resume_alloc_sender (h : PtxCallees) :
    DecCallResumeOn (StageP 0) SenderAllocated (ofString "sender") (ofString "alloc") [.const 24] := by
  intro F s vs body callee ret v post hc hP ha hl hb
  obtain ⟨nv, he, hn⟩ := params_one_value s (ofString "alloc") (ofString "n")
    .one _ .one (by rw [hc]; exact lookup_alloc) (.const 24) vs body callee ret ha hl
  have hnv : nv = .val (.word (24#64)) := by simpa [evalAt, evalHOLExact] using he.symm
  subst nv
  have hcn : locN (callEntryStateHOLFinite s callee) "n" = 24 := by simp [locN, callEntryStateHOLFinite, hn]
  have hrt := funSpec_at_lookup h.rt_alloc s hc vs body callee ret hl
    ((arenaReady_with_locals s callee (s.clock - 1)).mpr hP.1.1.1.1) (by rw [hb]; simp)
  rw [hb] at hrt
  obtain ⟨w,hv,hAp,hgrow,hfb⟩ := hrt v rfl
  subst v
  rw [hcn] at hfb
  change FreshBlock (callEntryStateHOLFinite s callee) post w.toNat 24 at hfb
  have hpFresh : globN s "heap_ptr" ≤ w.toNat := hfb.2.1.1
  have hs := funSpec_at_lookup h.wk_alloc s hc vs body callee ret hl
    (worldOK_callEntry hP.1.1.1 callee) (by rw [hb]; simp)
  rw [hb] at hs
  have hstep := hs (Or.inl ⟨.val (.word w),rfl⟩)
  have hsready := stage_after_scratchStep hstep hP (gs := []) (by simp [ScratchSet]) rfl
    (by decide) (by decide) (boKeep := [0,8,16,24,32,40,48,56,64,72,80]) (by simp) (by decide)
  obtain ⟨S,Nd,hW,hT⟩ := hP.1.2.2.2.2.2
  obtain ⟨S',Nd',_,hW',hog,hfr,hret⟩ := hstep.2.2.2.2 S Nd
    ((worldTypedWith_with_locals s callee (s.clock - 1) S Nd).mpr hW) (by simp [IvlsDisj])
  obtain ⟨w',heq,hav⟩ := hret (.val (.word w)) rfl
  have hww : w' = w := by cases heq; rfl
  subst w'
  dsimp only at hav
  rw [hcn] at hav
  change IvlsDisj [(w.toNat,24)] (worldOwned post S' Nd') at hav
  have hT' := txAccessListOK_survives_step hP.1.1.1.1.2 hstep.2.1 hW
    (R := []) (by simp) hog hfr hT (by simp) (by simp) (locals := s.locals) rfl
  obtain ⟨_,_,hu⟩ := heap_ivl_survives_step hP.1.1.1.1.2 hstep.2.1
    (worldOwned_zero_aligned hW) (R := []) (by simp) hog hfr hT.1 (by simp)
    hT.2.1 hT.2.2.1 (by simp)
  have hhi := (ivl_allocated_bound hP.1.1.1.1.2 (Or.inl hT.2.1)).2
  have hm0 : memW post (locN s "tx") = memW s (locN s "tx") :=
    memW_eq_of_ivlUnhit hu hT.1 hhi ⟨le_rfl,by omega⟩
  have hm208 : memW post (locN s "tx" + 208) = memW s (locN s "tx" + 208) :=
    memW_eq_of_ivlUnhit hu (by have := hT.1; omega) hhi ⟨by omega,by omega⟩
  have hm216 : memW post (locN s "tx" + 216) = memW s (locN s "tx" + 216) :=
    memW_eq_of_ivlUnhit hu (by have := hT.1; omega) hhi ⟨by omega,by omega⟩
  let resumed := setVarHOLFinite (ofString "sender") (.val (.word w)) {post with locals := s.locals}
  have htx : resumed.locals.lookup (ofString "tx") = s.locals.lookup (ofString "tx") := by
    simp [resumed,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,
      show ofString "sender" ≠ ofString "tx" from by decide]
  have hidx : resumed.locals.lookup (ofString "index") = s.locals.lookup (ofString "index") := by
    simp [resumed,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,
      show ofString "sender" ≠ ofString "index" from by decide]
  have hsender : locN resumed "sender" = w.toNat := by
    simp [resumed,locN,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  have htxN : locN resumed "tx" = locN s "tx" := locN_congr s resumed.locals post.clock "tx" htx
  have hrdy : TxReadyStrong resumed := txReadyStrong_with_locals {post with locals := s.locals}
    resumed.locals post.clock htx hidx hsready.1
  refine ⟨hrdy, ?_, S',Nd', ?_, ?_, ?_, ?_, ?_⟩
  · unfold SenderOK
    rw [hsender]
    exact ⟨⟨hP.1.1.1.1.2.1.trans hpFresh,hfb.2.1.2⟩,hfb.2.2⟩
  · exact (worldTypedWith_with_locals post resumed.locals post.clock S' Nd').mpr hW'
  · exact txAccessListOK_with_locals {post with locals := s.locals} resumed.locals post.clock htx hT'
  · rw [hsender]
    exact typed_disj_of_owned (fun j hj => hav _ (by simp) j hj)
  · rw [htxN,hsender]
    exact Or.inr (Or.inr (Or.inl (hT.2.1.2.trans hpFresh)))
  · rw [htxN,hsender]
    change memW post (locN s "tx") ≠ 0 → 0 < memW post (locN s "tx" + 216) →
      Disj (memW post (locN s "tx" + 208),24 * memW post (locN s "tx" + 216)) (w.toNat,24)
    rw [hm0,hm208,hm216]
    intro ht hn
    exact Or.inr (Or.inr (Or.inl (((hT.2.2.2 ht).2.1 hn).2.1.2.trans hpFresh)))

end InitECandidate.Solver.Wave8GuestInv.GuardedBody.R10.Phase1
