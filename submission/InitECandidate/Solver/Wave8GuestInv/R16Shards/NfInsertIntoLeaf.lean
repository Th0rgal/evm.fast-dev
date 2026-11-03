import InitECandidate.Solver.Wave8GuestInv.R16Shards.NfNodeNewLeaf
import InitECandidate.Solver.Wave8GuestInv.R16Shards.NfNodeNewExt

/-! `nf__insert_into_leaf`: `_insert_into_leaf(node, rk, rl, vptr, vlen)` preserves typed node heaps
(`NodeFn ["node"]` under `NodeKind s Nd "node" 1 ∧ KeyIn s Nd (locN s "rk") (locN s "rl") ∧ locN s "vlen" < 2 ^ 40`). -/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.style.nameCheck false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

private theorem node_new_leaf_body_no_nonTrap_exn {F : Type}
    (st : PanSemStateFiniteExact 64 F) (hcode : st.code = originalRuntimeCode)
    (eid : MlS) (ev : ValueHOL 64) (hne : eid ≠ ofString "TrapErr") :
    (evaluateHOLFiniteState st (sourceFnBody Guest.Software.guestFn_node_new_leaf)).1 ≠
      some (.exception eid ev) := by
  intro hexn
  have hbody : sourceFnBody Guest.Software.guestFn_node_new_leaf =
      .decCall (ofString "nd") .one (ofString "alloc") [.const 64]
        (.seq (.store (.op .add [.var .local (ofString "nd"), .const 0]) (.const 1))
          (.seq (.store (.op .add [.var .local (ofString "nd"), .const 8]) (.const 0))
            (.seq (.store (.op .add [.var .local (ofString "nd"), .const 16]) (.const 0))
              (.seq (.store (.op .add [.var .local (ofString "nd"), .const 24]) (.const 0))
                (.seq (.store (.op .add [.var .local (ofString "nd"), .const 32]) (.var .local (ofString "nib")))
                  (.seq (.store (.op .add [.var .local (ofString "nd"), .const 40]) (.var .local (ofString "nlen")))
                    (.seq (.store (.op .add [.var .local (ofString "nd"), .const 48]) (.var .local (ofString "vptr")))
                      (.seq (.store (.op .add [.var .local (ofString "nd"), .const 56]) (.var .local (ofString "vlen")))
                        (.return (.var .local (ofString "nd"))))))))))) := rfl
  rw [hbody] at hexn
  obtain ⟨avals, _, acallee, _, _, _, ahl, ahexn | ⟨_, _, _, _, _, ahr, _⟩⟩ :=
    decCall_resumes_inv (Or.inr ⟨eid, ev, hexn, hne⟩)
  · obtain ⟨aeid, aev, aha, ahne, _⟩ := ahexn
    have ahsame := lookupCodeHOLFinite_installed_body st.code.lookup (ofString "alloc")
      _ _ _ _ _ avals acallee (by rw [hcode]; exact lookup_alloc) ahl
    subst ahsame
    obtain ⟨_, ahret⟩ := alloc_body_resumes_eq_returned (callEntryStateHOLFinite st acallee) hcode
      (by rw [aha]; exact Or.inr ⟨aeid, aev, rfl, ahne⟩)
    rw [aha] at ahret; cases ahret
  · rw [hexn] at ahr
    exact evaluate_noExnProg _ (by decide) _ eid ev ahr.symm

private theorem cbtl_arm_step {F : Type}
    {s : PanSemStateFiniteExact 64 F} {Nd : List Nat}
    {kn ln vn vln lfn : String}
    {wbr wk wl wv wvl : BitVec 64}
    {cont : ProgHOL 64}
    (hcode : s.code = originalRuntimeCode)
    (ha : ArenaReady s) (hNd : NodeHeap s Nd)
    (hbr_in : wbr.toNat ∈ Nd) (hbr_k : memW s wbr.toNat = 3)
    (hkey : KeyIn s Nd wk.toNat wl.toNat) (hvl_lt : wvl.toNat < 2 ^ 40)
    (hl_br : s.locals.lookup (ofString "br") = some (.val (.word wbr)))
    (hl_k : s.locals.lookup (ofString kn) = some (.val (.word wk)))
    (hl_l : s.locals.lookup (ofString ln) = some (.val (.word wl)))
    (hl_v : s.locals.lookup (ofString vn) = some (.val (.word wv)))
    (hl_vl : s.locals.lookup (ofString vln) = some (.val (.word wvl)))
    (hne_lf_br : ofString "br" ≠ ofString lfn)
    (hne_lf_k : ofString kn ≠ ofString lfn)
    (hres : Resumes (evaluateHOLFiniteState s
      (.seq
        (.ite (.cmp .equal (.var .local (ofString ln)) (.const 0))
          (.seq
            (.store (.op .add [.var .local (ofString "br"), .const 160]) (.var .local (ofString vn)))
            (.store (.op .add [.var .local (ofString "br"), .const 168]) (.var .local (ofString vln))))
          (.decCall (ofString lfn) .one (ofString "node_new_leaf")
            [.op .add [.var .local (ofString kn), .const 1],
             .op .sub [.var .local (ofString ln), .const 1],
             .var .local (ofString vn),
             .var .local (ofString vln)]
            (.store (.op .add [.var .local (ofString "br"), .const 32,
                .panop .mul [.loadByte (.var .local (ofString kn)), .const 8]])
              (.var .local (ofString lfn)))))
        cont)).1) :
    ∃ (mid : PanSemStateFiniteExact 64 F) (Nd' : List Nat),
      evaluateHOLFiniteState s
        (.seq
          (.ite (.cmp .equal (.var .local (ofString ln)) (.const 0))
            (.seq
              (.store (.op .add [.var .local (ofString "br"), .const 160]) (.var .local (ofString vn)))
              (.store (.op .add [.var .local (ofString "br"), .const 168]) (.var .local (ofString vln))))
            (.decCall (ofString lfn) .one (ofString "node_new_leaf")
              [.op .add [.var .local (ofString kn), .const 1],
               .op .sub [.var .local (ofString ln), .const 1],
               .var .local (ofString vn),
               .var .local (ofString vln)]
              (.store (.op .add [.var .local (ofString "br"), .const 32,
                  .panop .mul [.loadByte (.var .local (ofString kn)), .const 8]])
                (.var .local (ofString lfn)))))
          cont) = evaluateHOLFiniteState mid cont ∧
      Resumes (evaluateHOLFiniteState mid cont).1 ∧
      mid.code = originalRuntimeCode ∧
      (∀ x : MlS, x ≠ ofString lfn → mid.locals.lookup x = s.locals.lookup x) ∧
      NodeStep s mid Nd Nd' ∧
      wbr.toNat ∈ Nd' ∧
      memW mid wbr.toNat = 3 := by
  have hc_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .equal (.var .local (ofString ln)) (.const 0)) =
      some (.val (.word (if wl = 0 then 1 else 0))) := by
    simp [evalHOLExact, hl_l, Compiler.Encoders.Asm.wordCmpHOL]
  by_cases hwl0 : wl = 0
  · have hite : evaluateHOLFiniteState s
        (.ite (.cmp .equal (.var .local (ofString ln)) (.const 0))
          (.seq
            (.store (.op .add [.var .local (ofString "br"), .const 160]) (.var .local (ofString vn)))
            (.store (.op .add [.var .local (ofString "br"), .const 168]) (.var .local (ofString vln))))
          (.decCall (ofString lfn) .one (ofString "node_new_leaf")
            [.op .add [.var .local (ofString kn), .const 1],
             .op .sub [.var .local (ofString ln), .const 1],
             .var .local (ofString vn),
             .var .local (ofString vln)]
            (.store (.op .add [.var .local (ofString "br"), .const 32,
                .panop .mul [.loadByte (.var .local (ofString kn)), .const 8]])
              (.var .local (ofString lfn))))) =
        evaluateHOLFiniteState s
          (.seq
            (.store (.op .add [.var .local (ofString "br"), .const 160]) (.var .local (ofString vn)))
            (.store (.op .add [.var .local (ofString "br"), .const 168]) (.var .local (ofString vln)))) := by
      rw [evaluateHOLFiniteState_ite, hc_ev, if_pos hwl0]; simp
    obtain ⟨hdom160, hdom168, hstep, hmw3⟩ := branch_store_value_step ha hNd hbr_in hbr_k hvl_lt
    set m1 := Wave8Contracts.M26.updW s.memory (wbr + BitVec.ofNat 64 160) wv
    set m2 := Wave8Contracts.M26.updW m1 (wbr + BitVec.ofNat 64 168) wvl
    have h2stores : evaluateHOLFiniteState s
        (.seq
          (.store (.op .add [.var .local (ofString "br"), .const 160]) (.var .local (ofString vn)))
          (.store (.op .add [.var .local (ofString "br"), .const 168]) (.var .local (ofString vln)))) =
        (none, { s with memory := m2 }) := by
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_store]
      have hd1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
          (.op .add [.var .local (ofString "br"), .const 160]) =
          some (.val (.word (wbr + BitVec.ofNat 64 160))) := by
        simp [evalHOLExact, evalListHOLExact, hl_br, valueIsWord, valueWord, wordOpHOL, wordOp]
      have he1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
          (.var .local (ofString vn)) = some (.val (.word wv)) := hl_v
      rw [hd1, he1]
      simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL, hdom160, ↓reduceIte]
      set st1 : PanSemStateFiniteExact 64 F := { s with memory := m1 }
      change evaluateHOLFiniteState st1
        (.store (.op .add [.var .local (ofString "br"), .const 168]) (.var .local (ofString vln))) =
        (none, { s with memory := m2 })
      rw [evaluateHOLFiniteState_store]
      have hd2 : @evalHOLExact 64 F _ st1.toExact (fun a => Classical.propDecidable (st1.memaddrs a))
          (.op .add [.var .local (ofString "br"), .const 168]) =
          some (.val (.word (wbr + BitVec.ofNat 64 168))) := by
        simp [st1, evalHOLExact, evalListHOLExact, hl_br, valueIsWord, valueWord, wordOpHOL, wordOp]
      have he2 : @evalHOLExact 64 F _ st1.toExact (fun a => Classical.propDecidable (st1.memaddrs a))
          (.var .local (ofString vln)) = some (.val (.word wvl)) := hl_vl
      rw [hd2, he2]
      have hdom168' : st1.memaddrs (wbr + BitVec.ofNat 64 168) := hdom168
      simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL, hdom168', ↓reduceIte]
      rfl
    have hseq_eq : evaluateHOLFiniteState s
        (.seq
          (.ite (.cmp .equal (.var .local (ofString ln)) (.const 0))
            (.seq
              (.store (.op .add [.var .local (ofString "br"), .const 160]) (.var .local (ofString vn)))
              (.store (.op .add [.var .local (ofString "br"), .const 168]) (.var .local (ofString vln))))
            (.decCall (ofString lfn) .one (ofString "node_new_leaf")
              [.op .add [.var .local (ofString kn), .const 1],
               .op .sub [.var .local (ofString ln), .const 1],
               .var .local (ofString vn),
               .var .local (ofString vln)]
              (.store (.op .add [.var .local (ofString "br"), .const 32,
                  .panop .mul [.loadByte (.var .local (ofString kn)), .const 8]])
                (.var .local (ofString lfn)))))
          cont) = evaluateHOLFiniteState { s with memory := m2 } cont := by
      rw [evaluateHOLFiniteState_seq_line780, hite, h2stores]
    rw [hseq_eq] at hres
    exact ⟨{ s with memory := m2 }, Nd, hseq_eq, hres, hcode, fun _ _ => rfl, hstep, hbr_in, hmw3⟩
  · have hwl_pos : wl.toNat ≠ 0 := fun hz => hwl0 (BitVec.eq_of_toNat_eq hz)
    set dcProg : ProgHOL 64 :=
      .decCall (ofString lfn) .one (ofString "node_new_leaf")
        [.op .add [.var .local (ofString kn), .const 1],
         .op .sub [.var .local (ofString ln), .const 1],
         .var .local (ofString vn),
         .var .local (ofString vln)]
        (.store (.op .add [.var .local (ofString "br"), .const 32,
            .panop .mul [.loadByte (.var .local (ofString kn)), .const 8]])
          (.var .local (ofString lfn)))
    have hite : evaluateHOLFiniteState s
        (.ite (.cmp .equal (.var .local (ofString ln)) (.const 0))
          (.seq
            (.store (.op .add [.var .local (ofString "br"), .const 160]) (.var .local (ofString vn)))
            (.store (.op .add [.var .local (ofString "br"), .const 168]) (.var .local (ofString vln))))
          dcProg) = evaluateHOLFiniteState s dcProg := by
      rw [evaluateHOLFiniteState_ite, hc_ev, if_neg hwl0]; simp
    have hseq1 := evaluateHOLFiniteState_seq_line780 s
      (.ite (.cmp .equal (.var .local (ofString ln)) (.const 0))
        (.seq
          (.store (.op .add [.var .local (ofString "br"), .const 160]) (.var .local (ofString vn)))
          (.store (.op .add [.var .local (ofString "br"), .const 168]) (.var .local (ofString vln))))
        dcProg) cont
    rw [hite] at hseq1
    have hdc := evaluateHOLFiniteState_decCall_total s (ofString lfn) .one (ofString "node_new_leaf")
      [.op .add [.var .local (ofString kn), .const 1],
       .op .sub [.var .local (ofString ln), .const 1],
       .var .local (ofString vn),
       .var .local (ofString vln)]
      (.store (.op .add [.var .local (ofString "br"), .const 32,
          .panop .mul [.loadByte (.var .local (ofString kn)), .const 8]])
        (.var .local (ofString lfn)))
    have hargs_ev : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        [.op .add [.var .local (ofString kn), .const 1],
         .op .sub [.var .local (ofString ln), .const 1],
         .var .local (ofString vn),
         .var .local (ofString vln)] =
        some [.val (.word (wk + 1)), .val (.word (wl - 1)), .val (.word wv), .val (.word wvl)] := by
      rw [evalListHOLFinite_eq_toExact]
      simp [evalListHOLExact, evalHOLExact, hl_k, hl_l, hl_v, hl_vl, valueIsWord, valueWord, wordOpHOL, wordOp]
    rw [hargs_ev] at hdc
    dsimp only at hdc
    rcases hlk_lf : lookupCodeHOLFinite s.code.lookup (ofString "node_new_leaf")
        [.val (.word (wk + 1)), .val (.word (wl - 1)), .val (.word wv), .val (.word wvl)] with
      _ | ⟨lfBody, lfCallee, lfRet⟩
    · rw [hlk_lf] at hdc; rw [hseq1, hdc] at hres; exact absurd hres not_resumes_error
    · rw [hlk_lf] at hdc
      dsimp only at hdc
      by_cases hcz : s.clock = 0
      · rw [if_pos hcz] at hdc; rw [hseq1, hdc] at hres
        rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
      · rw [if_neg hcz] at hdc
        have hrem := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite s lfCallee) lfBody
        rcases hlf_run : evaluateHOLFiniteState (callEntryStateHOLFinite s lfCallee) lfBody with ⟨lfr, lfPost⟩
        have hfix : fixClockHOLFinite (callEntryStateHOLFinite s lfCallee)
            (evaluateHOLFiniteState (callEntryStateHOLFinite s lfCallee) lfBody) = (lfr, lfPost) := by
          rw [hlf_run] at hrem ⊢
          simp [fixClockHOLFinite, Nat.not_lt.mpr hrem]
        rw [hfix, hlf_run] at hdc
        dsimp only at hdc
        have hl_code : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "node_new_leaf")
            [.val (.word (wk + 1)), .val (.word (wl - 1)), .val (.word wv), .val (.word wvl)] =
            some (lfBody, lfCallee, lfRet) := by rwa [← hcode]
        obtain ⟨rfl, hp_nib⟩ := lookup_param_exact lookup_node_new_leaf hl_code
          [] "nib" .one [(ofString "nlen", .one), (ofString "vptr", .one), (ofString "vlen", .one)]
          [] (.val (.word (wk + 1))) [.val (.word (wl - 1)), .val (.word wv), .val (.word wvl)]
          rfl rfl rfl (by decide)
        obtain ⟨_, hp_nlen⟩ := lookup_param_exact lookup_node_new_leaf hl_code
          [(ofString "nib", .one)] "nlen" .one [(ofString "vptr", .one), (ofString "vlen", .one)]
          [.val (.word (wk + 1))] (.val (.word (wl - 1))) [.val (.word wv), .val (.word wvl)]
          rfl rfl rfl (by decide)
        obtain ⟨_, hp_vlen⟩ := lookup_param_exact lookup_node_new_leaf hl_code
          [(ofString "nib", .one), (ofString "nlen", .one), (ofString "vptr", .one)] "vlen" .one []
          [.val (.word (wk + 1)), .val (.word (wl - 1)), .val (.word wv)] (.val (.word wvl)) []
          rfl rfl rfl (by decide)
        have hsub_key : KeyIn s Nd (wk + 1).toNat (wl - 1).toNat := by
          have hwl1 : (wl - 1).toNat = wl.toNat - 1 := by
            rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; change 1 ≤ wl.toNat; omega)]; rfl
          have hwk_eq : BitVec.ofNat 64 wk.toNat + BitVec.ofNat 64 1 = wk + 1 := by simp
          rw [← hwk_eq, hwl1]
          exact keyIn_subslice hkey (by omega)
        have hent_req : KeyIn (callEntryStateHOLFinite s lfCallee) Nd
            (locN (callEntryStateHOLFinite s lfCallee) "nib")
            (locN (callEntryStateHOLFinite s lfCallee) "nlen") ∧
            locN (callEntryStateHOLFinite s lfCallee) "vlen" < 2 ^ 40 := by
          have h1 : locN (callEntryStateHOLFinite s lfCallee) "nib" = (wk + 1).toNat := by
            simp [locN, callEntryStateHOLFinite, hp_nib]
          have h2 : locN (callEntryStateHOLFinite s lfCallee) "nlen" = (wl - 1).toNat := by
            simp [locN, callEntryStateHOLFinite, hp_nlen]
          have h3 : locN (callEntryStateHOLFinite s lfCallee) "vlen" = wvl.toNat := by
            simp [locN, callEntryStateHOLFinite, hp_vlen]
          rw [h1, h2, h3]
          exact ⟨hsub_key, hvl_lt⟩
        rcases lfr with _ | lfr'
        · rw [hseq1, hdc] at hres; exact absurd hres not_resumes_error
        · cases lfr' with
          | returned lfrv =>
            dsimp only at hdc
            by_cases hsh : (shapeEqHOL (shapeOfHOLExact lfrv) .one && shapeEqHOL (shapeOfHOLExact lfrv) lfRet) = true
            · rw [if_pos hsh] at hdc
              obtain ⟨Nd1, hstep1, hret1⟩ := nodeStep_of_nodeFn nf_node_new_leaf s hcode ha hNd hlk_lf
                (by intro _ h; simp at h) hent_req (by rw [hlf_run]; exact Or.inl ⟨lfrv, rfl⟩)
              rw [hlf_run] at hstep1 hret1
              dsimp only at hstep1 hret1
              obtain ⟨wlf, rfl, hwlf_root⟩ := hret1 lfrv rfl
              set st1 := setVarHOLFinite (ofString lfn) (.val (.word wlf)) { lfPost with locals := s.locals }
              have hstep1' : NodeStep s st1 Nd Nd1 := hstep1.with_locals_clock _ _
              have hst1_AR : ArenaReady st1 := hstep1'.arena
              have hkey1 : KeyIn st1 Nd1 wk.toNat wl.toNat := hstep1'.keyIn ha hNd hkey
              have hst1_k : @evalHOLExact 64 F _ st1.toExact (fun a => Classical.propDecidable (st1.memaddrs a))
                  (.var .local (ofString kn)) = some (.val (.word wk)) := by
                simp [evalHOLExact, st1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hl_k, Ne.symm hne_lf_k]
              obtain ⟨idx, hidx_ev, hidx_lt⟩ := eval_loadByte_nibble hst1_AR.1 hkey1 hwl_pos hst1_k
              have hbr_in1 : wbr.toNat ∈ Nd1 := hstep1.sub wbr.toNat hbr_in
              have hbr_k1 : memW st1 wbr.toNat = 3 := (hstep1'.kinds wbr.toNat hbr_in).trans hbr_k
              obtain ⟨hdom_slot, hstep2, hmw3_2⟩ :=
                branch_store_child_step hst1_AR hstep1'.heap hbr_in1 hbr_k1 hidx_lt hwlf_root
              have hst1_br : st1.locals.lookup (ofString "br") = some (.val (.word wbr)) := by
                simp [st1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hl_br, Ne.symm hne_lf_br]
              have hst1_lf : st1.locals.lookup (ofString lfn) = some (.val (.word wlf)) := by
                simp [st1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
              set m_slot := Wave8Contracts.M26.updW st1.memory
                (wbr + BitVec.ofNat 64 32 + idx * BitVec.ofNat 64 8) wlf
              set st2 : PanSemStateFiniteExact 64 F := { st1 with memory := m_slot }
              have hstore_eval : evaluateHOLFiniteState st1
                  (.store (.op .add [.var .local (ofString "br"), .const 32,
                      .panop .mul [.loadByte (.var .local (ofString kn)), .const 8]])
                    (.var .local (ofString lfn))) = (none, st2) := by
                rw [evaluateHOLFiniteState_store]
                have hd : @evalHOLExact 64 F _ st1.toExact (fun a => Classical.propDecidable (st1.memaddrs a))
                    (.op .add [.var .local (ofString "br"), .const 32,
                      .panop .mul [.loadByte (.var .local (ofString kn)), .const 8]]) =
                    some (.val (.word (wbr + BitVec.ofNat 64 32 + idx * BitVec.ofNat 64 8))) := by
                  have hst1_kn : st1.locals.lookup (ofString kn) = some (.val (.word wk)) := hst1_k
                  obtain ⟨b, hb_mem, rfl⟩ : ∃ b : UInt8,
                      @panMemLoadByteHOL 64 _ st1.memory st1.memaddrs
                        (fun a => Classical.propDecidable (st1.memaddrs a)) st1.be wk = some b ∧
                      BitVec.ofNat 64 b.toNat = idx := by
                    simpa [evalHOLExact, hst1_kn] using hidx_ev
                  simp only [evalHOLExact, evalListHOLExact, hst1_br, hst1_kn, hb_mem,
                    panOpHOL, valueIsWord, valueWord, wordOpHOL, wordOp, List.all, List.map, Option.map,
                    Bool.and_self, ↓reduceIte, List.foldr, BitVec.add_zero]
                  congr 3
                  have hadd0 : ∀ u : BitVec 64, u + (0 : BitVec 64) = u := BitVec.add_zero
                  have hc32 : (32 : BitVec 64) = BitVec.ofNat 64 32 := rfl
                  have hc8 : (8 : BitVec 64) = BitVec.ofNat 64 8 := rfl
                  rw [hadd0, hc32, hc8]
                  exact (BitVec.add_assoc wbr (BitVec.ofNat 64 32) (BitVec.ofNat 64 b.toNat * BitVec.ofNat 64 8)).symm
                have he : @evalHOLExact 64 F _ st1.toExact (fun a => Classical.propDecidable (st1.memaddrs a))
                    (.var .local (ofString lfn)) = some (.val (.word wlf)) := hst1_lf
                rw [hd, he]
                simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL, hdom_slot, ↓reduceIte]
                rfl
              rw [hstore_eval] at hdc
              dsimp only at hdc
              set mid : PanSemStateFiniteExact 64 F :=
                { st2 with locals := HolFiniteMapExact.resVarEq st1.locals (ofString lfn, s.locals.lookup (ofString lfn)) }
              have hdc_eq : evaluateHOLFiniteState s dcProg = (none, mid) := hdc
              rw [hdc_eq] at hseq1
              dsimp only at hseq1
              rw [hseq1] at hres
              have hstep12 : NodeStep s mid Nd Nd1 :=
                (NodeStep.trans ha hstep1' hstep2).with_locals_clock _ mid.clock
              have hmid_code : mid.code = originalRuntimeCode := hstep12.arena.1.code
              have hmid_loc : ∀ x : MlS, x ≠ ofString lfn → mid.locals.lookup x = s.locals.lookup x := by
                intro x hx
                dsimp only [mid]
                rw [resVarEq_lookup_ne _ _ _ _ hx]
                simp [st1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hx]
              exact ⟨mid, Nd1, hseq1, hres, hmid_code, hmid_loc, hstep12, hbr_in1, hmw3_2⟩
            · rw [if_neg hsh] at hdc; rw [hseq1, hdc] at hres; exact absurd hres not_resumes_error
          | exception eid ev =>
            dsimp only at hdc
            rw [hseq1, hdc] at hres
            rcases hres with ⟨_, h⟩ | ⟨eid', ev', h, hne_tr⟩
            · simp at h
            · injection h with h1; injection h1 with he1 he2; subst he1 he2
              exact absurd (congrArg Prod.fst hlf_run)
                (node_new_leaf_body_no_nonTrap_exn (callEntryStateHOLFinite s lfCallee) hcode eid ev hne_tr)
          | _ =>
            rw [hseq1, hdc] at hres
            rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h

/-- Specification of `_create_branch_from_two_leaves` body:
under `ArenaReady s` and `KeyIn` / `< 2^40` for `(k1, l1, vl1)` and `(k2, l2, vl2)`, returns
a fresh branch node `br` in `Nd'`. -/
private theorem create_branch_from_two_leaves_spec {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hcode : s.code = originalRuntimeCode)
    (hAR : ArenaReady s)
    {wk1 wl1 wv1 wvl1 wk2 wl2 wv2 wvl2 : BitVec 64}
    (hk1 : s.locals.lookup (ofString "k1") = some (.val (.word wk1)))
    (hl1 : s.locals.lookup (ofString "l1") = some (.val (.word wl1)))
    (hv1 : s.locals.lookup (ofString "v1") = some (.val (.word wv1)))
    (hvl1 : s.locals.lookup (ofString "vl1") = some (.val (.word wvl1)))
    (hk2 : s.locals.lookup (ofString "k2") = some (.val (.word wk2)))
    (hl2 : s.locals.lookup (ofString "l2") = some (.val (.word wl2)))
    (hv2 : s.locals.lookup (ofString "v2") = some (.val (.word wv2)))
    (hvl2 : s.locals.lookup (ofString "vl2") = some (.val (.word wvl2)))
    (hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn__create_branch_from_two_leaves)).1) :
    let r := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn__create_branch_from_two_leaves)).1
    let post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn__create_branch_from_two_leaves)).2
    ∀ Nd, NodeHeap s Nd →
      KeyIn s Nd wk1.toNat wl1.toNat → wvl1.toNat < 2 ^ 40 →
      KeyIn s Nd wk2.toNat wl2.toNat → wvl2.toNat < 2 ^ 40 →
      ∃ (Nd' : List Nat) (wbr : BitVec 64),
        r = some (.returned (.val (.word wbr))) ∧
        wbr.toNat ∈ Nd' ∧
        NodeStep s post Nd Nd' := by
  intro r post Nd hNd hKey1 hvl1_lt hKey2 hvl2_lt
  have hbody : sourceFnBody Guest.Software.guestFn__create_branch_from_two_leaves =
      .decCall (ofString "br") .one (ofString "node_new_branch") []
        (.seq
          (.ite (.cmp .equal (.var .local (ofString "l1")) (.const 0))
            (.seq
              (.store (.op .add [.var .local (ofString "br"), .const 160]) (.var .local (ofString "v1")))
              (.store (.op .add [.var .local (ofString "br"), .const 168]) (.var .local (ofString "vl1"))))
            (.decCall (ofString "lf1") .one (ofString "node_new_leaf")
              [.op .add [.var .local (ofString "k1"), .const 1],
               .op .sub [.var .local (ofString "l1"), .const 1],
               .var .local (ofString "v1"),
               .var .local (ofString "vl1")]
              (.store (.op .add [.var .local (ofString "br"), .const 32,
                  .panop .mul [.loadByte (.var .local (ofString "k1")), .const 8]])
                (.var .local (ofString "lf1")))))
          (.seq
            (.ite (.cmp .equal (.var .local (ofString "l2")) (.const 0))
              (.seq
                (.store (.op .add [.var .local (ofString "br"), .const 160]) (.var .local (ofString "v2")))
                (.store (.op .add [.var .local (ofString "br"), .const 168]) (.var .local (ofString "vl2"))))
              (.decCall (ofString "lf2") .one (ofString "node_new_leaf")
                [.op .add [.var .local (ofString "k2"), .const 1],
                 .op .sub [.var .local (ofString "l2"), .const 1],
                 .var .local (ofString "v2"),
                 .var .local (ofString "vl2")]
                (.store (.op .add [.var .local (ofString "br"), .const 32,
                    .panop .mul [.loadByte (.var .local (ofString "k2")), .const 8]])
                  (.var .local (ofString "lf2")))))
            (.return (.var .local (ofString "br"))))) := rfl
  have hres' : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn__create_branch_from_two_leaves)).1 := hres
  rw [hbody] at hres'
  obtain ⟨bvals, bbody, bcallee, bret, _, hbargs, hbl, hbexn | ⟨brv, bpost, hbrun, _, hbcont_res, hbr_eq, hbp_eq⟩⟩ :=
    decCall_resumes_inv hres'
  · obtain ⟨eid, ev, hb_exn, hne_tr, _⟩ := hbexn
    have hsame := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "node_new_branch")
      _ _ _ _ _ bvals bcallee (by rw [hcode]; exact lookup_node_new_branch) hbl
    subst hsame
    have hb_spec := node_new_branch_spec (callEntryStateHOLFinite s bcallee) hcode
      (localsFree_arenaReady s _ _ hAR) (by rw [hb_exn]; exact Or.inr ⟨eid, ev, rfl, hne_tr⟩)
    obtain ⟨_, _, _, wbr, hret_br, _⟩ := hb_spec
    rw [hb_exn] at hret_br; cases hret_br
  · have hsame := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "node_new_branch")
      _ _ _ _ _ bvals bcallee (by rw [hcode]; exact lookup_node_new_branch) hbl
    subst hsame
    have hb_spec := node_new_branch_spec (callEntryStateHOLFinite s bcallee) hcode
      (localsFree_arenaReady s _ _ hAR) (by rw [hbrun]; exact Or.inl ⟨brv, rfl⟩)
    obtain ⟨_, _, _, wbr, hret_br, _, _, _, hmw0_br, _, _, _, hstep_br_all⟩ := hb_spec
    rw [hbrun] at hret_br hmw0_br hstep_br_all
    injection hret_br with h1; injection h1 with hbrv_eq; subst hbrv_eq
    have hstep0_raw : NodeStep s bpost Nd (wbr.toNat :: Nd) :=
      NodeStep.from_locals_clock (hstep_br_all Nd hNd)
    set s0 := setVarHOLFinite (ofString "br") (.val (.word wbr)) { bpost with locals := s.locals }
    have hstep0 : NodeStep s s0 Nd (wbr.toNat :: Nd) := hstep0_raw.with_locals_clock _ _
    have hs0_code : s0.code = originalRuntimeCode := hstep0.arena.1.code
    have hs0_br : s0.locals.lookup (ofString "br") = some (.val (.word wbr)) := by
      simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hl_s0 : ∀ x : MlS, x ≠ ofString "br" → s0.locals.lookup x = s.locals.lookup x := by
      intro x hne
      simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hne]
    -- Arm 1 (`k1, l1, v1, vl1, lf1`)
    obtain ⟨s1, Nd1, hseq1_eq, hs1_res, hs1_code, hs1_loc, hstep1, hbr_in1, hbr_k1⟩ :=
      cbtl_arm_step hs0_code hstep0.arena hstep0.heap (List.mem_cons_self ..) hmw0_br
        (hstep0.keyIn hAR hNd hKey1) hvl1_lt
        hs0_br
        (by rw [hl_s0 _ (by decide)]; exact hk1)
        (by rw [hl_s0 _ (by decide)]; exact hl1)
        (by rw [hl_s0 _ (by decide)]; exact hv1)
        (by rw [hl_s0 _ (by decide)]; exact hvl1)
        (by decide) (by decide) hbcont_res
    have hstep01 : NodeStep s s1 Nd Nd1 := NodeStep.trans hAR hstep0 hstep1
    -- Arm 2 (`k2, l2, v2, vl2, lf2`)
    obtain ⟨s2, Nd2, hseq2_eq, hs2_res, hs2_code, hs2_loc, hstep2, hbr_in2, _⟩ :=
      cbtl_arm_step hs1_code hstep01.arena hstep01.heap hbr_in1 hbr_k1
        (hstep01.keyIn hAR hNd hKey2) hvl2_lt
        (by rw [hs1_loc _ (by decide)]; exact hs0_br)
        (by rw [hs1_loc _ (by decide), hl_s0 _ (by decide)]; exact hk2)
        (by rw [hs1_loc _ (by decide), hl_s0 _ (by decide)]; exact hl2)
        (by rw [hs1_loc _ (by decide), hl_s0 _ (by decide)]; exact hv2)
        (by rw [hs1_loc _ (by decide), hl_s0 _ (by decide)]; exact hvl2)
        (by decide) (by decide) hs1_res
    have hstep02 : NodeStep s s2 Nd Nd2 := NodeStep.trans hAR hstep01 hstep2
    have hs2_br : s2.locals.lookup (ofString "br") = some (.val (.word wbr)) := by
      rw [hs2_loc _ (by decide), hs1_loc _ (by decide)]; exact hs0_br
    have hret_eval : evaluateHOLFiniteState s2 (.return (.var .local (ofString "br"))) =
        (some (.returned (.val (.word wbr))), emptyLocalsHOLFinite s2) := by
      simp [evaluateHOLFiniteState_return, evalHOLExact, hs2_br, shapeOfHOLExact, sizeOfShapeWithContextHOL]
    have hr_final : r = some (.returned (.val (.word wbr))) := by
      change (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn__create_branch_from_two_leaves)).1 = _
      rw [hbody, hbr_eq, hseq1_eq, hseq2_eq, hret_eval]
    have hpost_eq : post = { emptyLocalsHOLFinite s2 with
        locals := HolFiniteMapExact.resVarEq (emptyLocalsHOLFinite s2).locals (ofString "br", s.locals.lookup (ofString "br")) } := by
      change (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn__create_branch_from_two_leaves)).2 = _
      rw [hbody, hbp_eq, hseq1_eq, hseq2_eq, hret_eval]
    refine ⟨Nd2, wbr, hr_final, hbr_in2, ?_⟩
    rw [hpost_eq]
    exact (hstep02.with_locals_clock _ _).with_locals_clock _ _

/-- `_insert_into_leaf` (AST line 10532): typed nodes in, typed nodes out (MPT tier);
requirement: `NodeKind s Nd "node" 1 ∧ KeyIn s Nd (locN s "rk") (locN s "rl") ∧ locN s "vlen" < 2 ^ 40`. -/
theorem «nf__insert_into_leaf» :
    NodeFn ["node"]
    (fun s Nd =>
      NodeKind s Nd "node" 1 ∧ KeyIn s Nd (locN s "rk") (locN s "rl") ∧ locN s "vlen" < 2 ^ 40)
    (ofString "_insert_into_leaf") := by
  refine ⟨_, _, _, lookup__insert_into_leaf, ?_⟩
  intro F s hcode hP ⟨callVals, hcallL⟩ _hnt hres
  have hAR : ArenaReady s := hP.1
  obtain ⟨Nd_wit, hNd_wit, _, hnk_wit, hkrk_wit, hvlen_wit⟩ := hP.2
  obtain ⟨wnode, hlk_node, hloc_node⟩ := lookup_param_word lookup__insert_into_leaf hcallL
    [] "node" [(ofString "rk", .one), (ofString "rl", .one), (ofString "vptr", .one), (ofString "vlen", .one)]
    rfl (by decide)
  obtain ⟨wrk, hlk_rk, hloc_rk⟩ := lookup_param_word lookup__insert_into_leaf hcallL
    [(ofString "node", .one)] "rk" [(ofString "rl", .one), (ofString "vptr", .one), (ofString "vlen", .one)]
    rfl (by decide)
  obtain ⟨wrl, hlk_rl, hloc_rl⟩ := lookup_param_word lookup__insert_into_leaf hcallL
    [(ofString "node", .one), (ofString "rk", .one)] "rl" [(ofString "vptr", .one), (ofString "vlen", .one)]
    rfl (by decide)
  obtain ⟨wvptr, hlk_vptr, hloc_vptr⟩ := lookup_param_word lookup__insert_into_leaf hcallL
    [(ofString "node", .one), (ofString "rk", .one), (ofString "rl", .one)] "vptr" [(ofString "vlen", .one)]
    rfl (by decide)
  obtain ⟨wvlen, hlk_vlen, hloc_vlen⟩ := lookup_param_word lookup__insert_into_leaf hcallL
    [(ofString "node", .one), (ofString "rk", .one), (ofString "rl", .one), (ofString "vptr", .one)] "vlen" []
    rfl (by decide)
  have hwnode_in_wit : wnode.toNat ∈ Nd_wit := by rw [← hloc_node s rfl]; exact hnk_wit.1
  have hwnode_k1 : memW s wnode.toNat = 1 := by rw [← hloc_node s rfl]; exact hnk_wit.2
  have hsz_node : nodeSize (memW s wnode.toNat) = 64 := by simp [nodeSize, hwnode_k1]
  have hp_wit := hNd_wit.1 wnode.toNat hwnode_in_wit
  have hhl_lt : heapLimit < 2 ^ 64 := by decide
  have hnode_lt : wnode.toNat + 64 ≤ heapLimit := by
    have := hp_wit.2.2.1.2; dsimp [nodeIvl] at this; omega
  have hnode_add : ∀ k : Nat, k ≤ 56 → wnode + BitVec.ofNat 64 k = BitVec.ofNat 64 (wnode.toNat + k) ∧
      (wnode + BitVec.ofNat 64 k).toNat = wnode.toNat + k := by
    intro k hk
    have hlt : wnode.toNat + k < 2 ^ 64 := by omega
    have heq : wnode + BitVec.ofNat 64 k = BitVec.ofNat 64 (wnode.toNat + k) := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    exact ⟨heq, by rw [heq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]⟩
  have hload_node_off : ∀ (st : PanSemStateFiniteExact 64 F) (k : Nat),
      st.memory = s.memory → st.memaddrs = s.memaddrs →
      st.locals.lookup (ofString "node") = some (.val (.word wnode)) →
      k < 64 → k % 8 = 0 →
      @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a))
        (.load .one (.op .add [.var .local (ofString "node"), .const (BitVec.ofNat 64 k)])) =
        some (.val (.word (BitVec.ofNat 64 (memW s (wnode.toNat + k))))) := by
    intro st k hmem hma hnd hk hk8
    obtain ⟨w_at, hdom_at, hm_at⟩ := hp_wit.2.2.2.1.2.2 (k / 8) (by dsimp [nodeIvl]; omega)
    dsimp [nodeIvl] at hdom_at hm_at
    have hmul : wnode.toNat + 8 * (k / 8) = wnode.toNat + k := by omega
    rw [hmul] at hdom_at hm_at
    have hdom_st : st.memaddrs (wnode + BitVec.ofNat 64 k) := by
      rw [hma, (hnode_add k (by omega)).1]; exact hdom_at
    have hm_st : st.memory (wnode + BitVec.ofNat 64 k) = .word w_at := by
      rw [hmem, (hnode_add k (by omega)).1]; exact hm_at
    have hmw_eq : BitVec.ofNat 64 (memW s (wnode.toNat + k)) = w_at := by
      unfold memW; rw [hm_at]; simp
    simp [evalHOLExact, evalListHOLExact, hnd, valueIsWord, valueWord, wordOpHOL, wordOp,
      isWfShapeExactHOL, memLoadHOLExact, hdom_st, hm_st, hmw_eq]
  -- Evaluate `dec ek := load(node + 32); dec el := load(node + 40); ...`
  set wek : BitVec 64 := BitVec.ofNat 64 (memW s (wnode.toNat + 32))
  set wel : BitVec 64 := BitVec.ofNat 64 (memW s (wnode.toNat + 40))
  have hwek_nat : wek.toNat = memW s (wnode.toNat + 32) := by
    dsimp [wek]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold memW; rcases s.memory _ with ⟨w⟩; exact w.isLt)]
  have hwel_nat : wel.toNat = memW s (wnode.toNat + 40) := by
    dsimp [wel]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold memW; rcases s.memory _ with ⟨w⟩; exact w.isLt)]
  set res := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn__insert_into_leaf)).1
  set post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn__insert_into_leaf)).2
  -- Prove a unified helper that for ANY `Nd` satisfying the entry requirement, produces `Nd'`, `NodeStep`, and `RootIn`!
  suffices hmain : ∀ Nd, NodeHeap s Nd → NodeKind s Nd "node" 1 →
      KeyIn s Nd (locN s "rk") (locN s "rl") → locN s "vlen" < 2 ^ 40 →
      ∃ Nd', NodeStep s post Nd Nd' ∧
        ∀ v, res = some (.returned v) → ∃ w : BitVec 64, v = .val (.word w) ∧ RootIn Nd' w.toNat by
    obtain ⟨Nd0', hns0, _⟩ := hmain Nd_wit hNd_wit hnk_wit hkrk_wit hvlen_wit
    refine ⟨hns0.arena, hns0.hp_le, hns0.sp_le, ?_⟩
    intro Nd hNd _ ⟨hnk, hkrk, hvlen⟩
    obtain ⟨Nd', hns, hret⟩ := hmain Nd hNd hnk hkrk hvlen
    exact ⟨Nd', hns.heap, hns.sub, hns.kinds, hns.fresh, hns.frame, hns.globals, hret⟩
  intro Nd hNd hnk hkrk hvlen_lt
  have hnode_in : wnode.toNat ∈ Nd := by rw [← hloc_node s rfl]; exact hnk.1
  have hnode_k1 : memW s wnode.toNat = 1 := by rw [← hloc_node s rfl]; exact hnk.2
  have hp_nd := hNd.1 wnode.toNat hnode_in
  have hkey_ek : KeyIn s Nd wek.toNat wel.toNat := by
    rw [hwek_nat, hwel_nat]
    exact hp_nd.2.2.2.2.2.2.1 (Or.inl hnode_k1)
  have hkey_rk : KeyIn s Nd wrk.toNat wrl.toNat := by
    rwa [hloc_rk s rfl, hloc_rl s rfl] at hkrk
  have hwvlen_lt : wvlen.toNat < 2 ^ 40 := by
    rwa [hloc_vlen s rfl] at hvlen_lt
  have hbody : sourceFnBody Guest.Software.guestFn__insert_into_leaf =
      .dec (ofString "ek") .one (.load .one (.op .add [.var .local (ofString "node"), .const (BitVec.ofNat 64 32)]))
        (.dec (ofString "el") .one (.load .one (.op .add [.var .local (ofString "node"), .const (BitVec.ofNat 64 40)]))
          (.seq
            (.ite (.cmp .equal (.var .local (ofString "el")) (.var .local (ofString "rl")))
              (.decCall (ofString "eq") .one (ofString "memeq")
                [.var .local (ofString "ek"), .var .local (ofString "rk"), .var .local (ofString "el")]
                (.ite (.cmp .notEqual (.var .local (ofString "eq")) (.const (BitVec.ofNat 64 0)))
                  (.seq
                    (.store (.op .add [.var .local (ofString "node"), .const (BitVec.ofNat 64 48)])
                      (.var .local (ofString "vptr")))
                    (.seq
                      (.store (.op .add [.var .local (ofString "node"), .const (BitVec.ofNat 64 56)])
                        (.var .local (ofString "vlen")))
                      (.return (.var .local (ofString "node")))))
                  .skip))
              .skip)
            (.decCall (ofString "pl") .one (ofString "common_prefix_length")
              [.var .local (ofString "ek"), .var .local (ofString "el"),
               .var .local (ofString "rk"), .var .local (ofString "rl")]
              (.decCall (ofString "br") .one (ofString "_create_branch_from_two_leaves")
                [.op .add [.var .local (ofString "ek"), .var .local (ofString "pl")],
                 .op .sub [.var .local (ofString "el"), .var .local (ofString "pl")],
                 .load .one (.op .add [.var .local (ofString "node"), .const (BitVec.ofNat 64 48)]),
                 .load .one (.op .add [.var .local (ofString "node"), .const (BitVec.ofNat 64 56)]),
                 .op .add [.var .local (ofString "rk"), .var .local (ofString "pl")],
                 .op .sub [.var .local (ofString "rl"), .var .local (ofString "pl")],
                 .var .local (ofString "vptr"),
                 .var .local (ofString "vlen")]
                (.seq
                  (.ite (.cmp .lower (.const (BitVec.ofNat 64 0)) (.var .local (ofString "pl")))
                    (.call none (ofString "node_new_ext")
                      [.var .local (ofString "ek"), .var .local (ofString "pl"), .var .local (ofString "br")])
                    .skip)
                  (.return (.var .local (ofString "br")))))))) := rfl
  -- Step through `dec ek` and `dec el`
  set s_ek := setVarHOLFinite (ofString "ek") (.val (.word wek)) s
  set s_el := setVarHOLFinite (ofString "el") (.val (.word wel)) s_ek
  have hsek_node : s_ek.locals.lookup (ofString "node") = some (.val (.word wnode)) := by
    simp [s_ek, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlk_node,
      show ofString "ek" ≠ ofString "node" by decide]
  have hsel_node : s_el.locals.lookup (ofString "node") = some (.val (.word wnode)) := by
    simp [s_el, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsek_node,
      show ofString "el" ≠ ofString "node" by decide]
  have hsel_ek : s_el.locals.lookup (ofString "ek") = some (.val (.word wek)) := by
    simp [s_el, s_ek, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "el" ≠ ofString "ek" by decide]
  have hsel_el : s_el.locals.lookup (ofString "el") = some (.val (.word wel)) := by
    simp [s_el, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hsel_rk : s_el.locals.lookup (ofString "rk") = some (.val (.word wrk)) := by
    simp [s_el, s_ek, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlk_rk,
      show ofString "el" ≠ ofString "rk" by decide, show ofString "ek" ≠ ofString "rk" by decide]
  have hsel_rl : s_el.locals.lookup (ofString "rl") = some (.val (.word wrl)) := by
    simp [s_el, s_ek, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlk_rl,
      show ofString "el" ≠ ofString "rl" by decide, show ofString "ek" ≠ ofString "rl" by decide]
  have hsel_vptr : s_el.locals.lookup (ofString "vptr") = some (.val (.word wvptr)) := by
    simp [s_el, s_ek, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlk_vptr,
      show ofString "el" ≠ ofString "vptr" by decide, show ofString "ek" ≠ ofString "vptr" by decide]
  have hsel_vlen : s_el.locals.lookup (ofString "vlen") = some (.val (.word wvlen)) := by
    simp [s_el, s_ek, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlk_vlen,
      show ofString "el" ≠ ofString "vlen" by decide, show ofString "ek" ≠ ofString "vlen" by decide]
  set body_core : ProgHOL 64 :=
    .seq
      (.ite (.cmp .equal (.var .local (ofString "el")) (.var .local (ofString "rl")))
        (.decCall (ofString "eq") .one (ofString "memeq")
          [.var .local (ofString "ek"), .var .local (ofString "rk"), .var .local (ofString "el")]
          (.ite (.cmp .notEqual (.var .local (ofString "eq")) (.const (BitVec.ofNat 64 0)))
            (.seq
              (.store (.op .add [.var .local (ofString "node"), .const (BitVec.ofNat 64 48)])
                (.var .local (ofString "vptr")))
              (.seq
                (.store (.op .add [.var .local (ofString "node"), .const (BitVec.ofNat 64 56)])
                  (.var .local (ofString "vlen")))
                (.return (.var .local (ofString "node")))))
            .skip))
        .skip)
      (.decCall (ofString "pl") .one (ofString "common_prefix_length")
        [.var .local (ofString "ek"), .var .local (ofString "el"),
         .var .local (ofString "rk"), .var .local (ofString "rl")]
        (.decCall (ofString "br") .one (ofString "_create_branch_from_two_leaves")
          [.op .add [.var .local (ofString "ek"), .var .local (ofString "pl")],
           .op .sub [.var .local (ofString "el"), .var .local (ofString "pl")],
           .load .one (.op .add [.var .local (ofString "node"), .const (BitVec.ofNat 64 48)]),
           .load .one (.op .add [.var .local (ofString "node"), .const (BitVec.ofNat 64 56)]),
           .op .add [.var .local (ofString "rk"), .var .local (ofString "pl")],
           .op .sub [.var .local (ofString "rl"), .var .local (ofString "pl")],
           .var .local (ofString "vptr"),
           .var .local (ofString "vlen")]
          (.seq
            (.ite (.cmp .lower (.const (BitVec.ofNat 64 0)) (.var .local (ofString "pl")))
              (.call none (ofString "node_new_ext")
                [.var .local (ofString "ek"), .var .local (ofString "pl"), .var .local (ofString "br")])
              .skip)
            (.return (.var .local (ofString "br"))))))
  have hdec_unfold : res = (evaluateHOLFiniteState s_el body_core).1 ∧
      post = { (evaluateHOLFiniteState s_el body_core).2 with
        locals := HolFiniteMapExact.resVarEq
          (HolFiniteMapExact.resVarEq (evaluateHOLFiniteState s_el body_core).2.locals
            (ofString "el", s_ek.locals.lookup (ofString "el")))
          (ofString "ek", s.locals.lookup (ofString "ek")) } := by
    have he1 := hload_node_off s 32 rfl rfl hlk_node (by decide) (by decide)
    have he2 := hload_node_off s_ek 40 rfl rfl hsek_node (by decide) (by decide)
    have hsh1 : shapeEqHOL .one (shapeOfHOLExact (.val (.word wek))) = true := by simp [shapeEqHOL, shapeOfHOLExact]
    have hsh2 : shapeEqHOL .one (shapeOfHOLExact (.val (.word wel))) = true := by simp [shapeEqHOL, shapeOfHOLExact]
    have hdec2 : evaluateHOLFiniteState s_ek
        (.dec (ofString "el") .one (.load .one (.op .add [.var .local (ofString "node"), .const (BitVec.ofNat 64 40)]))
          body_core) =
        ((evaluateHOLFiniteState s_el body_core).1,
         { (evaluateHOLFiniteState s_el body_core).2 with
           locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState s_el body_core).2.locals
             (ofString "el", s_ek.locals.lookup (ofString "el")) }) := by
      rw [evaluateHOLFiniteState_dec_total]
      dsimp only
      rw [he2]
      dsimp only
      rw [if_pos hsh2]
    have hdec1 : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn__insert_into_leaf) =
        ((evaluateHOLFiniteState s_el body_core).1,
         { (evaluateHOLFiniteState s_el body_core).2 with
           locals := HolFiniteMapExact.resVarEq
             (HolFiniteMapExact.resVarEq (evaluateHOLFiniteState s_el body_core).2.locals
               (ofString "el", s_ek.locals.lookup (ofString "el")))
             (ofString "ek", s.locals.lookup (ofString "ek")) }) := by
      rw [hbody, evaluateHOLFiniteState_dec_total]
      dsimp only
      rw [he1]
      dsimp only
      rw [if_pos hsh1]
      dsimp only [s_ek] at hdec2 ⊢
      rw [hdec2]
    exact ⟨by dsimp only [res]; rw [hdec1], by dsimp only [post]; rw [hdec1]⟩
  -- Analyze the first `ite (el == rl)` on `s_el`: either it returns `wnode` after updating `+48/+56`, or it falls through (`none`) to a state `s_mid` agreeing with `s` on everything except `locals` and `clock`!
  set tail_prog : ProgHOL 64 :=
    .decCall (ofString "pl") .one (ofString "common_prefix_length")
      [.var .local (ofString "ek"), .var .local (ofString "el"),
       .var .local (ofString "rk"), .var .local (ofString "rl")]
      (.decCall (ofString "br") .one (ofString "_create_branch_from_two_leaves")
        [.op .add [.var .local (ofString "ek"), .var .local (ofString "pl")],
         .op .sub [.var .local (ofString "el"), .var .local (ofString "pl")],
         .load .one (.op .add [.var .local (ofString "node"), .const (BitVec.ofNat 64 48)]),
         .load .one (.op .add [.var .local (ofString "node"), .const (BitVec.ofNat 64 56)]),
         .op .add [.var .local (ofString "rk"), .var .local (ofString "pl")],
         .op .sub [.var .local (ofString "rl"), .var .local (ofString "pl")],
         .var .local (ofString "vptr"),
         .var .local (ofString "vlen")]
        (.seq
          (.ite (.cmp .lower (.const (BitVec.ofNat 64 0)) (.var .local (ofString "pl")))
            (.call none (ofString "node_new_ext")
              [.var .local (ofString "ek"), .var .local (ofString "pl"), .var .local (ofString "br")])
            .skip)
          (.return (.var .local (ofString "br")))))
  set head_ite : ProgHOL 64 :=
    .ite (.cmp .equal (.var .local (ofString "el")) (.var .local (ofString "rl")))
      (.decCall (ofString "eq") .one (ofString "memeq")
        [.var .local (ofString "ek"), .var .local (ofString "rk"), .var .local (ofString "el")]
        (.ite (.cmp .notEqual (.var .local (ofString "eq")) (.const (BitVec.ofNat 64 0)))
          (.seq
            (.store (.op .add [.var .local (ofString "node"), .const (BitVec.ofNat 64 48)])
              (.var .local (ofString "vptr")))
            (.seq
              (.store (.op .add [.var .local (ofString "node"), .const (BitVec.ofNat 64 56)])
                (.var .local (ofString "vlen")))
              (.return (.var .local (ofString "node")))))
          .skip))
      .skip
  have hres_core : Resumes (evaluateHOLFiniteState s_el (.seq head_ite tail_prog)).1 := by
    rw [← hdec_unfold.1]; exact hres
  have hhead_cases :
      ((evaluateHOLFiniteState s_el head_ite).1 = some (.returned (.val (.word wnode))) ∧
       NodeStep s (evaluateHOLFiniteState s_el head_ite).2 Nd Nd) ∨
      (∃ s_mid : PanSemStateFiniteExact 64 F,
        evaluateHOLFiniteState s_el head_ite = (none, s_mid) ∧
        s_mid = { s with locals := s_mid.locals, clock := s_mid.clock } ∧
        ∀ x : MlS, x ≠ ofString "eq" → s_mid.locals.lookup x = s_el.locals.lookup x) := by
    have hc_el_rl : @evalHOLExact 64 F _ s_el.toExact (fun a => Classical.propDecidable (s_el.memaddrs a))
        (.cmp .equal (.var .local (ofString "el")) (.var .local (ofString "rl"))) =
        some (.val (.word (if wel = wrl then 1 else 0))) := by
      simp [evalHOLExact, hsel_el, hsel_rl, Compiler.Encoders.Asm.wordCmpHOL]
    by_cases heq_len : wel = wrl
    · have hite_t : evaluateHOLFiniteState s_el head_ite =
          evaluateHOLFiniteState s_el
            (.decCall (ofString "eq") .one (ofString "memeq")
              [.var .local (ofString "ek"), .var .local (ofString "rk"), .var .local (ofString "el")]
              (.ite (.cmp .notEqual (.var .local (ofString "eq")) (.const (BitVec.ofNat 64 0)))
                (.seq
                  (.store (.op .add [.var .local (ofString "node"), .const (BitVec.ofNat 64 48)])
                    (.var .local (ofString "vptr")))
                  (.seq
                    (.store (.op .add [.var .local (ofString "node"), .const (BitVec.ofNat 64 56)])
                      (.var .local (ofString "vlen")))
                    (.return (.var .local (ofString "node")))))
                .skip)) := by
        dsimp only [head_ite]
        rw [evaluateHOLFiniteState_ite, hc_el_rl, if_pos heq_len]; simp
      have hdc_eq := evaluateHOLFiniteState_decCall_total s_el (ofString "eq") .one (ofString "memeq")
        [.var .local (ofString "ek"), .var .local (ofString "rk"), .var .local (ofString "el")]
        (.ite (.cmp .notEqual (.var .local (ofString "eq")) (.const (BitVec.ofNat 64 0)))
          (.seq
            (.store (.op .add [.var .local (ofString "node"), .const (BitVec.ofNat 64 48)])
              (.var .local (ofString "vptr")))
            (.seq
              (.store (.op .add [.var .local (ofString "node"), .const (BitVec.ofNat 64 56)])
                (.var .local (ofString "vlen")))
              (.return (.var .local (ofString "node")))))
          .skip)
      have hargs_me : evalListHOLFinite s_el (h := fun a => Classical.propDecidable (s_el.memaddrs a))
          [.var .local (ofString "ek"), .var .local (ofString "rk"), .var .local (ofString "el")] =
          some [.val (.word wek), .val (.word wrk), .val (.word wel)] := by
        rw [evalListHOLFinite_eq_toExact]
        simp [evalListHOLExact, evalHOLExact, hsel_ek, hsel_rk, hsel_el]
      have hlk_me := pan_three_word_lookup s_el.code.lookup (ofString "memeq")
        (ofString "a") (ofString "b") (ofString "n")
        (sourceFnBody Guest.Software.guestFn_memeq) wek wrk wel
        (by decide) (by decide) (by decide) (by change s.code.lookup _ = _; rw [hcode]; exact lookup_memeq)
      rw [hargs_me] at hdc_eq; dsimp only at hdc_eq
      rw [hlk_me] at hdc_eq; dsimp only at hdc_eq
      by_cases hcz : s_el.clock = 0
      · rw [if_pos hcz] at hdc_eq
        rw [evaluateHOLFiniteState_seq_line780, hite_t, hdc_eq] at hres_core
        rcases hres_core with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
      · rw [if_neg hcz] at hdc_eq
        let mentry := callEntryStateHOLFinite s_el
          (((HolFiniteMapExact.empty.update (ofString "a", .val (.word wek))).update
            (ofString "b", .val (.word wrk))).update (ofString "n", .val (.word wel)))
        have hrem := evaluateHOLFiniteState_clock_le mentry (sourceFnBody Guest.Software.guestFn_memeq)
        rcases hmrun : evaluateHOLFiniteState mentry (sourceFnBody Guest.Software.guestFn_memeq) with ⟨mr, mpost⟩
        have hfix : fixClockHOLFinite mentry (evaluateHOLFiniteState mentry (sourceFnBody Guest.Software.guestFn_memeq)) =
            (mr, mpost) := by
          rw [hmrun] at hrem ⊢; simp [fixClockHOLFinite, Nat.not_lt.mpr hrem]
        rw [hfix, hmrun] at hdc_eq
        dsimp only at hdc_eq
        rcases mr with _ | mr'
        · rw [evaluateHOLFiniteState_seq_line780, hite_t, hdc_eq] at hres_core
          exact absurd hres_core not_resumes_error
        · cases mr' with
          | returned mrv =>
            dsimp only at hdc_eq
            by_cases hsh : (shapeEqHOL (shapeOfHOLExact mrv) .one && shapeEqHOL (shapeOfHOLExact mrv) .one) = true
            · rw [if_pos hsh] at hdc_eq
              rcases mrv with ⟨⟨weq⟩⟩ | _ | _ <;> try (simp [shapeOfHOLExact, shapeEqHOL] at hsh)
              -- `ro_memeq` gives `mpost = { mentry with locals := mpost.locals, clock := mpost.clock }`!
              have hro_spec : ReadOnlyFn (ofString "memeq") := by
                rcases Wave8Contracts.M15.ro_memeq with ⟨ps, bd, rt, hlk_ro, hrun_ro⟩
                exact ⟨ps, bd, rt, hlk_ro, fun st hc hg hex hnt hr => hrun_ro st hc hg hex hnt hr⟩
              have hro_me := FunSpec.at_lookup hro_spec s_el hcode
                [.val (.word wek), .val (.word wrk), .val (.word wel)]
                (sourceFnBody Guest.Software.guestFn_memeq) _ .one hlk_me
                (guestInv_callEntry s_el _ (guestInv_setVar _ _ _ (guestInv_setVar _ _ _ hAR.1)))
                (by rw [hmrun]; simp) (by rw [hmrun]; exact Or.inl ⟨.val (.word weq), rfl⟩)
              rw [hmrun] at hro_me
              dsimp only at hro_me
              set s_eq := setVarHOLFinite (ofString "eq") (.val (.word weq)) { mpost with locals := s_el.locals }
              have hseq_frame : s_eq = { s with locals := s_eq.locals, clock := s_eq.clock } := by
                dsimp only [s_eq, setVarHOLFinite]
                rw [hro_me]
                cases s; rfl
              have hc_eq0 : @evalHOLExact 64 F _ s_eq.toExact (fun a => Classical.propDecidable (s_eq.memaddrs a))
                  (.cmp .notEqual (.var .local (ofString "eq")) (.const (BitVec.ofNat 64 0))) =
                  some (.val (.word (if weq ≠ 0 then 1 else 0))) := by
                have heq_lk : s_eq.locals.lookup (ofString "eq") = some (.val (.word weq)) := by
                  simp [s_eq, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                simp [evalHOLExact, heq_lk, Compiler.Encoders.Asm.wordCmpHOL]
              by_cases hweq0 : weq = 0
              · -- `eq == 0`: `skip`, falls through!
                subst hweq0
                have hite_in : evaluateHOLFiniteState s_eq
                    (.ite (.cmp .notEqual (.var .local (ofString "eq")) (.const (BitVec.ofNat 64 0)))
                      (.seq
                        (.store (.op .add [.var .local (ofString "node"), .const (BitVec.ofNat 64 48)])
                          (.var .local (ofString "vptr")))
                        (.seq
                          (.store (.op .add [.var .local (ofString "node"), .const (BitVec.ofNat 64 56)])
                            (.var .local (ofString "vlen")))
                          (.return (.var .local (ofString "node")))))
                      .skip) = (none, s_eq) := by
                  rw [evaluateHOLFiniteState_ite, hc_eq0]; simp [evaluateHOLFiniteState_skip]
                rw [hite_in] at hdc_eq
                dsimp only at hdc_eq
                right
                refine ⟨_, hite_t.trans hdc_eq, ?_, ?_⟩
                · conv_lhs => rw [hseq_frame]
                · intro x hx
                  rw [resVarEq_lookup_ne _ _ _ _ hx]
                  simp [s_eq, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hx]
              · -- `eq ≠ 0`: updates `node + 48 := vptr`, `node + 56 := vlen`, returns `node`!
                have hite_in : evaluateHOLFiniteState s_eq
                    (.ite (.cmp .notEqual (.var .local (ofString "eq")) (.const (BitVec.ofNat 64 0)))
                      (.seq
                        (.store (.op .add [.var .local (ofString "node"), .const (BitVec.ofNat 64 48)])
                          (.var .local (ofString "vptr")))
                        (.seq
                          (.store (.op .add [.var .local (ofString "node"), .const (BitVec.ofNat 64 56)])
                            (.var .local (ofString "vlen")))
                          (.return (.var .local (ofString "node")))))
                      .skip) =
                    evaluateHOLFiniteState s_eq
                      (.seq
                        (.store (.op .add [.var .local (ofString "node"), .const (BitVec.ofNat 64 48)])
                          (.var .local (ofString "vptr")))
                        (.seq
                          (.store (.op .add [.var .local (ofString "node"), .const (BitVec.ofNat 64 56)])
                            (.var .local (ofString "vlen")))
                          (.return (.var .local (ofString "node"))))) := by
                  rw [evaluateHOLFiniteState_ite, hc_eq0, if_pos hweq0]; simp
                have hseq_nd : s_eq.locals.lookup (ofString "node") = some (.val (.word wnode)) := by
                  simp [s_eq, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsel_node,
                    show ofString "eq" ≠ ofString "node" by decide]
                have hseq_vp : s_eq.locals.lookup (ofString "vptr") = some (.val (.word wvptr)) := by
                  simp [s_eq, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsel_vptr,
                    show ofString "eq" ≠ ofString "vptr" by decide]
                have hseq_vl : s_eq.locals.lookup (ofString "vlen") = some (.val (.word wvlen)) := by
                  simp [s_eq, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsel_vlen,
                    show ofString "eq" ≠ ofString "vlen" by decide]
                have hdom48 : s_eq.memaddrs (wnode + BitVec.ofNat 64 48) := by
                  obtain ⟨_, hd, _⟩ := hp_nd.2.2.2.1.2.2 6 (by dsimp [nodeIvl]; omega)
                  dsimp [nodeIvl] at hd
                  have hm_eq : s_eq.memaddrs = s.memaddrs := by conv_lhs => rw [hseq_frame]
                  rw [hm_eq, (hnode_add 48 (by decide)).1]; simpa using hd
                have hdom56 : s_eq.memaddrs (wnode + BitVec.ofNat 64 56) := by
                  obtain ⟨_, hd, _⟩ := hp_nd.2.2.2.1.2.2 7 (by dsimp [nodeIvl]; omega)
                  dsimp [nodeIvl] at hd
                  have hm_eq : s_eq.memaddrs = s.memaddrs := by conv_lhs => rw [hseq_frame]
                  rw [hm_eq, (hnode_add 56 (by decide)).1]; simpa using hd
                have hmem_s_eq : s_eq.memory = s.memory := by conv_lhs => rw [hseq_frame]
                set m1 := Wave8Contracts.M26.updW s.memory (wnode + BitVec.ofNat 64 48) wvptr
                set m2 := Wave8Contracts.M26.updW m1 (wnode + BitVec.ofNat 64 56) wvlen
                have hupd_eval : evaluateHOLFiniteState s_eq
                    (.seq
                      (.store (.op .add [.var .local (ofString "node"), .const (BitVec.ofNat 64 48)])
                        (.var .local (ofString "vptr")))
                      (.seq
                        (.store (.op .add [.var .local (ofString "node"), .const (BitVec.ofNat 64 56)])
                          (.var .local (ofString "vlen")))
                        (.return (.var .local (ofString "node"))))) =
                    (some (.returned (.val (.word wnode))),
                      emptyLocalsHOLFinite { s_eq with memory := m2 }) := by
                  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_store]
                  have hd1 : @evalHOLExact 64 F _ s_eq.toExact (fun a => Classical.propDecidable (s_eq.memaddrs a))
                      (.op .add [.var .local (ofString "node"), .const (BitVec.ofNat 64 48)]) =
                      some (.val (.word (wnode + BitVec.ofNat 64 48))) := by
                    simp [evalHOLExact, evalListHOLExact, hseq_nd, valueIsWord, valueWord, wordOpHOL, wordOp]
                  have he1 : @evalHOLExact 64 F _ s_eq.toExact (fun a => Classical.propDecidable (s_eq.memaddrs a))
                      (.var .local (ofString "vptr")) = some (.val (.word wvptr)) := hseq_vp
                  rw [hd1, he1]
                  simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL, hdom48, ↓reduceIte, hmem_s_eq]
                  set u1 : PanSemStateFiniteExact 64 F := { s_eq with memory := m1 }
                  change evaluateHOLFiniteState u1
                    (.seq
                      (.store (.op .add [.var .local (ofString "node"), .const (BitVec.ofNat 64 56)])
                        (.var .local (ofString "vlen")))
                      (.return (.var .local (ofString "node")))) = _
                  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_store]
                  have hd2 : @evalHOLExact 64 F _ u1.toExact (fun a => Classical.propDecidable (u1.memaddrs a))
                      (.op .add [.var .local (ofString "node"), .const (BitVec.ofNat 64 56)]) =
                      some (.val (.word (wnode + BitVec.ofNat 64 56))) := by
                    simp [u1, evalHOLExact, evalListHOLExact, hseq_nd, valueIsWord, valueWord, wordOpHOL, wordOp]
                  have he2 : @evalHOLExact 64 F _ u1.toExact (fun a => Classical.propDecidable (u1.memaddrs a))
                      (.var .local (ofString "vlen")) = some (.val (.word wvlen)) := hseq_vl
                  have hdom56' : u1.memaddrs (wnode + BitVec.ofNat 64 56) := hdom56
                  rw [hd2, he2]
                  simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL, hdom56', ↓reduceIte]
                  have hu1_nd : u1.locals.lookup (ofString "node") = some (.val (.word wnode)) := hseq_nd
                  rw [evaluateHOLFiniteState_return]
                  simp [evalHOLExact, hu1_nd, shapeOfHOLExact, sizeOfShapeWithContextHOL]
                  rfl
                rw [hupd_eval] at hite_in
                rw [hite_in] at hdc_eq
                dsimp only at hdc_eq
                left
                rw [hite_t, hdc_eq]
                refine ⟨rfl, ?_⟩
                -- Show `NodeStep s _ Nd Nd` for modifying `node + 48` and `node + 56`!
                have hmw_other : ∀ off : Nat, off < 48 →
                    memW ({ s with memory := m2 } : PanSemStateFiniteExact 64 F) (wnode.toNat + off) =
                      memW s (wnode.toNat + off) := by
                  intro off hoff
                  have hlt : wnode.toNat + off < 2 ^ 64 := by omega
                  have hne56 : BitVec.ofNat 64 (wnode.toNat + off) ≠ wnode + BitVec.ofNat 64 56 := by
                    intro he; have := congrArg BitVec.toNat he
                    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt, (hnode_add 56 (by decide)).2] at this; omega
                  have hne48 : BitVec.ofNat 64 (wnode.toNat + off) ≠ wnode + BitVec.ofNat 64 48 := by
                    intro he; have := congrArg BitVec.toNat he
                    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt, (hnode_add 48 (by decide)).2] at this; omega
                  unfold memW
                  change (match m2 (BitVec.ofNat 64 (wnode.toNat + off)) with | .word w => w.toNat) = _
                  simp only [m2, m1, Wave8Contracts.M26.updW, if_neg hne56, if_neg hne48]
                have hmw_56 : memW ({ s with memory := m2 } : PanSemStateFiniteExact 64 F) (wnode.toNat + 56) = wvlen.toNat := by
                  have ha56 : BitVec.ofNat 64 (wnode.toNat + 56) = wnode + BitVec.ofNat 64 56 := (hnode_add 56 (by decide)).1.symm
                  unfold memW
                  change (match m2 (BitVec.ofNat 64 (wnode.toNat + 56)) with | .word w => w.toNat) = _
                  rw [ha56]; simp [m2, Wave8Contracts.M26.updW]
                have hstep_base : NodeStep s { s with memory := m2 } Nd Nd := by
                  refine nodeStep_modify_node hAR hNd hnode_in rfl rfl rfl rfl rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_
                  · intro a hout
                    by_cases h56 : a = wnode + BitVec.ofNat 64 56
                    · exfalso; apply hout; rw [h56, (hnode_add 56 (by decide)).2, hsz_node]; omega
                    · by_cases h48 : a = wnode + BitVec.ofNat 64 48
                      · exfalso; apply hout; rw [h48, (hnode_add 48 (by decide)).2, hsz_node]; omega
                      · simp only [m2, m1, Wave8Contracts.M26.updW, if_neg h56, if_neg h48]
                  · rw [hnode_k1]; intro h; cases h
                  · rw [hnode_k1]; intro h; cases h
                  · intro _; exact ⟨hmw_other 32 (by decide), hmw_other 40 (by decide)⟩
                  · rw [hmw_other 16 (by decide)]; exact hp_nd.2.2.2.2.2.2.2.1
                  · intro _; rw [hmw_56]; exact hwvlen_lt
                  · rw [hnode_k1]; intro h; cases h
                have hst_final_eq :
                    ({ (emptyLocalsHOLFinite { s_eq with memory := m2 }) with
                      locals := HolFiniteMapExact.resVarEq (emptyLocalsHOLFinite { s_eq with memory := m2 }).locals
                        (ofString "eq", s_el.locals.lookup (ofString "eq")) } : PanSemStateFiniteExact 64 F) =
                    { ({ s with memory := m2 }) with
                      locals := HolFiniteMapExact.resVarEq (emptyLocalsHOLFinite { s_eq with memory := m2 }).locals
                        (ofString "eq", s_el.locals.lookup (ofString "eq")),
                      clock := s_eq.clock } := by
                  dsimp only [emptyLocalsHOLFinite]
                  conv_lhs => rw [hseq_frame]
                rw [hst_final_eq]
                exact hstep_base.with_locals_clock _ _
            · rw [if_neg hsh] at hdc_eq
              rw [evaluateHOLFiniteState_seq_line780, hite_t, hdc_eq] at hres_core
              exact absurd hres_core not_resumes_error
          | exception eid ev =>
            exfalso
            exact memeq_body_no_exception _ eid ev (congrArg Prod.fst hmrun)
          | _ =>
            rw [evaluateHOLFiniteState_seq_line780, hite_t, hdc_eq] at hres_core
            rcases hres_core with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
    · -- `wel ≠ wrl`: `skip`, falls through immediately!
      have hite_f : evaluateHOLFiniteState s_el head_ite = (none, s_el) := by
        dsimp only [head_ite]
        rw [evaluateHOLFiniteState_ite, hc_el_rl, if_neg heq_len]; simp [evaluateHOLFiniteState_skip]
      right
      refine ⟨s_el, hite_f, by cases s; rfl, fun _ _ => rfl⟩
  -- Now split on `hhead_cases`!
  rcases hhead_cases with ⟨hhead_ret, hhead_step⟩ | ⟨s_mid, hhead_none, hsmid_frame, hsmid_loc⟩
  · -- Early return of `wnode`!
    have hcore_eq : evaluateHOLFiniteState s_el body_core =
        (some (.returned (.val (.word wnode))), (evaluateHOLFiniteState s_el head_ite).2) := by
      change evaluateHOLFiniteState s_el (.seq head_ite tail_prog) = _
      rw [evaluateHOLFiniteState_seq_line780]
      rcases hh : evaluateHOLFiniteState s_el head_ite with ⟨hr_i, hp_i⟩
      have h1 : hr_i = some (.returned (.val (.word wnode))) := by
        simpa [hh] using hhead_ret
      subst h1
      rfl
    refine ⟨Nd, ?_, ?_⟩
    · rw [hdec_unfold.2, hcore_eq]
      exact hhead_step.with_locals_clock _ _
    · intro v hv
      rw [hdec_unfold.1, hcore_eq] at hv
      injection hv with hv1; injection hv1 with hv2; subst hv2
      exact ⟨wnode, rfl, Or.inr hnode_in⟩
  · -- Fell through to `tail_prog` on `s_mid`!
    have hcore_eq : evaluateHOLFiniteState s_el body_core = evaluateHOLFiniteState s_mid tail_prog := by
      change evaluateHOLFiniteState s_el (.seq head_ite tail_prog) = _
      rw [evaluateHOLFiniteState_seq_line780, hhead_none]
    have htail_res : Resumes (evaluateHOLFiniteState s_mid tail_prog).1 := by
      rw [← hcore_eq]; exact hres_core
    have hsmid_code : s_mid.code = originalRuntimeCode := by rw [hsmid_frame]; exact hcode
    have hsmid_ek : s_mid.locals.lookup (ofString "ek") = some (.val (.word wek)) := by
      rw [hsmid_loc _ (by decide)]; exact hsel_ek
    have hsmid_el : s_mid.locals.lookup (ofString "el") = some (.val (.word wel)) := by
      rw [hsmid_loc _ (by decide)]; exact hsel_el
    have hsmid_rk : s_mid.locals.lookup (ofString "rk") = some (.val (.word wrk)) := by
      rw [hsmid_loc _ (by decide)]; exact hsel_rk
    have hsmid_rl : s_mid.locals.lookup (ofString "rl") = some (.val (.word wrl)) := by
      rw [hsmid_loc _ (by decide)]; exact hsel_rl
    have hsmid_node : s_mid.locals.lookup (ofString "node") = some (.val (.word wnode)) := by
      rw [hsmid_loc _ (by decide)]; exact hsel_node
    have hsmid_vptr : s_mid.locals.lookup (ofString "vptr") = some (.val (.word wvptr)) := by
      rw [hsmid_loc _ (by decide)]; exact hsel_vptr
    have hsmid_vlen : s_mid.locals.lookup (ofString "vlen") = some (.val (.word wvlen)) := by
      rw [hsmid_loc _ (by decide)]; exact hsel_vlen
    -- Step 1 of `tail_prog`: `decCall pl := common_prefix_length(ek, el, rk, rl)`
    dsimp only [tail_prog] at htail_res
    obtain ⟨cvals, cbody, ccallee, cret, _, hcargs, hcl, hcexn | ⟨crv, cpost, hcrun, _, hccont_res, hcr_eq, hcp_eq⟩⟩ :=
      decCall_resumes_inv htail_res
    · obtain ⟨eid, ev, hc_exn, hne_tr, _⟩ := hcexn
      have hsame := lookupCodeHOLFinite_installed_body s_mid.code.lookup (ofString "common_prefix_length")
        _ _ _ _ _ cvals ccallee (by rw [hsmid_code]; exact lookup_common_prefix_length) hcl
      subst hsame
      exact absurd (congrArg Prod.fst hc_exn)
        (cpl_body_no_nonTrap_exn (callEntryStateHOLFinite s_mid ccallee) hsmid_code eid ev hne_tr)
    · have hcvals : cvals = [.val (.word wek), .val (.word wel), .val (.word wrk), .val (.word wrl)] := by
        rw [evalListHOLFinite_eq_toExact] at hcargs
        simpa [evalListHOLExact, evalHOLExact, hsmid_ek, hsmid_el, hsmid_rk, hsmid_rl] using hcargs.symm
      subst hcvals
      have hcl_code : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "common_prefix_length")
          [.val (.word wek), .val (.word wel), .val (.word wrk), .val (.word wrl)] =
          some (cbody, ccallee, cret) := by rwa [← hsmid_code]
      obtain ⟨_, hcp_al⟩ := lookup_param_exact lookup_common_prefix_length hcl_code
        [(ofString "a", .one)] "al" .one [(ofString "b", .one), (ofString "bl", .one)]
        [.val (.word wek)] (.val (.word wel)) [.val (.word wrk), .val (.word wrl)]
        rfl rfl rfl (by decide)
      obtain ⟨_, hcp_bl⟩ := lookup_param_exact lookup_common_prefix_length hcl_code
        [(ofString "a", .one), (ofString "al", .one), (ofString "b", .one)] "bl" .one []
        [.val (.word wek), .val (.word wel), .val (.word wrk)] (.val (.word wrl)) []
        rfl rfl rfl (by decide)
      have hsmid_G : GuestInv s_mid := by rw [hsmid_frame]; exact guestInv_with_locals_clock s _ _ hAR.1
      have hro_cpl := FunSpec.at_lookup ro_common_prefix_length_spec s_mid hsmid_code
        _ cbody ccallee cret hcl (guestInv_callEntry s_mid ccallee hsmid_G)
        (by rw [hcrun]; simp) (by rw [hcrun]; exact Or.inl ⟨crv, rfl⟩)
      have hrv_spec : RetLe (fun st => min (locN st "al") (locN st "bl"))
          (ofString "common_prefix_length") := by
        rcases Wave8Contracts.M27.rv_common_prefix_length with ⟨ps, bd, rt, hlk_rv, hrun_rv⟩
        exact ⟨ps, bd, rt, hlk_rv, fun st hc hg hex hnt => hrun_rv st hc hg hex hnt⟩
      have hrv_cpl := FunSpec.at_lookup hrv_spec s_mid hsmid_code
        _ cbody ccallee cret hcl (guestInv_callEntry s_mid ccallee hsmid_G)
        (by rw [hcrun]; simp) crv (by rw [hcrun])
      rw [hcrun] at hro_cpl
      dsimp only at hro_cpl
      obtain ⟨wpl, rfl, hwpl_le⟩ := hrv_cpl
      dsimp only at hwpl_le
      have hal_ent : locN (callEntryStateHOLFinite s_mid ccallee) "al" = wel.toNat := by
        simp [locN, callEntryStateHOLFinite, hcp_al]
      have hbl_ent : locN (callEntryStateHOLFinite s_mid ccallee) "bl" = wrl.toNat := by
        simp [locN, callEntryStateHOLFinite, hcp_bl]
      rw [hal_ent, hbl_ent] at hwpl_le
      have hwpl_el : wpl.toNat ≤ wel.toNat := Nat.le_trans hwpl_le (Nat.min_le_left _ _)
      have hwpl_rl : wpl.toNat ≤ wrl.toNat := Nat.le_trans hwpl_le (Nat.min_le_right _ _)
      -- State `s_pl` after binding `pl := wpl`
      set s_pl := setVarHOLFinite (ofString "pl") (.val (.word wpl)) { cpost with locals := s_mid.locals }
      have hspl_frame : s_pl = { s with locals := s_pl.locals, clock := s_pl.clock } := by
        dsimp only [s_pl, setVarHOLFinite]
        rw [hro_cpl]; conv_lhs => rw [hsmid_frame]
        cases s; rfl
      have hspl_code : s_pl.code = originalRuntimeCode := by rw [hspl_frame]; exact hcode
      have hspl_AR : ArenaReady s_pl := by rw [hspl_frame]; exact localsFree_arenaReady s _ _ hAR
      have hspl_pl : s_pl.locals.lookup (ofString "pl") = some (.val (.word wpl)) := by
        simp [s_pl, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hspl_other : ∀ x : MlS, x ≠ ofString "pl" → s_pl.locals.lookup x = s_mid.locals.lookup x := by
        intro x hne
        simp [s_pl, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hne]
      -- Evaluate the 8 arguments to `_create_branch_from_two_leaves` on `s_pl` once:
      have hld48 := hload_node_off s_pl 48 (by rw [hspl_frame]) (by rw [hspl_frame])
        (by rw [hspl_other _ (by decide)]; exact hsmid_node) (by decide) (by decide)
      have hld56 := hload_node_off s_pl 56 (by rw [hspl_frame]) (by rw [hspl_frame])
        (by rw [hspl_other _ (by decide)]; exact hsmid_node) (by decide) (by decide)
      have hcb_args_eval : evalListHOLFinite s_pl (h := fun a => Classical.propDecidable (s_pl.memaddrs a))
          [.op .add [.var .local (ofString "ek"), .var .local (ofString "pl")],
           .op .sub [.var .local (ofString "el"), .var .local (ofString "pl")],
           .load .one (.op .add [.var .local (ofString "node"), .const (BitVec.ofNat 64 48)]),
           .load .one (.op .add [.var .local (ofString "node"), .const (BitVec.ofNat 64 56)]),
           .op .add [.var .local (ofString "rk"), .var .local (ofString "pl")],
           .op .sub [.var .local (ofString "rl"), .var .local (ofString "pl")],
           .var .local (ofString "vptr"),
           .var .local (ofString "vlen")] =
          some [.val (.word (wek + wpl)), .val (.word (wel - wpl)),
                .val (.word (BitVec.ofNat 64 (memW s (wnode.toNat + 48)))),
                .val (.word (BitVec.ofNat 64 (memW s (wnode.toNat + 56)))),
                .val (.word (wrk + wpl)), .val (.word (wrl - wpl)),
                .val (.word wvptr), .val (.word wvlen)] := by
        rw [evalListHOLFinite_eq_toExact]
        have hek' := hspl_other _ (by decide) |>.trans hsmid_ek
        have hel' := hspl_other _ (by decide) |>.trans hsmid_el
        have hrk' := hspl_other _ (by decide) |>.trans hsmid_rk
        have hrl' := hspl_other _ (by decide) |>.trans hsmid_rl
        have hvp' := hspl_other _ (by decide) |>.trans hsmid_vptr
        have hvl' := hspl_other _ (by decide) |>.trans hsmid_vlen
        simp only [evalListHOLExact]
        have ha1 : @evalHOLExact 64 F _ s_pl.toExact (fun a => Classical.propDecidable (s_pl.memaddrs a))
            (.op .add [.var .local (ofString "ek"), .var .local (ofString "pl")]) =
            some (.val (.word (wek + wpl))) := by
          simp [evalHOLExact, evalListHOLExact, hek', hspl_pl, valueIsWord, valueWord, wordOpHOL, wordOp]
        have ha2 : @evalHOLExact 64 F _ s_pl.toExact (fun a => Classical.propDecidable (s_pl.memaddrs a))
            (.op .sub [.var .local (ofString "el"), .var .local (ofString "pl")]) =
            some (.val (.word (wel - wpl))) := by
          simp [evalHOLExact, evalListHOLExact, hel', hspl_pl, valueIsWord, valueWord, wordOpHOL, wordOp]
        have ha5 : @evalHOLExact 64 F _ s_pl.toExact (fun a => Classical.propDecidable (s_pl.memaddrs a))
            (.op .add [.var .local (ofString "rk"), .var .local (ofString "pl")]) =
            some (.val (.word (wrk + wpl))) := by
          simp [evalHOLExact, evalListHOLExact, hrk', hspl_pl, valueIsWord, valueWord, wordOpHOL, wordOp]
        have ha6 : @evalHOLExact 64 F _ s_pl.toExact (fun a => Classical.propDecidable (s_pl.memaddrs a))
            (.op .sub [.var .local (ofString "rl"), .var .local (ofString "pl")]) =
            some (.val (.word (wrl - wpl))) := by
          simp [evalHOLExact, evalListHOLExact, hrl', hspl_pl, valueIsWord, valueWord, wordOpHOL, wordOp]
        have ha7 : @evalHOLExact 64 F _ s_pl.toExact (fun a => Classical.propDecidable (s_pl.memaddrs a))
            (.var .local (ofString "vptr")) = some (.val (.word wvptr)) := hvp'
        have ha8 : @evalHOLExact 64 F _ s_pl.toExact (fun a => Classical.propDecidable (s_pl.memaddrs a))
            (.var .local (ofString "vlen")) = some (.val (.word wvlen)) := hvl'
        rw [ha1, ha2, hld48, hld56, ha5, ha6, ha7, ha8]
      have hvl1_bound : (BitVec.ofNat 64 (memW s (wnode.toNat + 56))).toNat < 2 ^ 40 := by
        have h56 := hp_nd.2.2.2.2.2.2.2.2.1 hnode_k1
        have hlt64 : memW s (wnode.toNat + 56) < 2 ^ 64 := lt_trans h56 (by decide)
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64]
        exact h56
      -- Step 2 of `tail_prog`: `decCall br := _create_branch_from_two_leaves(...)`
      obtain ⟨cbvals, cbbody, cbcallee, cbret, _, hcbargs, hcbl, hcbexn | ⟨cbrv, cbpost, hcbrun, _, hcbcont_res, hcbr_eq, hcbp_eq⟩⟩ :=
        decCall_resumes_inv hccont_res
      · -- `_create_branch_from_two_leaves` cannot raise a non-TrapErr exception!
        obtain ⟨eid, ev, hcb_exn, hne_tr, _⟩ := hcbexn
        exfalso
        have hcbvals_eq : cbvals =
            [.val (.word (wek + wpl)), .val (.word (wel - wpl)),
             .val (.word (BitVec.ofNat 64 (memW s (wnode.toNat + 48)))),
             .val (.word (BitVec.ofNat 64 (memW s (wnode.toNat + 56)))),
             .val (.word (wrk + wpl)), .val (.word (wrl - wpl)),
             .val (.word wvptr), .val (.word wvlen)] :=
          Option.some.inj (hcbargs.symm.trans hcb_args_eval)
        subst hcbvals_eq
        have hcb_code : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "_create_branch_from_two_leaves")
            [.val (.word (wek + wpl)), .val (.word (wel - wpl)),
             .val (.word (BitVec.ofNat 64 (memW s (wnode.toNat + 48)))),
             .val (.word (BitVec.ofNat 64 (memW s (wnode.toNat + 56)))),
             .val (.word (wrk + wpl)), .val (.word (wrl - wpl)),
             .val (.word wvptr), .val (.word wvlen)] =
            some (cbbody, cbcallee, cbret) := by rwa [← hspl_code]
        obtain ⟨hbody_cb, hk1_cb⟩ := lookup_param_exact lookup__create_branch_from_two_leaves hcb_code
          [] "k1" .one [(ofString "l1", .one), (ofString "v1", .one), (ofString "vl1", .one),
                        (ofString "k2", .one), (ofString "l2", .one), (ofString "v2", .one), (ofString "vl2", .one)]
          [] (.val (.word (wek + wpl))) _ rfl rfl rfl (by decide)
        obtain ⟨_, hl1_cb⟩ := lookup_param_exact lookup__create_branch_from_two_leaves hcb_code
          [(ofString "k1", .one)] "l1" .one [(ofString "v1", .one), (ofString "vl1", .one),
                        (ofString "k2", .one), (ofString "l2", .one), (ofString "v2", .one), (ofString "vl2", .one)]
          [_] (.val (.word (wel - wpl))) _ rfl rfl rfl (by decide)
        obtain ⟨_, hv1_cb⟩ := lookup_param_exact lookup__create_branch_from_two_leaves hcb_code
          [(ofString "k1", .one), (ofString "l1", .one)] "v1" .one [(ofString "vl1", .one),
                        (ofString "k2", .one), (ofString "l2", .one), (ofString "v2", .one), (ofString "vl2", .one)]
          [_, _] _ _ rfl rfl rfl (by decide)
        obtain ⟨_, hvl1_cb⟩ := lookup_param_exact lookup__create_branch_from_two_leaves hcb_code
          [(ofString "k1", .one), (ofString "l1", .one), (ofString "v1", .one)] "vl1" .one
          [(ofString "k2", .one), (ofString "l2", .one), (ofString "v2", .one), (ofString "vl2", .one)]
          [_, _, _] _ _ rfl rfl rfl (by decide)
        obtain ⟨_, hk2_cb⟩ := lookup_param_exact lookup__create_branch_from_two_leaves hcb_code
          [(ofString "k1", .one), (ofString "l1", .one), (ofString "v1", .one), (ofString "vl1", .one)] "k2" .one
          [(ofString "l2", .one), (ofString "v2", .one), (ofString "vl2", .one)]
          [_, _, _, _] _ _ rfl rfl rfl (by decide)
        obtain ⟨_, hl2_cb⟩ := lookup_param_exact lookup__create_branch_from_two_leaves hcb_code
          [(ofString "k1", .one), (ofString "l1", .one), (ofString "v1", .one), (ofString "vl1", .one),
           (ofString "k2", .one)] "l2" .one [(ofString "v2", .one), (ofString "vl2", .one)]
          [_, _, _, _, _] _ _ rfl rfl rfl (by decide)
        obtain ⟨_, hv2_cb⟩ := lookup_param_exact lookup__create_branch_from_two_leaves hcb_code
          [(ofString "k1", .one), (ofString "l1", .one), (ofString "v1", .one), (ofString "vl1", .one),
           (ofString "k2", .one), (ofString "l2", .one)] "v2" .one [(ofString "vl2", .one)]
          [_, _, _, _, _, _] _ _ rfl rfl rfl (by decide)
        obtain ⟨_, hvl2_cb⟩ := lookup_param_exact lookup__create_branch_from_two_leaves hcb_code
          [(ofString "k1", .one), (ofString "l1", .one), (ofString "v1", .one), (ofString "vl1", .one),
           (ofString "k2", .one), (ofString "l2", .one), (ofString "v2", .one)] "vl2" .one []
          [_, _, _, _, _, _, _] _ [] rfl rfl rfl (by decide)
        subst hbody_cb
        have hk1_sub : KeyIn (callEntryStateHOLFinite s_pl cbcallee) Nd (wek + wpl).toNat (wel - wpl).toNat := by
          have heq1 : (wel - wpl).toNat = wel.toNat - wpl.toNat := by
            rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact hwpl_el)]
          have heq2 : BitVec.ofNat 64 wek.toNat + BitVec.ofNat 64 wpl.toNat = wek + wpl := by simp
          have hk' : KeyIn (callEntryStateHOLFinite s_pl cbcallee) Nd wek.toNat wel.toNat := by
            change KeyIn { s_pl with locals := _, clock := _ } Nd _ _
            rw [hspl_frame]; exact hkey_ek
          rw [← heq2, heq1]
          exact keyIn_subslice hk' (by omega)
        have hk2_sub : KeyIn (callEntryStateHOLFinite s_pl cbcallee) Nd (wrk + wpl).toNat (wrl - wpl).toNat := by
          have heq1 : (wrl - wpl).toNat = wrl.toNat - wpl.toNat := by
            rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact hwpl_rl)]
          have heq2 : BitVec.ofNat 64 wrk.toNat + BitVec.ofNat 64 wpl.toNat = wrk + wpl := by simp
          have hk' : KeyIn (callEntryStateHOLFinite s_pl cbcallee) Nd wrk.toNat wrl.toNat := by
            change KeyIn { s_pl with locals := _, clock := _ } Nd _ _
            rw [hspl_frame]; exact hkey_rk
          rw [← heq2, heq1]
          exact keyIn_subslice hk' (by omega)
        have hNd_cb : NodeHeap (callEntryStateHOLFinite s_pl cbcallee) Nd := by
          change NodeHeap { s_pl with locals := _, clock := _ } Nd
          rw [hspl_frame]; exact hNd
        obtain ⟨_, _, hcb_ret, _, _⟩ := create_branch_from_two_leaves_spec
          (callEntryStateHOLFinite s_pl cbcallee) hspl_code (localsFree_arenaReady s_pl _ _ hspl_AR)
          hk1_cb hl1_cb hv1_cb hvl1_cb hk2_cb hl2_cb hv2_cb hvl2_cb
          (by rw [hcb_exn]; exact Or.inr ⟨eid, ev, rfl, hne_tr⟩)
          Nd hNd_cb hk1_sub hvl1_bound hk2_sub hwvlen_lt
        rw [hcb_exn] at hcb_ret; cases hcb_ret
      · -- `_create_branch_from_two_leaves` returned `cbrv`!
        have hcbvals_eq : cbvals =
            [.val (.word (wek + wpl)), .val (.word (wel - wpl)),
             .val (.word (BitVec.ofNat 64 (memW s (wnode.toNat + 48)))),
             .val (.word (BitVec.ofNat 64 (memW s (wnode.toNat + 56)))),
             .val (.word (wrk + wpl)), .val (.word (wrl - wpl)),
             .val (.word wvptr), .val (.word wvlen)] :=
          Option.some.inj (hcbargs.symm.trans hcb_args_eval)
        subst hcbvals_eq
        have hcb_code : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "_create_branch_from_two_leaves")
            [.val (.word (wek + wpl)), .val (.word (wel - wpl)),
             .val (.word (BitVec.ofNat 64 (memW s (wnode.toNat + 48)))),
             .val (.word (BitVec.ofNat 64 (memW s (wnode.toNat + 56)))),
             .val (.word (wrk + wpl)), .val (.word (wrl - wpl)),
             .val (.word wvptr), .val (.word wvlen)] =
            some (cbbody, cbcallee, cbret) := by rwa [← hspl_code]
        obtain ⟨hbody_cb, hk1_cb⟩ := lookup_param_exact lookup__create_branch_from_two_leaves hcb_code
          [] "k1" .one [(ofString "l1", .one), (ofString "v1", .one), (ofString "vl1", .one),
                        (ofString "k2", .one), (ofString "l2", .one), (ofString "v2", .one), (ofString "vl2", .one)]
          [] (.val (.word (wek + wpl))) _ rfl rfl rfl (by decide)
        obtain ⟨_, hl1_cb⟩ := lookup_param_exact lookup__create_branch_from_two_leaves hcb_code
          [(ofString "k1", .one)] "l1" .one [(ofString "v1", .one), (ofString "vl1", .one),
                        (ofString "k2", .one), (ofString "l2", .one), (ofString "v2", .one), (ofString "vl2", .one)]
          [_] (.val (.word (wel - wpl))) _ rfl rfl rfl (by decide)
        obtain ⟨_, hv1_cb⟩ := lookup_param_exact lookup__create_branch_from_two_leaves hcb_code
          [(ofString "k1", .one), (ofString "l1", .one)] "v1" .one [(ofString "vl1", .one),
                        (ofString "k2", .one), (ofString "l2", .one), (ofString "v2", .one), (ofString "vl2", .one)]
          [_, _] _ _ rfl rfl rfl (by decide)
        obtain ⟨_, hvl1_cb⟩ := lookup_param_exact lookup__create_branch_from_two_leaves hcb_code
          [(ofString "k1", .one), (ofString "l1", .one), (ofString "v1", .one)] "vl1" .one
          [(ofString "k2", .one), (ofString "l2", .one), (ofString "v2", .one), (ofString "vl2", .one)]
          [_, _, _] _ _ rfl rfl rfl (by decide)
        obtain ⟨_, hk2_cb⟩ := lookup_param_exact lookup__create_branch_from_two_leaves hcb_code
          [(ofString "k1", .one), (ofString "l1", .one), (ofString "v1", .one), (ofString "vl1", .one)] "k2" .one
          [(ofString "l2", .one), (ofString "v2", .one), (ofString "vl2", .one)]
          [_, _, _, _] _ _ rfl rfl rfl (by decide)
        obtain ⟨_, hl2_cb⟩ := lookup_param_exact lookup__create_branch_from_two_leaves hcb_code
          [(ofString "k1", .one), (ofString "l1", .one), (ofString "v1", .one), (ofString "vl1", .one),
           (ofString "k2", .one)] "l2" .one [(ofString "v2", .one), (ofString "vl2", .one)]
          [_, _, _, _, _] _ _ rfl rfl rfl (by decide)
        obtain ⟨_, hv2_cb⟩ := lookup_param_exact lookup__create_branch_from_two_leaves hcb_code
          [(ofString "k1", .one), (ofString "l1", .one), (ofString "v1", .one), (ofString "vl1", .one),
           (ofString "k2", .one), (ofString "l2", .one)] "v2" .one [(ofString "vl2", .one)]
          [_, _, _, _, _, _] _ _ rfl rfl rfl (by decide)
        obtain ⟨_, hvl2_cb⟩ := lookup_param_exact lookup__create_branch_from_two_leaves hcb_code
          [(ofString "k1", .one), (ofString "l1", .one), (ofString "v1", .one), (ofString "vl1", .one),
           (ofString "k2", .one), (ofString "l2", .one), (ofString "v2", .one)] "vl2" .one []
          [_, _, _, _, _, _, _] _ [] rfl rfl rfl (by decide)
        subst hbody_cb
        have hk1_sub : KeyIn (callEntryStateHOLFinite s_pl cbcallee) Nd (wek + wpl).toNat (wel - wpl).toNat := by
          have heq1 : (wel - wpl).toNat = wel.toNat - wpl.toNat := by
            rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact hwpl_el)]
          have heq2 : BitVec.ofNat 64 wek.toNat + BitVec.ofNat 64 wpl.toNat = wek + wpl := by simp
          have hk' : KeyIn (callEntryStateHOLFinite s_pl cbcallee) Nd wek.toNat wel.toNat := by
            change KeyIn { s_pl with locals := _, clock := _ } Nd _ _
            rw [hspl_frame]; exact hkey_ek
          rw [← heq2, heq1]
          exact keyIn_subslice hk' (by omega)
        have hk2_sub : KeyIn (callEntryStateHOLFinite s_pl cbcallee) Nd (wrk + wpl).toNat (wrl - wpl).toNat := by
          have heq1 : (wrl - wpl).toNat = wrl.toNat - wpl.toNat := by
            rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact hwpl_rl)]
          have heq2 : BitVec.ofNat 64 wrk.toNat + BitVec.ofNat 64 wpl.toNat = wrk + wpl := by simp
          have hk' : KeyIn (callEntryStateHOLFinite s_pl cbcallee) Nd wrk.toNat wrl.toNat := by
            change KeyIn { s_pl with locals := _, clock := _ } Nd _ _
            rw [hspl_frame]; exact hkey_rk
          rw [← heq2, heq1]
          exact keyIn_subslice hk' (by omega)
        have hNd_cb : NodeHeap (callEntryStateHOLFinite s_pl cbcallee) Nd := by
          change NodeHeap { s_pl with locals := _, clock := _ } Nd
          rw [hspl_frame]; exact hNd
        obtain ⟨Nd_cb, wbr, hcb_ret, hwbr_in, hstep_cb_raw⟩ := create_branch_from_two_leaves_spec
          (callEntryStateHOLFinite s_pl cbcallee) hspl_code (localsFree_arenaReady s_pl _ _ hspl_AR)
          hk1_cb hl1_cb hv1_cb hvl1_cb hk2_cb hl2_cb hv2_cb hvl2_cb
          (by rw [hcbrun]; exact Or.inl ⟨cbrv, rfl⟩)
          Nd hNd_cb hk1_sub hvl1_bound hk2_sub hwvlen_lt
        rw [hcbrun] at hcb_ret hstep_cb_raw
        injection hcb_ret with h1; injection h1 with hcbrv_eq; subst hcbrv_eq
        -- `s_br` after binding `br := wbr`
        set s_br := setVarHOLFinite (ofString "br") (.val (.word wbr)) { cbpost with locals := s_pl.locals }
        have hstep_cb : NodeStep s s_br Nd Nd_cb := by
          have h1 : NodeStep s_pl cbpost Nd Nd_cb := NodeStep.from_locals_clock hstep_cb_raw
          have h2 : NodeStep s cbpost Nd Nd_cb := by
            rw [hspl_frame] at h1
            exact NodeStep.from_locals_clock h1
          exact h2.with_locals_clock _ _
        have hsbr_code : s_br.code = originalRuntimeCode := hstep_cb.arena.1.code
        have hsbr_br : s_br.locals.lookup (ofString "br") = some (.val (.word wbr)) := by
          simp [s_br, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have hsbr_pl : s_br.locals.lookup (ofString "pl") = some (.val (.word wpl)) := by
          simp [s_br, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hspl_pl,
            show ofString "br" ≠ ofString "pl" by decide]
        have hsbr_ek : s_br.locals.lookup (ofString "ek") = some (.val (.word wek)) := by
          have hek' := hspl_other _ (by decide) |>.trans hsmid_ek
          simp [s_br, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hek',
            show ofString "br" ≠ ofString "ek" by decide]
        -- Final step: `if 0 < pl then call none node_new_ext(ek, pl, br) else skip; return br`
        have hc_pl_pos : @evalHOLExact 64 F _ s_br.toExact (fun a => Classical.propDecidable (s_br.memaddrs a))
            (.cmp .lower (.const (BitVec.ofNat 64 0)) (.var .local (ofString "pl"))) =
            some (.val (.word (if 0 < wpl.toNat then 1 else 0))) := by
          simp [evalHOLExact, hsbr_pl, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def]
        by_cases hpl_pos : 0 < wpl.toNat
        · -- Tail call `node_new_ext(ek, pl, br)`!
          have hite_ext : evaluateHOLFiniteState s_br
              (.ite (.cmp .lower (.const (BitVec.ofNat 64 0)) (.var .local (ofString "pl")))
                (.call none (ofString "node_new_ext")
                  [.var .local (ofString "ek"), .var .local (ofString "pl"), .var .local (ofString "br")])
                .skip) =
              evaluateHOLFiniteState s_br
                (.call none (ofString "node_new_ext")
                  [.var .local (ofString "ek"), .var .local (ofString "pl"), .var .local (ofString "br")]) := by
            rw [evaluateHOLFiniteState_ite, hc_pl_pos, if_pos hpl_pos]; simp
          rw [evaluateHOLFiniteState_seq_line780, hite_ext] at hcbcont_res hcbr_eq hcbp_eq
          -- Note `.call none` never returns `none` when it resumes! Let's check:
          have hcall_not_none : (evaluateHOLFiniteState s_br
              (.call none (ofString "node_new_ext")
                [.var .local (ofString "ek"), .var .local (ofString "pl"), .var .local (ofString "br")])).1 ≠ none := by
            rw [evaluateHOLFiniteState_call]
            rcases evalListHOLFinite s_br (h := fun a => Classical.propDecidable (s_br.memaddrs a))
                [.var .local (ofString "ek"), .var .local (ofString "pl"), .var .local (ofString "br")] with _ | vs
            · simp
            · dsimp only
              rcases lookupCodeHOLFinite s_br.code.lookup (ofString "node_new_ext") vs with _ | ⟨eb, ec, er⟩
              · simp
              · dsimp only
                split
                · simp
                · rcases evaluateHOLFiniteState (callEntryStateHOLFinite s_br ec) eb with ⟨er1, ep1⟩
                  rcases er1 with _ | er1'
                  · simp
                  · cases er1' <;> simp
                    split <;> simp
          rcases hcall_out : evaluateHOLFiniteState s_br
              (.call none (ofString "node_new_ext")
                [.var .local (ofString "ek"), .var .local (ofString "pl"), .var .local (ofString "br")]) with ⟨er_out, ep_out⟩
          have hcall_out' : evaluateHOLFiniteState s_br
              (.call none (ofString "node_new_ext")
                [.var .local (ofString "ek"), .var .local (ofString "pl"), .var .local (ofString "br")]) = (er_out, ep_out) := hcall_out
          rw [hcall_out'] at hcbcont_res hcbr_eq hcbp_eq hcall_not_none
          rcases er_out with _ | er_some
          · exact absurd rfl hcall_not_none
          · dsimp only at hcbcont_res hcbr_eq hcbp_eq
            obtain ⟨evals, ebody, ecallee, eret, _, heargs, hel_lk, heexn | ⟨erv, epost, herun, _, heout_eq⟩⟩ :=
              call_none_resumes_inv (by rw [hcall_out']; exact hcbcont_res)
            · -- If `node_new_ext` raised a non-TrapErr exception, `nf_node_new_ext` handles it too!
              -- Let's invoke `nodeStep_of_nodeFn nf_node_new_ext` uniformly on BOTH branches!
              obtain ⟨eid, ev, he_exn, hne_tr, he_call_eq⟩ := heexn
              have hevals : evals = [.val (.word wek), .val (.word wpl), .val (.word wbr)] := by
                rw [evalListHOLFinite_eq_toExact] at heargs
                simpa [evalListHOLExact, evalHOLExact, hsbr_ek, hsbr_pl, hsbr_br] using heargs.symm
              subst hevals
              have hel_code : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "node_new_ext")
                  [.val (.word wek), .val (.word wpl), .val (.word wbr)] =
                  some (ebody, ecallee, eret) := by rwa [← hsbr_code]
              obtain ⟨_, hep_nib⟩ := lookup_param_exact lookup_node_new_ext hel_code
                [] "nib" .one [(ofString "nlen", .one), (ofString "child", .one)]
                [] (.val (.word wek)) _ rfl rfl rfl (by decide)
              obtain ⟨_, hep_nlen⟩ := lookup_param_exact lookup_node_new_ext hel_code
                [(ofString "nib", .one)] "nlen" .one [(ofString "child", .one)]
                [_] (.val (.word wpl)) _ rfl rfl rfl (by decide)
              obtain ⟨_, hep_ch⟩ := lookup_param_exact lookup_node_new_ext hel_code
                [(ofString "nib", .one), (ofString "nlen", .one)] "child" .one []
                [_, _] (.val (.word wbr)) [] rfl rfl rfl (by decide)
              have hkey_ek_pl : KeyIn s_br Nd_cb wek.toNat wpl.toNat := by
                have hk_cb : KeyIn s_br Nd_cb wek.toNat wel.toNat := hstep_cb.keyIn hAR hNd hkey_ek
                have h0 : (BitVec.ofNat 64 wek.toNat + BitVec.ofNat 64 0).toNat = wek.toNat := by simp
                rw [← h0]
                exact keyIn_subslice hk_cb (by omega)
              obtain ⟨Nd_ext, hstep_ext, _⟩ := nodeStep_of_nodeFn nf_node_new_ext s_br hsbr_code
                hstep_cb.arena hstep_cb.heap hel_lk
                (by intro n hn; rw [List.mem_singleton.mp hn]; simp [locN, callEntryStateHOLFinite, hep_ch]; exact Or.inr hwbr_in)
                (by simp [locN, callEntryStateHOLFinite, hep_nib, hep_nlen]; exact hkey_ek_pl)
                (by rw [he_exn]; exact Or.inr ⟨eid, ev, rfl, hne_tr⟩)
              rw [hcall_out'] at he_call_eq
              obtain ⟨her_eq, hep_eq⟩ := Prod.mk.inj he_call_eq
              refine ⟨Nd_ext, ?_, ?_⟩
              · rw [hdec_unfold.2, hcore_eq, hcp_eq, hcbp_eq, hep_eq]
                exact (((NodeStep.trans hAR hstep_cb hstep_ext).with_locals_clock _ _).with_locals_clock _ _).with_locals_clock _ _
              · intro v hv
                rw [hdec_unfold.1, hcore_eq, hcr_eq, hcbr_eq, her_eq] at hv
                cases hv
            · -- `node_new_ext` returned `erv`!
              have hevals : evals = [.val (.word wek), .val (.word wpl), .val (.word wbr)] := by
                rw [evalListHOLFinite_eq_toExact] at heargs
                simpa [evalListHOLExact, evalHOLExact, hsbr_ek, hsbr_pl, hsbr_br] using heargs.symm
              subst hevals
              have hel_code : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "node_new_ext")
                  [.val (.word wek), .val (.word wpl), .val (.word wbr)] =
                  some (ebody, ecallee, eret) := by rwa [← hsbr_code]
              obtain ⟨_, hep_nib⟩ := lookup_param_exact lookup_node_new_ext hel_code
                [] "nib" .one [(ofString "nlen", .one), (ofString "child", .one)]
                [] (.val (.word wek)) _ rfl rfl rfl (by decide)
              obtain ⟨_, hep_nlen⟩ := lookup_param_exact lookup_node_new_ext hel_code
                [(ofString "nib", .one)] "nlen" .one [(ofString "child", .one)]
                [_] (.val (.word wpl)) _ rfl rfl rfl (by decide)
              obtain ⟨_, hep_ch⟩ := lookup_param_exact lookup_node_new_ext hel_code
                [(ofString "nib", .one), (ofString "nlen", .one)] "child" .one []
                [_, _] (.val (.word wbr)) [] rfl rfl rfl (by decide)
              have hkey_ek_pl : KeyIn s_br Nd_cb wek.toNat wpl.toNat := by
                have hk_cb : KeyIn s_br Nd_cb wek.toNat wel.toNat := hstep_cb.keyIn hAR hNd hkey_ek
                have h0 : (BitVec.ofNat 64 wek.toNat + BitVec.ofNat 64 0).toNat = wek.toNat := by simp
                rw [← h0]
                exact keyIn_subslice hk_cb (by omega)
              obtain ⟨Nd_ext, hstep_ext, hret_ext⟩ := nodeStep_of_nodeFn nf_node_new_ext s_br hsbr_code
                hstep_cb.arena hstep_cb.heap hel_lk
                (by intro n hn; rw [List.mem_singleton.mp hn]; simp [locN, callEntryStateHOLFinite, hep_ch]; exact Or.inr hwbr_in)
                (by simp [locN, callEntryStateHOLFinite, hep_nib, hep_nlen]; exact hkey_ek_pl)
                (by rw [herun]; exact Or.inl ⟨erv, rfl⟩)
              rw [herun] at hstep_ext hret_ext
              dsimp only at hstep_ext hret_ext
              obtain ⟨wext, rfl, hwext_root⟩ := hret_ext erv rfl
              rw [hcall_out'] at heout_eq
              obtain ⟨her_eq, hep_eq⟩ := Prod.mk.inj heout_eq
              refine ⟨Nd_ext, ?_, ?_⟩
              · rw [hdec_unfold.2, hcore_eq, hcp_eq, hcbp_eq, hep_eq]
                exact (((NodeStep.trans hAR hstep_cb hstep_ext).with_locals_clock _ _).with_locals_clock _ _).with_locals_clock _ _
              · intro v hv
                rw [hdec_unfold.1, hcore_eq, hcr_eq, hcbr_eq, her_eq] at hv
                injection hv with hv1; injection hv1 with hv2; subst hv2
                exact ⟨wext, rfl, hwext_root⟩
        · -- `pl == 0`: `skip; return br`!
          have hite_skip : evaluateHOLFiniteState s_br
              (.ite (.cmp .lower (.const (BitVec.ofNat 64 0)) (.var .local (ofString "pl")))
                (.call none (ofString "node_new_ext")
                  [.var .local (ofString "ek"), .var .local (ofString "pl"), .var .local (ofString "br")])
                .skip) = (none, s_br) := by
            rw [evaluateHOLFiniteState_ite, hc_pl_pos, if_neg hpl_pos]; simp [evaluateHOLFiniteState_skip]
          have hret_br : evaluateHOLFiniteState s_br (.return (.var .local (ofString "br"))) =
              (some (.returned (.val (.word wbr))), emptyLocalsHOLFinite s_br) := by
            simp [evaluateHOLFiniteState_return, evalHOLExact, hsbr_br, shapeOfHOLExact, sizeOfShapeWithContextHOL]
          rw [evaluateHOLFiniteState_seq_line780, hite_skip] at hcbr_eq hcbp_eq
          dsimp only at hcbr_eq hcbp_eq
          rw [hret_br] at hcbr_eq hcbp_eq
          refine ⟨Nd_cb, ?_, ?_⟩
          · rw [hdec_unfold.2, hcore_eq, hcp_eq, hcbp_eq]
            exact ((hstep_cb.with_locals_clock _ _).with_locals_clock _ _).with_locals_clock _ _
          · intro v hv
            rw [hdec_unfold.1, hcore_eq, hcr_eq, hcbr_eq] at hv
            injection hv with hv1; injection hv1 with hv2; subst hv2
            exact ⟨wbr, rfl, Or.inr hwbr_in⟩

end InitECandidate.Solver.Wave8GuestInv.R16Shards
