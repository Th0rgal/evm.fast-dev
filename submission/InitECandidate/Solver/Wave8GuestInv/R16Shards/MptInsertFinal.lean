import InitECandidate.Solver.Wave8GuestInv.R16Shards.MptInsertSpec

/-! Final assembly of `mpt_insert_node_spec` (`ContractParts/C00.lean:247`) with 0 `sorry` and 0 custom axioms. -/

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

/-- `mpt_fail` call never returns `(none, _)`: its body executes `raise MptErr code`, which either
raises an exception or errors. -/
theorem mpt_fail_not_none {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (c : BitVec 64) (u : PanSemStateFiniteExact 64 F) :
    evaluateHOLFiniteState s (.call (some (none, none)) (ofString "mpt_fail") [.const c]) ≠ (none, u) := by
  intro h
  obtain ⟨values, body, callee, retShape, rv, post, hargs, hl, hrun, _⟩ := call_void_none_inv h
  have hsame := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "mpt_fail")
    _ _ _ _ _ values callee (by rw [hc]; exact lookup_mpt_fail) hl
  subst hsame
  have hbody : sourceFnBody Guest.Software.guestFn_mpt_fail =
      .seq (.raise (ofString "MptErr") (.var .local (ofString "code"))) (.return (.const 0)) := rfl
  rw [hbody, evaluateHOLFiniteState_seq_line780] at hrun
  have hraise_out : ∀ st : PanSemStateFiniteExact 64 F,
      (evaluateHOLFiniteState st (.raise (ofString "MptErr") (.var .local (ofString "code")))).1 = some .error ∨
      ∃ v, (evaluateHOLFiniteState st (.raise (ofString "MptErr") (.var .local (ofString "code")))).1 =
        some (.exception (ofString "MptErr") v) := by
    intro st
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only
      split
      · exact Or.inr ⟨_, rfl⟩
      · exact Or.inl rfl
    · exact Or.inl rfl
  rcases hr_raise : evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
      (.raise (ofString "MptErr") (.var .local (ofString "code"))) with ⟨rr, mr⟩
  rw [hr_raise] at hrun
  rcases hraise_out (callEntryStateHOLFinite s callee) with herr | ⟨ev, hex⟩
  · rw [hr_raise] at herr; cases herr; simp at hrun
  · rw [hr_raise] at hex; cases hex; simp at hrun

/-- Full selection step (`insSelect`) from prepared state (`go = 0`, `r = next_node = next_slot = next_level = 0`). -/
theorem insSelect_step {F : Type}
    {s0 s u : PanSemStateFiniteExact 64 F} {Nd0 Nd : List Nat}
    {wkey wklen wvptr wvlen wnode wslot wlevel wres : BitVec 64}
    (ha0 : ArenaReady s0)
    (hstep : NodeStep s0 s Nd0 Nd)
    (hsc : s.code = originalRuntimeCode)
    (hnode_root : RootIn Nd wnode.toNat)
    (hle : wlevel.toNat ≤ wklen.toNat)
    (hvlt : wvlen.toNat < 2 ^ 40)
    (hklt : wklen.toNat ≤ 64)
    (hkey : KeyIn s Nd (wkey.toNat + wlevel.toNat) (wklen.toNat - wlevel.toNat))
    (hsl_inv : wslot = 0 ∨ (ValidSlot s Nd wslot.toNat ∧ wres.toNat ∈ Nd))
    (hs_key : s.locals.lookup (ofString "key") = some (.val (.word wkey)))
    (hs_klen : s.locals.lookup (ofString "klen") = some (.val (.word wklen)))
    (hs_vptr : s.locals.lookup (ofString "vptr") = some (.val (.word wvptr)))
    (hs_vlen : s.locals.lookup (ofString "vlen") = some (.val (.word wvlen)))
    (hs_node : s.locals.lookup (ofString "node") = some (.val (.word wnode)))
    (hs_slot : s.locals.lookup (ofString "slot") = some (.val (.word wslot)))
    (hs_level : s.locals.lookup (ofString "level") = some (.val (.word wlevel)))
    (hs_res : s.locals.lookup (ofString "result") = some (.val (.word wres)))
    (hs_nn : s.locals.lookup (ofString "next_node") = some (.val (.word 0)))
    (hs_ns : s.locals.lookup (ofString "next_slot") = some (.val (.word 0)))
    (hs_nl : s.locals.lookup (ofString "next_level") = some (.val (.word 0)))
    (hs_go : s.locals.lookup (ofString "go") = some (.val (.word 0)))
    (hrun : evaluateHOLFiniteState s insSelect = (none, u)) :
    InsSelectPost s0 u Nd0 wkey wklen wvptr wvlen wslot wres := by
  rw [insSelect_eq, evaluateHOLFiniteState_ite] at hrun
  have hc_nd0 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .equal (.var .local (ofString "node")) (.const 0)) =
      some (.val (.word (if wnode = 0 then 1 else 0))) := by
    simp [evalHOLExact, hs_node, Compiler.Encoders.Asm.wordCmpHOL]
  rw [hc_nd0] at hrun
  by_cases hnd0 : wnode = 0
  · -- Null-root case (`node == 0`): `r = node_new_leaf(key + level, klen - level, vptr, vlen)`
    rw [if_pos hnd0] at hrun
    simp only [show (1 : BitVec 64) ≠ 0 by decide, ↓reduceIte] at hrun
    obtain ⟨lvals, lbody, lcallee, lret, lrv, lpost, hlargs, hll, hlrun, hu_eq⟩ :=
      call_assign_local_none_inv hrun
    have hlvals_eq : lvals = [.val (.word (wkey + wlevel)), .val (.word (wklen - wlevel)),
        .val (.word wvptr), .val (.word wvlen)] := by
      rw [evalListHOLFinite_eq_toExact] at hlargs
      simpa [evalListHOLExact, evalHOLExact, hs_key, hs_level, hs_klen, hs_vptr, hs_vlen,
        valueIsWord, valueWord, wordOpHOL, wordOp] using hlargs.symm
    subst hlvals_eq
    have hll_code : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "node_new_leaf")
        [.val (.word (wkey + wlevel)), .val (.word (wklen - wlevel)),
         .val (.word wvptr), .val (.word wvlen)] =
        some (lbody, lcallee, lret) := by rwa [← hsc]
    obtain ⟨_, hlp_nib⟩ := lookup_param_exact lookup_node_new_leaf hll_code
      [] "nib" .one [(ofString "nlen", .one), (ofString "vptr", .one), (ofString "vlen", .one)]
      [] (.val (.word (wkey + wlevel))) _ rfl rfl rfl (by decide)
    obtain ⟨_, hlp_nlen⟩ := lookup_param_exact lookup_node_new_leaf hll_code
      [(ofString "nib", .one)] "nlen" .one [(ofString "vptr", .one), (ofString "vlen", .one)]
      [_] (.val (.word (wklen - wlevel))) _ rfl rfl rfl (by decide)
    obtain ⟨_, hlp_vlen⟩ := lookup_param_exact lookup_node_new_leaf hll_code
      [(ofString "nib", .one), (ofString "nlen", .one), (ofString "vptr", .one)] "vlen" .one []
      [_, _, _] (.val (.word wvlen)) [] rfl rfl rfl (by decide)
    obtain ⟨_, hkey_bv⟩ := keyIn_suffix_bv hle hkey
    obtain ⟨Nd_lf, hstep_lf, hret_lf⟩ := nodeStep_of_nodeFn nf_node_new_leaf s hsc
      hstep.arena hstep.heap hll
      (by intro _ h; simp at h)
      (by simp [locN, callEntryStateHOLFinite, hlp_nib, hlp_nlen, hlp_vlen]; exact ⟨hkey_bv, hvlt⟩)
      (by rw [hlrun]; exact Or.inl ⟨lrv, rfl⟩)
    rw [hlrun] at hstep_lf hret_lf; dsimp only at hstep_lf hret_lf
    obtain ⟨wlf, rfl, hwlf_root⟩ := hret_lf lrv rfl
    subst hu_eq
    set slf := setVarHOLFinite (ofString "r") (.val (.word wlf)) { lpost with locals := s.locals }
    have hstep_s_slf : NodeStep s slf Nd Nd_lf := hstep_lf.with_locals_clock _ _
    have hslf_code : slf.code = originalRuntimeCode := by
      have := (evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s lcallee) lbody).1
      rw [hlrun] at this; exact this.trans hsc
    have hslf_other : ∀ x : MlS, x ≠ ofString "r" → slf.locals.lookup x = s.locals.lookup x := by
      intro x hx
      simp [slf, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hx]
    exact ⟨Nd_lf, wlf, 0, 0, 0, 0,
      NodeStep.trans ha0 hstep hstep_s_slf, hslf_code,
      (hslf_other _ (by decide)).trans hs_key,
      (hslf_other _ (by decide)).trans hs_klen,
      (hslf_other _ (by decide)).trans hs_vptr,
      (hslf_other _ (by decide)).trans hs_vlen,
      (hslf_other _ (by decide)).trans hs_slot,
      (hslf_other _ (by decide)).trans hs_res,
      by simp [slf, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE],
      (hslf_other _ (by decide)).trans hs_nn,
      (hslf_other _ (by decide)).trans hs_ns,
      (hslf_other _ (by decide)).trans hs_nl,
      (hslf_other _ (by decide)).trans hs_go,
      hwlf_root,
      hsl_inv.imp id (fun ⟨hv, hrin⟩ => ⟨hv.mono hstep_s_slf, hstep_s_slf.sub _ hrin⟩),
      fun h => absurd rfl h⟩
  · -- Non-null case (`node != 0`): `wnode.toNat ∈ Nd`
    rw [if_neg hnd0] at hrun
    simp only [↓reduceIte] at hrun
    have hwnode_nz : wnode.toNat ≠ 0 := fun hz => hnd0 (BitVec.eq_of_toNat_eq hz)
    have hnode_in : wnode.toNat ∈ Nd := hnode_root.resolve_left hwnode_nz
    rw [insNonnull_eq] at hrun
    obtain ⟨hsz32, _, _⟩ := nodeSize_bounds (memW s wnode.toNat)
    obtain ⟨hev_k, hwk_nat⟩ := eval_load_node_field hstep.heap hnode_in hs_node 0 (by omega) (by decide)
    obtain ⟨vk, u_k, hev1, hr_k, hu_eq⟩ := dec_none_inv hrun
    have hvk : vk = .val (.word (BitVec.ofNat 64 (memW s (wnode.toNat + 0)))) :=
      Option.some.inj (hev1.symm.trans hev_k)
    subst hvk
    suffices hk_post : InsSelectPost s0 u_k Nd0 wkey wklen wvptr wvlen wslot wres by
      rw [hu_eq]
      exact hk_post.restore_local (by decide)
    set wk := BitVec.ofNat 64 (memW s (wnode.toNat + 0))
    have hwk_s : wk.toNat = memW s wnode.toNat := by simpa using hwk_nat
    have hwk_le3 : wk.toNat ≤ 3 := by rw [hwk_s]; exact (hstep.heap.1 wnode.toNat hnode_in).1
    set sk := setVarHOLFinite (ofString "k") (.val (.word wk)) s
    have hsk_k : sk.locals.lookup (ofString "k") = some (.val (.word wk)) := by
      simp [sk, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hsk_other : ∀ x : MlS, x ≠ ofString "k" → sk.locals.lookup x = s.locals.lookup x := by
      intro x hx
      simp [sk, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hx]
    obtain ⟨m_chk, hchk, hr_inv_kinds⟩ := seq_none_inv hr_k
    -- `if k == 0 { mpt_fail(2) } else { skip }`
    rw [evaluateHOLFiniteState_ite] at hchk
    have hc_k0 : @evalHOLExact 64 F _ sk.toExact (fun a => Classical.propDecidable (sk.memaddrs a))
        (.cmp .equal (.var .local (ofString "k")) (.const 0)) =
        some (.val (.word (if wk = 0 then 1 else 0))) := by
      simp [evalHOLExact, hsk_k, Compiler.Encoders.Asm.wordCmpHOL]
    rw [hc_k0] at hchk
    by_cases hwk0 : wk = 0
    · rw [if_pos hwk0] at hchk
      simp only [show (1 : BitVec 64) ≠ 0 by decide, ↓reduceIte] at hchk
      exact absurd hchk (mpt_fail_not_none sk hsc 2 m_chk)
    · rw [if_neg hwk0] at hchk
      dsimp only at hchk
      rw [evaluateHOLFiniteState_skip] at hchk
      injection hchk with _ hmchk; subst hmchk
      have hwk_pos : 1 ≤ wk.toNat := by
        have : wk.toNat ≠ 0 := fun hz => hwk0 (BitVec.eq_of_toNat_eq hz)
        omega
      -- Next: `node_invalidate(node); insKinds`
      obtain ⟨s_inv, hinv, hr_kinds⟩ := seq_none_inv hr_inv_kinds
      obtain ⟨ivals, ibody, icallee, iret, irv, ipost, hiargs, hil, hirun, hsinv_eq⟩ :=
        call_void_none_inv hinv
      have hsk_node : sk.locals.lookup (ofString "node") = some (.val (.word wnode)) :=
        (hsk_other _ (by decide)).trans hs_node
      have hivals_eq : ivals = [.val (.word wnode)] := by
        rw [evalListHOLFinite_eq_toExact] at hiargs
        simpa [evalListHOLExact, evalHOLExact, hsk_node] using hiargs.symm
      subst hivals_eq
      have hil_code : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "node_invalidate")
          [.val (.word wnode)] = some (ibody, icallee, iret) := by rwa [← hsc]
      have hnd_inv_lookup : originalRuntimeCode.lookup (ofString "node_invalidate") =
          some ([(ofString "nd", .one)], sourceFnBody Guest.Software.guestFn_node_invalidate, .one) :=
        lookup_of_guestAst_getElem 259 (by rw [guestAst_len]; decide)
          (extractFn Guest.Software.guestFn_node_invalidate) rfl
      obtain ⟨_, hip_nd⟩ := lookup_param_exact hnd_inv_lookup hil_code
        [] "nd" .one [] [] (.val (.word wnode)) [] rfl rfl rfl (by decide)
      have hstep_sk : NodeStep s0 sk Nd0 Nd := hstep.with_locals_clock sk.locals sk.clock
      obtain ⟨Nd_i, hstep_i, _⟩ := nodeStep_of_nodeFn nf_node_invalidate sk hsc
        hstep_sk.arena hstep_sk.heap hil
        (by intro n hn; rw [List.mem_singleton.mp hn]; simp [locN, callEntryStateHOLFinite, hip_nd]; exact Or.inr hnode_in)
        trivial
        (by rw [hirun]; exact Or.inl ⟨irv, rfl⟩)
      rw [hirun] at hstep_i; dsimp only at hstep_i
      subst hsinv_eq
      set si : PanSemStateFiniteExact 64 F := { ipost with locals := sk.locals }
      have hstep_sk_si : NodeStep sk si Nd Nd_i := hstep_i.with_locals_clock sk.locals ipost.clock
      have hstep_s_si : NodeStep s si Nd Nd_i := NodeStep.from_locals_clock hstep_sk_si
      have hstep_si : NodeStep s0 si Nd0 Nd_i := NodeStep.trans ha0 hstep hstep_s_si
      have hsi_code : si.code = originalRuntimeCode := by
        have := (evaluateHOLFiniteState_metadata (callEntryStateHOLFinite sk icallee) ibody).1
        rw [hirun] at this; exact this.trans hsc
      have hnode_in_i : wnode.toNat ∈ Nd_i := hstep_s_si.sub _ hnode_in
      have hnode_kind_i : memW si wnode.toNat = wk.toNat :=
        (hstep_s_si.kinds _ hnode_in).trans hwk_s.symm
      have hkey_i : KeyIn si Nd_i (wkey.toNat + wlevel.toNat) (wklen.toNat - wlevel.toNat) :=
        hstep_s_si.keyIn hstep.arena hstep.heap hkey
      have hsl_inv_i : wslot = 0 ∨ (ValidSlot si Nd_i wslot.toNat ∧ wres.toNat ∈ Nd_i) :=
        hsl_inv.imp id (fun ⟨hv, hrin⟩ => ⟨hv.mono hstep_s_si, hstep_s_si.sub _ hrin⟩)
      -- Now evaluate `insKinds` on `si` (`si.locals = sk.locals`)
      have hsi_k : si.locals.lookup (ofString "k") = some (.val (.word wk)) := hsk_k
      have hsi_node : si.locals.lookup (ofString "node") = some (.val (.word wnode)) := hsk_node
      rw [insKinds_eq, evaluateHOLFiniteState_ite] at hr_kinds
      have hc_k1 : @evalHOLExact 64 F _ si.toExact (fun a => Classical.propDecidable (si.memaddrs a))
          (.cmp .equal (.var .local (ofString "k")) (.const 1)) =
          some (.val (.word (if wk = 1 then 1 else 0))) := by
        simp [evalHOLExact, hsi_k, Compiler.Encoders.Asm.wordCmpHOL]
      rw [hc_k1] at hr_kinds
      by_cases hwk1 : wk = 1
      · -- Kind 1 (`k == 1`): `r = _insert_into_leaf(node, key + level, klen - level, vptr, vlen)`
        rw [if_pos hwk1] at hr_kinds
        simp only [show (1 : BitVec 64) ≠ 0 by decide, ↓reduceIte] at hr_kinds
        obtain ⟨lvals, lbody, lcallee, lret, lrv, lpost, hlargs, hll, hlrun, hu_k_eq⟩ :=
          call_assign_local_none_inv hr_kinds
        have hsi_key : si.locals.lookup (ofString "key") = some (.val (.word wkey)) :=
          (hsk_other _ (by decide)).trans hs_key
        have hsi_level : si.locals.lookup (ofString "level") = some (.val (.word wlevel)) :=
          (hsk_other _ (by decide)).trans hs_level
        have hsi_klen : si.locals.lookup (ofString "klen") = some (.val (.word wklen)) :=
          (hsk_other _ (by decide)).trans hs_klen
        have hsi_vptr : si.locals.lookup (ofString "vptr") = some (.val (.word wvptr)) :=
          (hsk_other _ (by decide)).trans hs_vptr
        have hsi_vlen : si.locals.lookup (ofString "vlen") = some (.val (.word wvlen)) :=
          (hsk_other _ (by decide)).trans hs_vlen
        have hlvals_eq : lvals = [.val (.word wnode), .val (.word (wkey + wlevel)),
            .val (.word (wklen - wlevel)), .val (.word wvptr), .val (.word wvlen)] := by
          rw [evalListHOLFinite_eq_toExact] at hlargs
          simpa [evalListHOLExact, evalHOLExact, hsi_node, hsi_key, hsi_level, hsi_klen, hsi_vptr, hsi_vlen,
            valueIsWord, valueWord, wordOpHOL, wordOp] using hlargs.symm
        subst hlvals_eq
        have hll_code : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "_insert_into_leaf")
            [.val (.word wnode), .val (.word (wkey + wlevel)),
             .val (.word (wklen - wlevel)), .val (.word wvptr), .val (.word wvlen)] =
            some (lbody, lcallee, lret) := by rwa [← hsi_code]
        obtain ⟨_, hlp_nd⟩ := lookup_param_exact lookup__insert_into_leaf hll_code
          [] "node" .one [(ofString "rk", .one), (ofString "rl", .one), (ofString "vptr", .one), (ofString "vlen", .one)]
          [] (.val (.word wnode)) _ rfl rfl rfl (by decide)
        obtain ⟨_, hlp_rk⟩ := lookup_param_exact lookup__insert_into_leaf hll_code
          [(ofString "node", .one)] "rk" .one [(ofString "rl", .one), (ofString "vptr", .one), (ofString "vlen", .one)]
          [_] (.val (.word (wkey + wlevel))) _ rfl rfl rfl (by decide)
        obtain ⟨_, hlp_rl⟩ := lookup_param_exact lookup__insert_into_leaf hll_code
          [(ofString "node", .one), (ofString "rk", .one)] "rl" .one [(ofString "vptr", .one), (ofString "vlen", .one)]
          [_, _] (.val (.word (wklen - wlevel))) _ rfl rfl rfl (by decide)
        obtain ⟨_, hlp_vl⟩ := lookup_param_exact lookup__insert_into_leaf hll_code
          [(ofString "node", .one), (ofString "rk", .one), (ofString "rl", .one), (ofString "vptr", .one)] "vlen" .one []
          [_, _, _, _] (.val (.word wvlen)) [] rfl rfl rfl (by decide)
        obtain ⟨_, hkey_i_bv⟩ := keyIn_suffix_bv hle hkey_i
        have hk1_i : memW si wnode.toNat = 1 := by
          rw [hnode_kind_i, hwk1]; rfl
        obtain ⟨Nd_il, hstep_il, hret_il⟩ := nodeStep_of_nodeFn nf__insert_into_leaf si hsi_code
          hstep_si.arena hstep_si.heap hll
          (by intro n hn; rw [List.mem_singleton.mp hn]; simp [locN, callEntryStateHOLFinite, hlp_nd]; exact Or.inr hnode_in_i)
          (by
            have hln : locN (callEntryStateHOLFinite si lcallee) "node" = wnode.toNat := by
              simp [locN, callEntryStateHOLFinite, hlp_nd]
            refine ⟨⟨by rw [hln]; exact hnode_in_i, by rw [hln]; exact hk1_i⟩,
              by simp [locN, callEntryStateHOLFinite, hlp_rk, hlp_rl]; exact hkey_i_bv,
              by simp [locN, callEntryStateHOLFinite, hlp_vl]; exact hvlt⟩)
          (by rw [hlrun]; exact Or.inl ⟨lrv, rfl⟩)
        rw [hlrun] at hstep_il hret_il; dsimp only at hstep_il hret_il
        obtain ⟨wil, rfl, hwil_root⟩ := hret_il lrv rfl
        subst hu_k_eq
        set sil := setVarHOLFinite (ofString "r") (.val (.word wil)) { lpost with locals := si.locals }
        have hstep_si_sil : NodeStep si sil Nd_i Nd_il := hstep_il.with_locals_clock _ _
        have hsil_code : sil.code = originalRuntimeCode := by
          have := (evaluateHOLFiniteState_metadata (callEntryStateHOLFinite si lcallee) lbody).1
          rw [hlrun] at this; exact this.trans hsi_code
        have hsil_other : ∀ x : MlS, x ≠ ofString "r" → x ≠ ofString "k" → sil.locals.lookup x = s.locals.lookup x := by
          intro x h1 h2
          have hsi_lk : si.locals.lookup x = s.locals.lookup x := hsk_other x h2
          simp [sil, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm h1, hsi_lk]
        exact ⟨Nd_il, wil, 0, 0, 0, 0,
          NodeStep.trans ha0 hstep_si hstep_si_sil, hsil_code,
          (hsil_other _ (by decide) (by decide)).trans hs_key,
          (hsil_other _ (by decide) (by decide)).trans hs_klen,
          (hsil_other _ (by decide) (by decide)).trans hs_vptr,
          (hsil_other _ (by decide) (by decide)).trans hs_vlen,
          (hsil_other _ (by decide) (by decide)).trans hs_slot,
          (hsil_other _ (by decide) (by decide)).trans hs_res,
          by simp [sil, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE],
          (hsil_other _ (by decide) (by decide)).trans hs_nn,
          (hsil_other _ (by decide) (by decide)).trans hs_ns,
          (hsil_other _ (by decide) (by decide)).trans hs_nl,
          (hsil_other _ (by decide) (by decide)).trans hs_go,
          hwil_root,
          hsl_inv_i.imp id (fun ⟨hv, hrin⟩ => ⟨hv.mono hstep_si_sil, hstep_si_sil.sub _ hrin⟩),
          fun h => absurd rfl h⟩
      · -- `k != 1`: check `if k == 2`
        rw [if_neg hwk1] at hr_kinds
        simp only [↓reduceIte] at hr_kinds
        rw [evaluateHOLFiniteState_ite] at hr_kinds
        have hc_k2 : @evalHOLExact 64 F _ si.toExact (fun a => Classical.propDecidable (si.memaddrs a))
            (.cmp .equal (.var .local (ofString "k")) (.const 2)) =
            some (.val (.word (if wk = 2 then 1 else 0))) := by
          simp [evalHOLExact, hsi_k, Compiler.Encoders.Asm.wordCmpHOL]
        rw [hc_k2] at hr_kinds
        by_cases hwk2 : wk = 2
        · -- Kind 2 (`k == 2`): `insExt`
          rw [if_pos hwk2] at hr_kinds
          simp only [show (1 : BitVec 64) ≠ 0 by decide, ↓reduceIte] at hr_kinds
          have hk2_i : memW si wnode.toNat = 2 := by rw [hnode_kind_i, hwk2]; rfl
          exact insExt_step ha0 hstep_si hsi_code hnode_in_i hk2_i hle hvlt hklt hkey_i hsl_inv_i
            ((hsk_other _ (by decide)).trans hs_key)
            ((hsk_other _ (by decide)).trans hs_klen)
            ((hsk_other _ (by decide)).trans hs_vptr)
            ((hsk_other _ (by decide)).trans hs_vlen)
            hsk_node
            ((hsk_other _ (by decide)).trans hs_slot)
            ((hsk_other _ (by decide)).trans hs_level)
            ((hsk_other _ (by decide)).trans hs_res)
            ((hsk_other _ (by decide)).trans hs_nn)
            ((hsk_other _ (by decide)).trans hs_ns)
            ((hsk_other _ (by decide)).trans hs_nl)
            ((hsk_other _ (by decide)).trans hs_go)
            hr_kinds
        · -- Kind 3 (`k == 3`): `insBranch`
          rw [if_neg hwk2] at hr_kinds
          simp only [↓reduceIte] at hr_kinds
          have hwk_ne1 : wk.toNat ≠ 1 := fun h1 => hwk1 (BitVec.eq_of_toNat_eq h1)
          have hwk_ne2 : wk.toNat ≠ 2 := fun h2 => hwk2 (BitVec.eq_of_toNat_eq h2)
          have hk3_i : memW si wnode.toNat = 3 := by omega
          exact insBranch_step ha0 hstep_si hsi_code hnode_in_i hk3_i hle hvlt hklt hkey_i hsl_inv_i
            ((hsk_other _ (by decide)).trans hs_key)
            ((hsk_other _ (by decide)).trans hs_klen)
            ((hsk_other _ (by decide)).trans hs_vptr)
            ((hsk_other _ (by decide)).trans hs_vlen)
            hsk_node
            ((hsk_other _ (by decide)).trans hs_slot)
            ((hsk_other _ (by decide)).trans hs_level)
            ((hsk_other _ (by decide)).trans hs_res)
            ((hsk_other _ (by decide)).trans hs_nn)
            ((hsk_other _ (by decide)).trans hs_ns)
            ((hsk_other _ (by decide)).trans hs_nl)
            ((hsk_other _ (by decide)).trans hs_go)
            hr_kinds

/-- Full one-iteration step of `insBody`: preserves `InsLoopInv`. -/
theorem insBody_step {F : Type} {s0 s t : PanSemStateFiniteExact 64 F} {Nd0 : List Nat}
    {wkey wklen wvptr wvlen : BitVec 64}
    (ha0 : ArenaReady s0)
    (hinv : InsLoopInv s0 Nd0 wkey wklen wvptr wvlen s)
    (hact_go : ∃ wgo, s.locals.lookup (ofString "go") = some (.val (.word wgo)) ∧ wgo ≠ 0)
    (hrun : evaluateHOLFiniteState s insBody = (none, t)) :
    InsLoopInv s0 Nd0 wkey wklen wvptr wvlen t := by
  obtain ⟨hc, hk, hkl, hvp, hvl, hvlt, hklt, wnode, wslot, wlevel, wres, wgo, Nd,
    hnd, hsl, hlv, hrs, hgo, hstep, hr_res, hact⟩ := hinv
  obtain ⟨wgo', hgo', hwgo'_nz⟩ := hact_go
  have hwgo_eq : wgo = wgo' := by rw [hgo] at hgo'; injection hgo' with h1; injection h1 with h2; injection h2
  subst hwgo_eq
  obtain ⟨hle, hnode_root, hkey, hsl_inv⟩ := hact hwgo'_nz
  rw [insBody_eq] at hrun
  obtain ⟨v1, t1, hev1, hr1, ht1⟩ := dec_none_inv hrun
  cases Option.some.inj hev1
  obtain ⟨v2, t2, hev2, hr2, ht2⟩ := dec_none_inv hr1
  cases Option.some.inj hev2
  obtain ⟨v3, t3, hev3, hr3, ht3⟩ := dec_none_inv hr2
  cases Option.some.inj hev3
  obtain ⟨v4, t4, hev4, hr4, ht4⟩ := dec_none_inv hr3
  cases Option.some.inj hev4
  suffices ht4_inv : InsLoopInv s0 Nd0 wkey wklen wvptr wvlen t4 by
    rw [ht1, ht2, ht3, ht4]
    exact (((ht4_inv.restore_local (by decide)).restore_local (by decide)).restore_local (by decide)).restore_local (by decide)
  obtain ⟨s_prep, hgo0, hseq⟩ := seq_none_inv hr4
  have hs_prep_eq := assign_local_eval_inv (w := 0) rfl hgo0
  subst hs_prep_eq
  set sp := setVarHOLFinite (ofString "go") (.val (.word 0))
    (setVarHOLFinite (ofString "next_level") (.val (.word 0))
      (setVarHOLFinite (ofString "next_slot") (.val (.word 0))
        (setVarHOLFinite (ofString "next_node") (.val (.word 0))
          (setVarHOLFinite (ofString "r") (.val (.word 0)) s))))
  obtain ⟨u_sel, hsel, hfin⟩ := seq_none_inv hseq
  have hsp_other : ∀ x : MlS,
      x ≠ ofString "go" → x ≠ ofString "next_level" → x ≠ ofString "next_slot" →
      x ≠ ofString "next_node" → x ≠ ofString "r" →
      sp.locals.lookup x = s.locals.lookup x := by
    intro x h1 h2 h3 h4 h5
    simp [sp, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4, Ne.symm h5]
  have hstep_s_sp : NodeStep s sp Nd Nd :=
    (NodeStep.refl hstep.arena hstep.heap).with_locals_clock sp.locals sp.clock
  have hsel_post := insSelect_step ha0 (hstep.with_locals_clock sp.locals sp.clock) hc
    hnode_root hle hvlt hklt
    (hstep_s_sp.keyIn hstep.arena hstep.heap hkey)
    (hsl_inv.imp id (fun ⟨hv, hrin⟩ => ⟨hv.mono hstep_s_sp, hrin⟩))
    ((hsp_other _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hk)
    ((hsp_other _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hkl)
    ((hsp_other _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hvp)
    ((hsp_other _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hvl)
    ((hsp_other _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hnd)
    ((hsp_other _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hsl)
    ((hsp_other _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hlv)
    ((hsp_other _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hrs)
    (by simp [sp, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
         show ofString "go" ≠ ofString "next_node" by decide,
         show ofString "next_level" ≠ ofString "next_node" by decide,
         show ofString "next_slot" ≠ ofString "next_node" by decide])
    (by simp [sp, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
         show ofString "go" ≠ ofString "next_slot" by decide,
         show ofString "next_level" ≠ ofString "next_slot" by decide])
    (by simp [sp, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
         show ofString "go" ≠ ofString "next_level" by decide])
    (by simp [sp, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
    hsel
  obtain ⟨Nd', wr, wnn, wns, wnl, wgo_u, hst_u, huc, huk, hukl, huvp, huvl, husl, hurs,
    hur, hunn, huns, hunl, hugo, hr_root, husl_inv, hunxt⟩ := hsel_post
  exact insFinish_step ha0 hst_u huc huk hukl huvp huvl hvlt hklt husl hurs hur hunn huns hunl hugo
    hr_root husl_inv hunxt hfin

/-- `insBody` has no top-level `break` or `continue`. -/
theorem insBody_noTopBreak : GuestUniformClockBound.noTopBreak insBody = true := by decide
theorem insBody_noTopContinue : noTopContinue insBody = true := by decide

/-- Helper: no `return` inside `insBody` or its `while` loop. -/
def noReturnProg : ProgHOL 64 → Bool
  | .return _ => false
  | .seq first second => noReturnProg first && noReturnProg second
  | .ite _ yes no => noReturnProg yes && noReturnProg no
  | .dec _ _ _ body => noReturnProg body
  | .decCall _ _ _ _ cont => noReturnProg cont
  | .while _ body => noReturnProg body
  | .skip | .assign _ _ _ | .primitive _ _ _ | .store _ _ | .storeByte _ _ | .store32 _ _
  | .break | .continue | .raise _ _ | .annot _ _ | .call (some (_, none)) _ _ => true
  | _ => false

theorem evaluate_noReturnProg {F : Type} (p : ProgHOL 64) (hp : noReturnProg p = true)
    (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64) :
    (evaluateHOLFiniteState s p).1 ≠ some (.returned v) := by
  cases hshape : p with
  | «return» _ => simp [hshape, noReturnProg] at hp
  | seq a b =>
    have hab : noReturnProg a = true ∧ noReturnProg b = true := by
      simpa only [hshape, noReturnProg, Bool.and_eq_true] using hp
    have hrem := evaluateHOLFiniteState_clock_le s a
    rw [evaluateHOLFiniteState_seq_line780]
    have ha := evaluate_noReturnProg a hab.1 s v
    cases hra : evaluateHOLFiniteState s a with
    | mk r1 mid =>
      rw [hra] at ha hrem
      cases r1 with
      | none => exact evaluate_noReturnProg b hab.2 mid v
      | some _ => exact ha
  | ite c yes no =>
    have hy : noReturnProg yes = true ∧ noReturnProg no = true := by
      simpa only [hshape, noReturnProg, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_noReturnProg no hy.2 s v
      · exact evaluate_noReturnProg yes hy.1 s v
    · simp
  | dec nm sh init body =>
    have hb : noReturnProg body = true := by simpa only [hshape, noReturnProg] using hp
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · simp
    · split
      · exact evaluate_noReturnProg body hb _ v
      · simp
  | decCall nm sh fn args cont =>
    have hc : noReturnProg cont = true := by simpa only [hshape, noReturnProg] using hp
    intro hret
    rw [evaluateHOLFiniteState_decCall_total] at hret
    split at hret
    · simp at hret
    · split at hret
      · simp at hret
      · rename_i vs _ bbody blocals brs _
        split at hret
        · simp at hret
        · have hrem := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite s blocals) bbody
          dsimp only at hret
          rw [fixClockHOLFinite_evaluateState] at hret
          cases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s blocals) bbody with
          | mk r1 bpost =>
            rw [hb] at hrem hret
            rcases r1 with _ | (_ | _ | _ | _ | rv | _ | _)
            all_goals try (simp at hret; done)
            dsimp only at hret
            split at hret
            · have hclk_lt : (setVarHOLFinite nm rv {bpost with locals := s.locals}).clock < s.clock := by
                change bpost.clock < s.clock
                change bpost.clock ≤ s.clock - 1 at hrem
                omega
              exact evaluate_noReturnProg cont hc _ v hret
            · simp at hret
  | «while» cond body =>
    have hb : noReturnProg body = true := by simpa only [hshape, noReturnProg] using hp
    intro hret
    rw [evaluateHOLFiniteState_while_total] at hret
    split at hret
    · split at hret
      · split at hret
        · simp at hret
        · dsimp only at hret
          rw [fixClockHOLFinite_evaluateState] at hret
          have hrem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
          cases hbr : evaluateHOLFiniteState (decClockHOLFinite s) body with
          | mk r1 mid =>
            rw [hbr] at hret hrem
            have hclk_lt : mid.clock < s.clock := by
              change mid.clock ≤ s.clock - 1 at hrem
              omega
            cases r1 with
            | none => exact evaluate_noReturnProg (.while cond body) (by simpa [noReturnProg] using hb) mid v hret
            | some r1' =>
              cases r1' with
              | «continue» =>
                exact evaluate_noReturnProg (.while cond body) (by simpa [noReturnProg] using hb) mid v hret
              | «break» => simp at hret
              | returned rv =>
                have hno := evaluate_noReturnProg body hb (decClockHOLFinite s) rv
                rw [hbr] at hno
                exact hno rfl
              | _ => simp at hret
      · simp at hret
    · simp at hret
  | skip => simp [evaluateHOLFiniteState_skip]
  | «break» => simp [evaluateHOLFiniteState_break]
  | «continue» => simp [evaluateHOLFiniteState_continue]
  | annot _ _ => simp [evaluateHOLFiniteState_annot]
  | raise _ _ =>
    rw [evaluateHOLFiniteState_raise]; split
    · dsimp only; split <;> simp
    · simp
  | assign _ _ _ => rw [evaluateHOLFiniteState_assign]; repeat' first | split | simp
  | primitive _ _ _ => rw [evaluateHOLFiniteState_primitive]; repeat' first | split | simp
  | store a e =>
    rcases (PanRunBounded.evaluate_store_control_frame s a e).1 with h | h <;> (rw [h]; simp)
  | storeByte a e =>
    rcases (PanRunBounded.evaluate_storeByte_control_frame s a e).1 with h | h <;> (rw [h]; simp)
  | store32 _ _ => rw [evaluateHOLFiniteState_store32]; repeat' first | split | simp
  | call info fn args =>
    rcases info with _ | ⟨dest, _ | _⟩
    · simp [hshape, noReturnProg] at hp
    · intro hret
      rw [evaluateHOLFiniteState_call] at hret
      split at hret
      · simp at hret
      · split at hret
        · simp at hret
        · split at hret
          · simp at hret
          · rename_i vs _ bbody blocals brs _ _
            rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s blocals) bbody with ⟨r1, bpost⟩
            rw [hb] at hret
            rcases r1 with _ | r1'
            · simp at hret
            · cases r1' with
              | returned rv =>
                dsimp only at hret
                split at hret
                · rcases dest with _ | ⟨knd, dnm⟩
                  · simp at hret
                  · dsimp only at hret; split at hret <;> simp at hret
                · simp at hret
              | _ => simp at hret
    · simp [hshape, noReturnProg] at hp
  | _ => simp [hshape, noReturnProg] at hp
termination_by (s.clock, sizeOf p)
decreasing_by all_goals (simp_all [decClockHOLFinite, setVarHOLFinite]; omega)

/-- Strong induction on clock for the `while go != 0` loop of `_mpt_insert_node`. -/
theorem insWhile_inv {F : Type}
    {s0 s post : PanSemStateFiniteExact 64 F} {Nd0 : List Nat}
    {wkey wklen wvptr wvlen : BitVec 64}
    (ha0 : ArenaReady s0)
    (hinv : InsLoopInv s0 Nd0 wkey wklen wvptr wvlen s)
    (hr : evaluateHOLFiniteState s (.while (.cmp .notEqual (.var .local (ofString "go")) (.const 0)) insBody) =
      (none, post)) :
    InsLoopInv s0 Nd0 wkey wklen wvptr wvlen post := by
  generalize hk_clk : s.clock = k
  induction k using Nat.strongRecOn generalizing s with
  | ind k ih =>
    have hinv_copy := hinv
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, wgo, _, _, _, _, _, hgo_lk, _⟩ := hinv_copy
    rw [evaluateHOLFiniteState_while_total] at hr
    have hc_ev : s.evalHOLFinite (h := fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .notEqual (.var .local (ofString "go")) (.const 0)) =
        some (.val (.word (if wgo ≠ 0 then 1 else 0))) := by
      rw [evalHOLFinite_eq_toExact]
      simp [evalHOLExact, hgo_lk, Compiler.Encoders.Asm.wordCmpHOL]
    rw [hc_ev] at hr
    by_cases hwgo : wgo ≠ 0
    · rw [if_pos hwgo] at hr
      have h1_nz : (1 : BitVec 64) ≠ 0 := by decide
      dsimp only at hr
      rw [if_pos h1_nz] at hr
      split at hr
      · simp at hr
      · rename_i hclk_nz
        rw [fixClockHOLFinite_evaluateState] at hr
        have hrem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) insBody
        have hnb := GuestUniformClockBound.evaluate_noTopBreak insBody insBody_noTopBreak (decClockHOLFinite s)
        have hnc := evaluate_noTopContinue insBody insBody_noTopContinue (decClockHOLFinite s)
        rcases hb : evaluateHOLFiniteState (decClockHOLFinite s) insBody with ⟨rb, mid⟩
        rw [hb] at hr hrem hnb hnc
        have hlt : mid.clock < k := by
          change mid.clock ≤ s.clock - 1 at hrem
          omega
        cases rb with
        | none =>
          have hmid_inv := insBody_step ha0 hinv.decClock ⟨wgo, hgo_lk, hwgo⟩ hb
          exact ih mid.clock hlt hmid_inv hr rfl
        | some rb' =>
          cases rb' with
          | «continue» => exact absurd rfl hnc
          | «break» => exact absurd rfl hnb
          | _ => simp at hr
    · rw [if_neg hwgo] at hr
      dsimp only at hr
      have h0_not_nz : ¬ ((0 : BitVec 64) ≠ 0) := by simp
      rw [if_neg h0_not_nz] at hr
      injection hr with _ hpost_eq
      subst hpost_eq
      exact hinv

/-- `_mpt_insert_node` contract (`ContractParts/C00.lean:247`). -/
theorem mpt_insert_node_spec_proof :
    FunSpec MptInsertReady_spec MptExit_spec (ofString "_mpt_insert_node") := by
  refine ⟨_, _, _, lookup__mpt_insert_node, ?_⟩
  intro F s hcode hP ⟨callVals, hcallL⟩ _hnt v hret
  obtain ⟨⟨hAR, hlev_le, Nd0, hNd0, hroot0, hkey0, hklen_le⟩, hvlen_lt⟩ := hP
  obtain ⟨wnode, hlk_node, hloc_node⟩ := lookup_param_word lookup__mpt_insert_node hcallL
    [] "node" [(ofString "key", .one), (ofString "klen", .one), (ofString "level", .one), (ofString "vptr", .one), (ofString "vlen", .one)]
    rfl (by decide)
  obtain ⟨wkey, hlk_key, hloc_key⟩ := lookup_param_word lookup__mpt_insert_node hcallL
    [(ofString "node", .one)] "key" [(ofString "klen", .one), (ofString "level", .one), (ofString "vptr", .one), (ofString "vlen", .one)]
    rfl (by decide)
  obtain ⟨wklen, hlk_klen, hloc_klen⟩ := lookup_param_word lookup__mpt_insert_node hcallL
    [(ofString "node", .one), (ofString "key", .one)] "klen" [(ofString "level", .one), (ofString "vptr", .one), (ofString "vlen", .one)]
    rfl (by decide)
  obtain ⟨wlevel, hlk_level, hloc_level⟩ := lookup_param_word lookup__mpt_insert_node hcallL
    [(ofString "node", .one), (ofString "key", .one), (ofString "klen", .one)] "level" [(ofString "vptr", .one), (ofString "vlen", .one)]
    rfl (by decide)
  obtain ⟨wvptr, hlk_vptr, _⟩ := lookup_param_word lookup__mpt_insert_node hcallL
    [(ofString "node", .one), (ofString "key", .one), (ofString "klen", .one), (ofString "level", .one)] "vptr" [(ofString "vlen", .one)]
    rfl (by decide)
  obtain ⟨wvlen, hlk_vlen, hloc_vlen⟩ := lookup_param_word lookup__mpt_insert_node hcallL
    [(ofString "node", .one), (ofString "key", .one), (ofString "klen", .one), (ofString "level", .one), (ofString "vptr", .one)] "vlen" []
    rfl (by decide)
  change (evaluateHOLFiniteState s insFnCode).1 = some (.returned v) at hret
  set post := (evaluateHOLFiniteState s insFnCode).2
  -- Unfold the 3 outer declarations: `result := 0`, `slot := 0`, `go := 1`
  set s_init := setVarHOLFinite (ofString "go") (.val (.word 1))
    (setVarHOLFinite (ofString "slot") (.val (.word 0))
      (setVarHOLFinite (ofString "result") (.val (.word 0)) s))
  set loop_ret : ProgHOL 64 :=
    .seq (.while (.cmp .notEqual (.var .local (ofString "go")) (.const 0)) insBody)
      (.return (.var .local (ofString "result")))
  have hinit_eq : (evaluateHOLFiniteState s insFnCode).1 = (evaluateHOLFiniteState s_init loop_ret).1 ∧
      post = { (evaluateHOLFiniteState s_init loop_ret).2 with
        locals := HolFiniteMapExact.resVarEq
          (HolFiniteMapExact.resVarEq
            (HolFiniteMapExact.resVarEq (evaluateHOLFiniteState s_init loop_ret).2.locals
              (ofString "go", (setVarHOLFinite (ofString "slot") (.val (.word 0))
                (setVarHOLFinite (ofString "result") (.val (.word 0)) s)).locals.lookup (ofString "go")))
            (ofString "slot", (setVarHOLFinite (ofString "result") (.val (.word 0)) s).locals.lookup (ofString "slot")))
          (ofString "result", s.locals.lookup (ofString "result")) } := by
    have hsh0 : shapeEqHOL .one (shapeOfHOLExact (.val (.word (0 : BitVec 64)))) = true := by
      simp [shapeEqHOL, shapeOfHOLExact]
    have hsh1 : shapeEqHOL .one (shapeOfHOLExact (.val (.word (1 : BitVec 64)))) = true := by
      simp [shapeEqHOL, shapeOfHOLExact]
    have hd : evaluateHOLFiniteState s insFnCode =
        ((evaluateHOLFiniteState s_init loop_ret).1,
         { (evaluateHOLFiniteState s_init loop_ret).2 with
           locals := HolFiniteMapExact.resVarEq
             (HolFiniteMapExact.resVarEq
               (HolFiniteMapExact.resVarEq (evaluateHOLFiniteState s_init loop_ret).2.locals
                 (ofString "go", (setVarHOLFinite (ofString "slot") (.val (.word 0))
                   (setVarHOLFinite (ofString "result") (.val (.word 0)) s)).locals.lookup (ofString "go")))
               (ofString "slot", (setVarHOLFinite (ofString "result") (.val (.word 0)) s).locals.lookup (ofString "slot")))
             (ofString "result", s.locals.lookup (ofString "result")) }) := by
      rw [insFn_eq, evaluateHOLFiniteState_dec_total]
      dsimp only [evalHOLExact]; rw [if_pos hsh0]
      rw [evaluateHOLFiniteState_dec_total]
      dsimp only [evalHOLExact]; rw [if_pos hsh0]
      rw [evaluateHOLFiniteState_dec_total]
      dsimp only [evalHOLExact]; rw [if_pos hsh1]
    exact ⟨by rw [hd], by dsimp only [post]; rw [hd]⟩
  have hseq_eval := evaluateHOLFiniteState_seq_line780 s_init
    (.while (.cmp .notEqual (.var .local (ofString "go")) (.const 0)) insBody)
    (.return (.var .local (ofString "result")))
  change evaluateHOLFiniteState s_init loop_ret = _ at hseq_eval
  rcases hloop : evaluateHOLFiniteState s_init
      (.while (.cmp .notEqual (.var .local (ofString "go")) (.const 0)) insBody) with ⟨rl, mid⟩
  rw [hloop] at hseq_eval
  rw [hinit_eq.1, hseq_eval] at hret
  cases rl with
  | some rl' =>
    dsimp only at hret
    injection hret with hrl; subst hrl
    have hno_ret := evaluate_noReturnProg
      (.while (.cmp .notEqual (.var .local (ofString "go")) (.const 0)) insBody) (by decide) s_init v
    exact absurd (congrArg Prod.fst hloop) hno_ret
  | none =>
    dsimp only at hret hseq_eval
    have hsinit_other : ∀ x : MlS, x ≠ ofString "go" → x ≠ ofString "slot" → x ≠ ofString "result" →
        s_init.locals.lookup x = s.locals.lookup x := by
      intro x h1 h2 h3
      simp [s_init, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm h1, Ne.symm h2, Ne.symm h3]
    have hinv_init : InsLoopInv s Nd0 wkey wklen wvptr wvlen s_init := by
      refine ⟨hcode,
        (hsinit_other _ (by decide) (by decide) (by decide)).trans hlk_key,
        (hsinit_other _ (by decide) (by decide) (by decide)).trans hlk_klen,
        (hsinit_other _ (by decide) (by decide) (by decide)).trans hlk_vptr,
        (hsinit_other _ (by decide) (by decide) (by decide)).trans hlk_vlen,
        by rwa [← hloc_vlen s rfl],
        by rwa [← hloc_klen s rfl],
        wnode, 0, wlevel, 0, 1, Nd0,
        (hsinit_other _ (by decide) (by decide) (by decide)).trans hlk_node,
        by simp [s_init, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
             show ofString "go" ≠ ofString "slot" by decide],
        (hsinit_other _ (by decide) (by decide) (by decide)).trans hlk_level,
        by simp [s_init, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
             show ofString "go" ≠ ofString "result" by decide,
             show ofString "slot" ≠ ofString "result" by decide],
        by simp [s_init, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE],
        (NodeStep.refl hAR hNd0).with_locals_clock s_init.locals s_init.clock,
        Or.inl rfl,
        ?_⟩
      intro _
      refine ⟨by rwa [← hloc_level s rfl, ← hloc_klen s rfl],
        by rwa [← hloc_node s rfl],
        by rwa [← hloc_key s rfl, ← hloc_level s rfl, ← hloc_klen s rfl],
        Or.inl rfl⟩
    have hinv_mid := insWhile_inv hAR hinv_init hloop
    obtain ⟨_, _, _, _, _, _, _, _, _, _, wres_m, _, Nd_m, _, _, _, hmid_res, _, hstep_mid, hres_root, _⟩ := hinv_mid
    have hret_mid : evaluateHOLFiniteState mid (.return (.var .local (ofString "result"))) =
        (some (.returned (.val (.word wres_m))), emptyLocalsHOLFinite mid) := by
      simp [evaluateHOLFiniteState_return, evalHOLExact, hmid_res, shapeOfHOLExact, sizeOfShapeWithContextHOL]
    rw [hret_mid] at hret hseq_eval
    injection hret with hv1; injection hv1 with hv2; subst hv2
    have hstep_post : NodeStep s post Nd0 Nd_m := by
      rw [hinit_eq.2, hseq_eval]
      exact hstep_mid.with_locals_clock _ mid.clock
    exact ⟨wres_m, rfl, hstep_post.arena, hstep_post.hp_le, hstep_post.globals,
      Nd0, Nd_m, hNd0, hroot0, hstep_post.heap, hres_root, hstep_post.frame⟩

end InitECandidate.Solver.Wave8GuestInv.R16Shards
