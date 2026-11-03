import InitECandidate.Solver.Wave8GuestInv.R16Shards.NfNodeNewLeaf
import InitECandidate.Solver.Wave8GuestInv.R16Shards.NfNodeNewExt

/-! `nf__split_extension`: `_split_extension(node, rk, rl, vptr, vlen, pl)` preserves typed node heaps
(`NodeFn ["node"]`). -/

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

private theorem node_new_leaf_no_nonTrap_exn {F : Type}
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

private theorem node_new_ext_no_nonTrap_exn {F : Type}
    (st : PanSemStateFiniteExact 64 F) (hcode : st.code = originalRuntimeCode)
    (eid : MlS) (ev : ValueHOL 64) (hne : eid ≠ ofString "TrapErr") :
    (evaluateHOLFiniteState st (sourceFnBody Guest.Software.guestFn_node_new_ext)).1 ≠
      some (.exception eid ev) := by
  intro hexn
  have hbody : sourceFnBody Guest.Software.guestFn_node_new_ext =
      .decCall (ofString "nd") .one (ofString "alloc") [.const 56]
        (.seq (.store (.op .add [.var .local (ofString "nd"), .const 0]) (.const 2))
          (.seq (.store (.op .add [.var .local (ofString "nd"), .const 8]) (.const 0))
            (.seq (.store (.op .add [.var .local (ofString "nd"), .const 16]) (.const 0))
              (.seq (.store (.op .add [.var .local (ofString "nd"), .const 24]) (.const 0))
                (.seq (.store (.op .add [.var .local (ofString "nd"), .const 32]) (.var .local (ofString "nib")))
                  (.seq (.store (.op .add [.var .local (ofString "nd"), .const 40]) (.var .local (ofString "nlen")))
                    (.seq (.store (.op .add [.var .local (ofString "nd"), .const 48]) (.var .local (ofString "child")))
                      (.return (.var .local (ofString "nd")))))))))) := rfl
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

/-- Helper evaluating `br + 32 + idx * 8` when `idx` comes from `loadByte (seg + pl)`. -/
private theorem eval_slot_loadByte_add {F : Type}
    {st : PanSemStateFiniteExact 64 F} {segn pln : String}
    {wbr wseg wpl idx : BitVec 64}
    (hl_br : st.locals.lookup (ofString "br") = some (.val (.word wbr)))
    (hl_seg : st.locals.lookup (ofString segn) = some (.val (.word wseg)))
    (hl_pl : st.locals.lookup (ofString pln) = some (.val (.word wpl)))
    (hlb : @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a))
      (.loadByte (.op .add [.var .local (ofString segn), .var .local (ofString pln)])) =
      some (.val (.word idx))) :
    @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a))
      (.op .add [.var .local (ofString "br"), .const (BitVec.ofNat 64 32),
        .panop .mul [.loadByte (.op .add [.var .local (ofString segn), .var .local (ofString pln)]),
          .const (BitVec.ofNat 64 8)]]) =
      some (.val (.word (wbr + BitVec.ofNat 64 32 + idx * BitVec.ofNat 64 8))) := by
  obtain ⟨b, hb_mem, rfl⟩ : ∃ b : UInt8,
      @panMemLoadByteHOL 64 _ st.memory st.memaddrs
        (fun a => Classical.propDecidable (st.memaddrs a)) st.be (wseg + wpl) = some b ∧
      BitVec.ofNat 64 b.toNat = idx := by
    simpa [evalHOLExact, evalListHOLExact, hl_seg, hl_pl,
      valueIsWord, valueWord, wordOpHOL, wordOp] using hlb
  have hadd0 : ∀ u : BitVec 64, u + (0 : BitVec 64) = u := BitVec.add_zero
  simp only [evalHOLExact, evalListHOLExact, hl_br, hl_seg, hl_pl,
    valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL, List.all, List.map, Option.map,
    Bool.and_self, ↓reduceIte, List.foldr, hadd0]
  rw [hb_mem]
  simp only [Option.map, valueIsWord, valueWord, List.all, List.map, Bool.and_self, ↓reduceIte, List.foldr, hadd0]
  congr 3
  exact (BitVec.add_assoc wbr (BitVec.ofNat 64 32) (BitVec.ofNat 64 b.toNat * BitVec.ofNat 64 8)).symm

/-- Helper evaluating `br + 32 + idx * 8` when `idx` is a local variable. -/
private theorem eval_slot_var {F : Type}
    {st : PanSemStateFiniteExact 64 F} {idxn : String}
    {wbr idx : BitVec 64}
    (hl_br : st.locals.lookup (ofString "br") = some (.val (.word wbr)))
    (hl_idx : st.locals.lookup (ofString idxn) = some (.val (.word idx))) :
    @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a))
      (.op .add [.var .local (ofString "br"), .const (BitVec.ofNat 64 32),
        .panop .mul [.var .local (ofString idxn), .const (BitVec.ofNat 64 8)]]) =
      some (.val (.word (wbr + BitVec.ofNat 64 32 + idx * BitVec.ofNat 64 8))) := by
  simp only [evalHOLExact, evalListHOLExact, hl_br, hl_idx,
    valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL, List.all, List.map, Option.map,
    Bool.and_self, ↓reduceIte, List.foldr]
  congr 3
  have hadd0 : ∀ u : BitVec 64, u + (0 : BitVec 64) = u := BitVec.add_zero
  rw [hadd0]
  exact (BitVec.add_assoc wbr (BitVec.ofNat 64 32) (idx * BitVec.ofNat 64 8)).symm

/-- `_split_extension` (AST line 10561): typed nodes in, typed nodes out (MPT tier);
requirement:
`NodeKind s Nd "node" 2 ∧ KeyIn s Nd (locN s "rk") (locN s "rl") ∧
 locN s "vlen" < 2 ^ 40 ∧ locN s "pl" < memW s (locN s "node" + 40) ∧ locN s "pl" ≤ locN s "rl"`. -/
theorem «nf__split_extension» :
    NodeFn ["node"]
    (fun s Nd =>
      NodeKind s Nd "node" 2 ∧ KeyIn s Nd (locN s "rk") (locN s "rl") ∧
      locN s "vlen" < 2 ^ 40 ∧ locN s "pl" < memW s (locN s "node" + 40) ∧ locN s "pl" ≤ locN s "rl")
    (ofString "_split_extension") := by
  refine ⟨_, _, _, lookup__split_extension, ?_⟩
  intro F s hcode hP ⟨callVals, hcallL⟩ _hnt hres
  have hAR : ArenaReady s := hP.1
  obtain ⟨Nd_wit, hNd_wit, _, hnk_wit, hkrk_wit, hvlen_wit, hpl_sl_wit, hpl_rl_wit⟩ := hP.2
  obtain ⟨wnode, hlk_node, hloc_node⟩ := lookup_param_word lookup__split_extension hcallL
    [] "node" [(ofString "rk", .one), (ofString "rl", .one), (ofString "vptr", .one), (ofString "vlen", .one), (ofString "pl", .one)]
    rfl (by decide)
  obtain ⟨wrk, hlk_rk, hloc_rk⟩ := lookup_param_word lookup__split_extension hcallL
    [(ofString "node", .one)] "rk" [(ofString "rl", .one), (ofString "vptr", .one), (ofString "vlen", .one), (ofString "pl", .one)]
    rfl (by decide)
  obtain ⟨wrl, hlk_rl, hloc_rl⟩ := lookup_param_word lookup__split_extension hcallL
    [(ofString "node", .one), (ofString "rk", .one)] "rl" [(ofString "vptr", .one), (ofString "vlen", .one), (ofString "pl", .one)]
    rfl (by decide)
  obtain ⟨wvptr, hlk_vptr, hloc_vptr⟩ := lookup_param_word lookup__split_extension hcallL
    [(ofString "node", .one), (ofString "rk", .one), (ofString "rl", .one)] "vptr" [(ofString "vlen", .one), (ofString "pl", .one)]
    rfl (by decide)
  obtain ⟨wvlen, hlk_vlen, hloc_vlen⟩ := lookup_param_word lookup__split_extension hcallL
    [(ofString "node", .one), (ofString "rk", .one), (ofString "rl", .one), (ofString "vptr", .one)] "vlen" [(ofString "pl", .one)]
    rfl (by decide)
  obtain ⟨wpl, hlk_pl, hloc_pl⟩ := lookup_param_word lookup__split_extension hcallL
    [(ofString "node", .one), (ofString "rk", .one), (ofString "rl", .one), (ofString "vptr", .one), (ofString "vlen", .one)] "pl" []
    rfl (by decide)
  have hwnode_in_wit : wnode.toNat ∈ Nd_wit := by rw [← hloc_node s rfl]; exact hnk_wit.1
  have hwnode_k2 : memW s wnode.toNat = 2 := by rw [← hloc_node s rfl]; exact hnk_wit.2
  have hp_wit := hNd_wit.1 wnode.toNat hwnode_in_wit
  have hhl_lt : heapLimit < 2 ^ 64 := by decide
  have hnode_lt : wnode.toNat + 56 ≤ heapLimit := by
    have := hp_wit.2.2.1.2; dsimp [nodeIvl] at this; rw [hwnode_k2] at this; dsimp [nodeSize] at this; omega
  have hnode_add : ∀ k : Nat, k ≤ 48 → wnode + BitVec.ofNat 64 k = BitVec.ofNat 64 (wnode.toNat + k) ∧
      (wnode + BitVec.ofNat 64 k).toNat = wnode.toNat + k := by
    intro k hk
    have hlt : wnode.toNat + k < 2 ^ 64 := by omega
    have heq : wnode + BitVec.ofNat 64 k = BitVec.ofNat 64 (wnode.toNat + k) := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    exact ⟨heq, by rw [heq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]⟩
  have hload_node_off : ∀ (st : PanSemStateFiniteExact 64 F) (k : Nat),
      st.memory = s.memory → st.memaddrs = s.memaddrs →
      st.locals.lookup (ofString "node") = some (.val (.word wnode)) →
      k < 56 → k % 8 = 0 →
      @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a))
        (.load .one (.op .add [.var .local (ofString "node"), .const (BitVec.ofNat 64 k)])) =
        some (.val (.word (BitVec.ofNat 64 (memW s (wnode.toNat + k))))) := by
    intro st k hmem hma hnd hk hk8
    have hsz2 : nodeSize (memW s wnode.toNat) = 56 := by simp [nodeSize, hwnode_k2]
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
  set wseg : BitVec 64 := BitVec.ofNat 64 (memW s (wnode.toNat + 32))
  set wsl : BitVec 64 := BitVec.ofNat 64 (memW s (wnode.toNat + 40))
  set wchild : BitVec 64 := BitVec.ofNat 64 (memW s (wnode.toNat + 48))
  have hwseg_nat : wseg.toNat = memW s (wnode.toNat + 32) := by
    dsimp [wseg]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold memW; rcases s.memory _ with ⟨w⟩; exact w.isLt)]
  have hwsl_nat : wsl.toNat = memW s (wnode.toNat + 40) := by
    dsimp [wsl]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold memW; rcases s.memory _ with ⟨w⟩; exact w.isLt)]
  have hwchild_nat : wchild.toNat = memW s (wnode.toNat + 48) := by
    dsimp [wchild]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold memW; rcases s.memory _ with ⟨w⟩; exact w.isLt)]
  set res := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn__split_extension)).1
  set post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn__split_extension)).2
  suffices hmain : ∀ Nd, NodeHeap s Nd → NodeKind s Nd "node" 2 →
      KeyIn s Nd (locN s "rk") (locN s "rl") → locN s "vlen" < 2 ^ 40 →
      locN s "pl" < memW s (locN s "node" + 40) → locN s "pl" ≤ locN s "rl" →
      ∃ Nd', NodeStep s post Nd Nd' ∧
        ∀ v, res = some (.returned v) → ∃ w : BitVec 64, v = .val (.word w) ∧ RootIn Nd' w.toNat by
    obtain ⟨Nd0', hns0, _⟩ := hmain Nd_wit hNd_wit hnk_wit hkrk_wit hvlen_wit hpl_sl_wit hpl_rl_wit
    refine ⟨hns0.arena, hns0.hp_le, hns0.sp_le, ?_⟩
    intro Nd hNd _ ⟨hnk, hkrk, hvlen, hpl_sl, hpl_rl⟩
    obtain ⟨Nd', hns, hret⟩ := hmain Nd hNd hnk hkrk hvlen hpl_sl hpl_rl
    exact ⟨Nd', hns.heap, hns.sub, hns.kinds, hns.fresh, hns.frame, hns.globals, hret⟩
  intro Nd hNd hnk hkrk hvlen_lt hpl_sl hpl_rl
  have hnode_in : wnode.toNat ∈ Nd := by rw [← hloc_node s rfl]; exact hnk.1
  have hnode_k2 : memW s wnode.toNat = 2 := by rw [← hloc_node s rfl]; exact hnk.2
  have hp_nd := hNd.1 wnode.toNat hnode_in
  have hkey_seg : KeyIn s Nd wseg.toNat wsl.toNat := by
    rw [hwseg_nat, hwsl_nat]
    exact hp_nd.2.2.2.2.2.2.1 (Or.inr hnode_k2)
  have hchild_root : RootIn Nd wchild.toNat := by
    rw [hwchild_nat]
    exact hp_nd.2.2.2.2.1 hnode_k2
  have hkey_rk : KeyIn s Nd wrk.toNat wrl.toNat := by
    rwa [hloc_rk s rfl, hloc_rl s rfl] at hkrk
  have hwvlen_lt : wvlen.toNat < 2 ^ 40 := by
    rwa [hloc_vlen s rfl] at hvlen_lt
  have hwpl_lt_wsl : wpl.toNat < wsl.toNat := by
    rw [← hloc_pl s rfl, hwsl_nat, ← hloc_node s rfl]
    exact hpl_sl
  have hwpl_le_wrl : wpl.toNat ≤ wrl.toNat := by
    rwa [hloc_pl s rfl, hloc_rl s rfl] at hpl_rl
  -- Unfold the 3 outer `dec` bindings (`seg`, `sl`, `child`)
  set s_seg := setVarHOLFinite (ofString "seg") (.val (.word wseg)) s
  set s_sl := setVarHOLFinite (ofString "sl") (.val (.word wsl)) s_seg
  set s_ch := setVarHOLFinite (ofString "child") (.val (.word wchild)) s_sl
  have hsseg_node : s_seg.locals.lookup (ofString "node") = some (.val (.word wnode)) := by
    simp [s_seg, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlk_node,
      show ofString "seg" ≠ ofString "node" by decide]
  have hssl_node : s_sl.locals.lookup (ofString "node") = some (.val (.word wnode)) := by
    simp [s_sl, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsseg_node,
      show ofString "sl" ≠ ofString "node" by decide]
  have hsch_other : ∀ x : MlS, x ≠ ofString "seg" → x ≠ ofString "sl" → x ≠ ofString "child" →
      s_ch.locals.lookup x = s.locals.lookup x := by
    intro x h1 h2 h3
    simp [s_ch, s_sl, s_seg, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      Ne.symm h1, Ne.symm h2, Ne.symm h3]
  have hsch_seg : s_ch.locals.lookup (ofString "seg") = some (.val (.word wseg)) := by
    simp [s_ch, s_sl, s_seg, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "child" ≠ ofString "seg" by decide, show ofString "sl" ≠ ofString "seg" by decide]
  have hsch_sl : s_ch.locals.lookup (ofString "sl") = some (.val (.word wsl)) := by
    simp [s_ch, s_sl, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "child" ≠ ofString "sl" by decide]
  have hsch_child : s_ch.locals.lookup (ofString "child") = some (.val (.word wchild)) := by
    simp [s_ch, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  set sal_ite1 : ProgHOL 64 :=
    .ite (.cmp .equal (.var .local (ofString "sal")) (.const (BitVec.ofNat 64 1)))
      (.store (.op .add [.var .local (ofString "br"), .const (BitVec.ofNat 64 32),
          .panop .mul [.loadByte (.op .add [.var .local (ofString "seg"), .var .local (ofString "pl")]),
            .const (BitVec.ofNat 64 8)]])
        (.var .local (ofString "child")))
      .skip
  set sal_ite2 : ProgHOL 64 :=
    .ite (.cmp .lower (.const (BitVec.ofNat 64 1)) (.var .local (ofString "sal")))
      (.decCall (ofString "ex") .one (ofString "node_new_ext")
        [.op .add [.var .local (ofString "seg"), .var .local (ofString "pl"), .const (BitVec.ofNat 64 1)],
         .op .sub [.var .local (ofString "sal"), .const (BitVec.ofNat 64 1)],
         .var .local (ofString "child")]
        (.store (.op .add [.var .local (ofString "br"), .const (BitVec.ofNat 64 32),
            .panop .mul [.loadByte (.op .add [.var .local (ofString "seg"), .var .local (ofString "pl")]),
              .const (BitVec.ofNat 64 8)]])
          (.var .local (ofString "ex"))))
      .skip
  set kal_ite : ProgHOL 64 :=
    .ite (.cmp .equal (.var .local (ofString "kal")) (.const (BitVec.ofNat 64 0)))
      (.seq
        (.store (.op .add [.var .local (ofString "br"), .const (BitVec.ofNat 64 160)]) (.var .local (ofString "vptr")))
        (.store (.op .add [.var .local (ofString "br"), .const (BitVec.ofNat 64 168)]) (.var .local (ofString "vlen"))))
      (.dec (ofString "idx") .one
        (.loadByte (.op .add [.var .local (ofString "rk"), .var .local (ofString "pl")]))
        (.seq
          (.ite (.cmp .notEqual
              (.load .one (.op .add [.var .local (ofString "br"), .const (BitVec.ofNat 64 32),
                .panop .mul [.var .local (ofString "idx"), .const (BitVec.ofNat 64 8)]]))
              (.const (BitVec.ofNat 64 0)))
            (.call (some (none, none)) (ofString "mpt_fail") [.const (BitVec.ofNat 64 11)])
            .skip)
          (.decCall (ofString "lf") .one (ofString "node_new_leaf")
            [.op .add [.var .local (ofString "rk"), .var .local (ofString "pl"), .const (BitVec.ofNat 64 1)],
             .op .sub [.var .local (ofString "kal"), .const (BitVec.ofNat 64 1)],
             .var .local (ofString "vptr"),
             .var .local (ofString "vlen")]
            (.store (.op .add [.var .local (ofString "br"), .const (BitVec.ofNat 64 32),
                .panop .mul [.var .local (ofString "idx"), .const (BitVec.ofNat 64 8)]])
              (.var .local (ofString "lf"))))))
  set br_prog : ProgHOL 64 :=
    .decCall (ofString "br") .one (ofString "node_new_branch") []
      (.dec (ofString "sal") .one (.op .sub [.var .local (ofString "sl"), .var .local (ofString "pl")])
        (.seq sal_ite1
          (.seq sal_ite2
            (.dec (ofString "kal") .one (.op .sub [.var .local (ofString "rl"), .var .local (ofString "pl")])
              (.seq kal_ite (.return (.var .local (ofString "br"))))))))
  have hbody : sourceFnBody Guest.Software.guestFn__split_extension =
      .dec (ofString "seg") .one (.load .one (.op .add [.var .local (ofString "node"), .const (BitVec.ofNat 64 32)]))
        (.dec (ofString "sl") .one (.load .one (.op .add [.var .local (ofString "node"), .const (BitVec.ofNat 64 40)]))
          (.dec (ofString "child") .one (.load .one (.op .add [.var .local (ofString "node"), .const (BitVec.ofNat 64 48)]))
            br_prog)) := rfl
  have hdec3_unfold : res = (evaluateHOLFiniteState s_ch br_prog).1 ∧
      post = { (evaluateHOLFiniteState s_ch br_prog).2 with
        locals := HolFiniteMapExact.resVarEq
          (HolFiniteMapExact.resVarEq
            (HolFiniteMapExact.resVarEq (evaluateHOLFiniteState s_ch br_prog).2.locals
              (ofString "child", s_sl.locals.lookup (ofString "child")))
            (ofString "sl", s_seg.locals.lookup (ofString "sl")))
          (ofString "seg", s.locals.lookup (ofString "seg")) } := by
    have he1 := hload_node_off s 32 rfl rfl hlk_node (by decide) (by decide)
    have he2 := hload_node_off s_seg 40 rfl rfl hsseg_node (by decide) (by decide)
    have he3 := hload_node_off s_sl 48 rfl rfl hssl_node (by decide) (by decide)
    have hsh1 : shapeEqHOL .one (shapeOfHOLExact (.val (.word wseg))) = true := by simp [shapeEqHOL, shapeOfHOLExact]
    have hsh2 : shapeEqHOL .one (shapeOfHOLExact (.val (.word wsl))) = true := by simp [shapeEqHOL, shapeOfHOLExact]
    have hsh3 : shapeEqHOL .one (shapeOfHOLExact (.val (.word wchild))) = true := by simp [shapeEqHOL, shapeOfHOLExact]
    have hd3 : evaluateHOLFiniteState s_sl
        (.dec (ofString "child") .one (.load .one (.op .add [.var .local (ofString "node"), .const (BitVec.ofNat 64 48)]))
          br_prog) =
        ((evaluateHOLFiniteState s_ch br_prog).1,
         { (evaluateHOLFiniteState s_ch br_prog).2 with
           locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState s_ch br_prog).2.locals
             (ofString "child", s_sl.locals.lookup (ofString "child")) }) := by
      rw [evaluateHOLFiniteState_dec_total]; dsimp only; rw [he3]; dsimp only; rw [if_pos hsh3]
    have hd2 : evaluateHOLFiniteState s_seg
        (.dec (ofString "sl") .one (.load .one (.op .add [.var .local (ofString "node"), .const (BitVec.ofNat 64 40)]))
          (.dec (ofString "child") .one (.load .one (.op .add [.var .local (ofString "node"), .const (BitVec.ofNat 64 48)]))
            br_prog)) =
        ((evaluateHOLFiniteState s_ch br_prog).1,
         { (evaluateHOLFiniteState s_ch br_prog).2 with
           locals := HolFiniteMapExact.resVarEq
             (HolFiniteMapExact.resVarEq (evaluateHOLFiniteState s_ch br_prog).2.locals
               (ofString "child", s_sl.locals.lookup (ofString "child")))
             (ofString "sl", s_seg.locals.lookup (ofString "sl")) }) := by
      rw [evaluateHOLFiniteState_dec_total]; dsimp only; rw [he2]; dsimp only; rw [if_pos hsh2]
      dsimp only [s_sl] at hd3 ⊢; rw [hd3]
    have hd1 : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn__split_extension) =
        ((evaluateHOLFiniteState s_ch br_prog).1,
         { (evaluateHOLFiniteState s_ch br_prog).2 with
           locals := HolFiniteMapExact.resVarEq
             (HolFiniteMapExact.resVarEq
               (HolFiniteMapExact.resVarEq (evaluateHOLFiniteState s_ch br_prog).2.locals
                 (ofString "child", s_sl.locals.lookup (ofString "child")))
               (ofString "sl", s_seg.locals.lookup (ofString "sl")))
             (ofString "seg", s.locals.lookup (ofString "seg")) }) := by
      rw [hbody, evaluateHOLFiniteState_dec_total]; dsimp only; rw [he1]; dsimp only; rw [if_pos hsh1]
      dsimp only [s_seg] at hd2 ⊢; rw [hd2]
    exact ⟨by dsimp only [res]; rw [hd1], by dsimp only [post]; rw [hd1]⟩
  -- Step 1: `decCall br := node_new_branch()` on `s_ch`
  have hres_br : Resumes (evaluateHOLFiniteState s_ch br_prog).1 := by
    rw [← hdec3_unfold.1]; exact hres
  have hsch_code : s_ch.code = originalRuntimeCode := hcode
  have hsch_AR : ArenaReady s_ch := localsFree_arenaReady s _ _ hAR
  dsimp only [br_prog] at hres_br
  obtain ⟨bvals, bbody, bcallee, bret, _, _, hbl, hbexn | ⟨brv, bpost, hbrun, _, hbcont_res, hbr_eq, hbp_eq⟩⟩ :=
    decCall_resumes_inv hres_br
  · obtain ⟨eid, ev, hb_exn, hne_tr, _⟩ := hbexn
    have hsame := lookupCodeHOLFinite_installed_body s_ch.code.lookup (ofString "node_new_branch")
      _ _ _ _ _ bvals bcallee (by rw [hsch_code]; exact lookup_node_new_branch) hbl
    subst hsame
    obtain ⟨_, _, _, _, hret_b, _⟩ := node_new_branch_spec (callEntryStateHOLFinite s_ch bcallee) hsch_code
      (localsFree_arenaReady s_ch _ _ hsch_AR) (by rw [hb_exn]; exact Or.inr ⟨eid, ev, rfl, hne_tr⟩)
    rw [hb_exn] at hret_b; cases hret_b
  · have hsame := lookupCodeHOLFinite_installed_body s_ch.code.lookup (ofString "node_new_branch")
      _ _ _ _ _ bvals bcallee (by rw [hsch_code]; exact lookup_node_new_branch) hbl
    subst hsame
    obtain ⟨_, _, _, wbr, hret_b, _, _, _, hmw0_br, _, _, _, hstep_br_all⟩ := node_new_branch_spec
      (callEntryStateHOLFinite s_ch bcallee) hsch_code
      (localsFree_arenaReady s_ch _ _ hsch_AR) (by rw [hbrun]; exact Or.inl ⟨brv, rfl⟩)
    rw [hbrun] at hret_b hmw0_br hstep_br_all
    injection hret_b with h1; injection h1 with hbrv_eq; subst hbrv_eq
    have hNd_sch : NodeHeap s_ch Nd := hNd
    set s0 := setVarHOLFinite (ofString "br") (.val (.word wbr)) { bpost with locals := s_ch.locals }
    have hstep0 : NodeStep s s0 Nd (wbr.toNat :: Nd) := by
      have hraw : NodeStep s_ch bpost Nd (wbr.toNat :: Nd) := NodeStep.from_locals_clock (hstep_br_all Nd hNd_sch)
      have hraw_s : NodeStep s bpost Nd (wbr.toNat :: Nd) := NodeStep.from_locals_clock hraw
      exact hraw_s.with_locals_clock _ _
    -- Step 2: `dec sal := sl - pl` on `s0`
    set wsal : BitVec 64 := wsl - wpl
    have hwsal_nat : wsal.toNat = wsl.toNat - wpl.toNat := by
      dsimp only [wsal]
      exact BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega)
    have hwsal_pos : 1 ≤ wsal.toNat := by omega
    set s1 := setVarHOLFinite (ofString "sal") (.val (.word wsal)) s0
    have hs0_sl : s0.locals.lookup (ofString "sl") = some (.val (.word wsl)) := by
      simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsch_sl,
        show ofString "br" ≠ ofString "sl" by decide]
    have hs0_pl : s0.locals.lookup (ofString "pl") = some (.val (.word wpl)) := by
      have hch_pl := hsch_other (ofString "pl") (by decide) (by decide) (by decide)
      simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hch_pl, hlk_pl,
        show ofString "br" ≠ ofString "pl" by decide]
    have hdec_sal : evaluateHOLFiniteState s0
        (.dec (ofString "sal") .one (.op .sub [.var .local (ofString "sl"), .var .local (ofString "pl")])
          (.seq sal_ite1
            (.seq sal_ite2
              (.dec (ofString "kal") .one (.op .sub [.var .local (ofString "rl"), .var .local (ofString "pl")])
                (.seq kal_ite (.return (.var .local (ofString "br")))))))) =
        ((evaluateHOLFiniteState s1
            (.seq sal_ite1
              (.seq sal_ite2
                (.dec (ofString "kal") .one (.op .sub [.var .local (ofString "rl"), .var .local (ofString "pl")])
                  (.seq kal_ite (.return (.var .local (ofString "br")))))))).1,
         { (evaluateHOLFiniteState s1
              (.seq sal_ite1
                (.seq sal_ite2
                  (.dec (ofString "kal") .one (.op .sub [.var .local (ofString "rl"), .var .local (ofString "pl")])
                    (.seq kal_ite (.return (.var .local (ofString "br")))))))).2 with
           locals := HolFiniteMapExact.resVarEq
             (evaluateHOLFiniteState s1
               (.seq sal_ite1
                 (.seq sal_ite2
                   (.dec (ofString "kal") .one (.op .sub [.var .local (ofString "rl"), .var .local (ofString "pl")])
                     (.seq kal_ite (.return (.var .local (ofString "br")))))))).2.locals
             (ofString "sal", s0.locals.lookup (ofString "sal")) }) := by
      rw [evaluateHOLFiniteState_dec_total]
      have hev : @evalHOLExact 64 F _ s0.toExact (fun a => Classical.propDecidable (s0.memaddrs a))
          (.op .sub [.var .local (ofString "sl"), .var .local (ofString "pl")]) =
          some (.val (.word wsal)) := by
        simp [evalHOLExact, evalListHOLExact, hs0_sl, hs0_pl, valueIsWord, valueWord, wordOpHOL, wordOp, wsal]
      have hsh : shapeEqHOL .one (shapeOfHOLExact (.val (.word wsal))) = true := by simp [shapeEqHOL, shapeOfHOLExact]
      dsimp only; rw [hev]; dsimp only; rw [if_pos hsh]
    have hstep1 : NodeStep s s1 Nd (wbr.toNat :: Nd) := hstep0.with_locals_clock _ _
    have hs1_res : Resumes (evaluateHOLFiniteState s1
        (.seq sal_ite1
          (.seq sal_ite2
            (.dec (ofString "kal") .one (.op .sub [.var .local (ofString "rl"), .var .local (ofString "pl")])
              (.seq kal_ite (.return (.var .local (ofString "br")))))))).1 := by
      rw [hdec_sal] at hbcont_res; exact hbcont_res
    -- Local lookups in `s1`
    have hs1_br : s1.locals.lookup (ofString "br") = some (.val (.word wbr)) := by
      simp [s1, s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "sal" ≠ ofString "br" by decide]
    have hs1_sal : s1.locals.lookup (ofString "sal") = some (.val (.word wsal)) := by
      simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hs1_seg : s1.locals.lookup (ofString "seg") = some (.val (.word wseg)) := by
      simp [s1, s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsch_seg,
        show ofString "sal" ≠ ofString "seg" by decide, show ofString "br" ≠ ofString "seg" by decide]
    have hs1_pl : s1.locals.lookup (ofString "pl") = some (.val (.word wpl)) := by
      simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs0_pl,
        show ofString "sal" ≠ ofString "pl" by decide]
    have hs1_child : s1.locals.lookup (ofString "child") = some (.val (.word wchild)) := by
      simp [s1, s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsch_child,
        show ofString "sal" ≠ ofString "child" by decide, show ofString "br" ≠ ofString "child" by decide]
    have hs1_other : ∀ x : MlS, x ≠ ofString "sal" → x ≠ ofString "br" →
        x ≠ ofString "seg" → x ≠ ofString "sl" → x ≠ ofString "child" →
        s1.locals.lookup x = s.locals.lookup x := by
      intro x h1 h2 h3 h4 h5
      simp [s1, s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        Ne.symm h1, Ne.symm h2, hsch_other x h3 h4 h5]
    -- Step 3: Evaluate `.seq sal_ite1 (.seq sal_ite2 cont_kal)` to `evaluateHOLFiniteState s2 cont_kal`!
    set cont_kal : ProgHOL 64 :=
      .dec (ofString "kal") .one (.op .sub [.var .local (ofString "rl"), .var .local (ofString "pl")])
        (.seq kal_ite (.return (.var .local (ofString "br"))))
    have hsal_steps : ∃ (s2 : PanSemStateFiniteExact 64 F) (Nd2 : List Nat),
        evaluateHOLFiniteState s1 (.seq sal_ite1 (.seq sal_ite2 cont_kal)) =
          evaluateHOLFiniteState s2 cont_kal ∧
        Resumes (evaluateHOLFiniteState s2 cont_kal).1 ∧
        NodeStep s s2 Nd Nd2 ∧
        wbr.toNat ∈ Nd2 ∧
        memW s2 wbr.toNat = 3 ∧
        (∀ x : MlS, x ≠ ofString "ex" → s2.locals.lookup x = s1.locals.lookup x) := by
      have hkey_seg_pl : KeyIn s1 (wbr.toNat :: Nd) (wseg + wpl).toNat wsal.toNat := by
        have hk0 : KeyIn s1 (wbr.toNat :: Nd) wseg.toNat wsl.toNat := hstep1.keyIn hAR hNd hkey_seg
        have heq_add : BitVec.ofNat 64 wseg.toNat + BitVec.ofNat 64 wpl.toNat = wseg + wpl := by simp
        rw [← heq_add, hwsal_nat]
        exact keyIn_subslice hk0 (by omega)
      have hc1 : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
          (.cmp .equal (.var .local (ofString "sal")) (.const (BitVec.ofNat 64 1))) =
          some (.val (.word (if wsal = 1 then 1 else 0))) := by
        simp [evalHOLExact, hs1_sal, Compiler.Encoders.Asm.wordCmpHOL]
      by_cases hsal1 : wsal.toNat = 1
      · -- Case `sal == 1`: `sal_ite1` stores `child` into `br`, `sal_ite2` skips!
        have hwsal_eq1 : wsal = 1 := by apply BitVec.eq_of_toNat_eq; simpa using hsal1
        have he_seg_pl : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
            (.op .add [.var .local (ofString "seg"), .var .local (ofString "pl")]) =
            some (.val (.word (wseg + wpl))) := by
          simp [evalHOLExact, evalListHOLExact, hs1_seg, hs1_pl, valueIsWord, valueWord, wordOpHOL, wordOp]
        obtain ⟨idx1, hlb1, hidx1_lt⟩ := eval_loadByte_nibble hstep1.arena.1 hkey_seg_pl (by omega) he_seg_pl
        have hch_root1 : RootIn (wbr.toNat :: Nd) wchild.toNat := hstep1.rootIn hchild_root
        obtain ⟨hdom_slot1, hstep_st1, hmw3_st1⟩ :=
          branch_store_child_step hstep1.arena hstep1.heap (List.mem_cons_self ..) hmw0_br hidx1_lt hch_root1
        set m_s1 := Wave8Contracts.M26.updW s1.memory (wbr + BitVec.ofNat 64 32 + idx1 * BitVec.ofNat 64 8) wchild
        set s2 : PanSemStateFiniteExact 64 F := { s1 with memory := m_s1 }
        have hite1_ev : evaluateHOLFiniteState s1 sal_ite1 = (none, s2) := by
          dsimp only [sal_ite1]
          rw [evaluateHOLFiniteState_ite, hc1, if_pos hwsal_eq1]; dsimp only
          simp only [if_neg (by decide : (1 : BitVec 64) ≠ 0)]
          rw [evaluateHOLFiniteState_store]
          rw [eval_slot_loadByte_add hs1_br hs1_seg hs1_pl hlb1]
          have hch_ev : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
              (.var .local (ofString "child")) = some (.val (.word wchild)) := hs1_child
          rw [hch_ev]
          simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL, hdom_slot1, ↓reduceIte]
          rfl
        have hc2 : @evalHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a))
            (.cmp .lower (.const (BitVec.ofNat 64 1)) (.var .local (ofString "sal"))) =
            some (.val (.word 0)) := by
          have hs2_sal : s2.locals.lookup (ofString "sal") = some (.val (.word wsal)) := hs1_sal
          simp [evalHOLExact, hs2_sal, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, hsal1]
        have hite2_ev : evaluateHOLFiniteState s2 sal_ite2 = (none, s2) := by
          dsimp only [sal_ite2]
          rw [evaluateHOLFiniteState_ite, hc2]; simp [evaluateHOLFiniteState_skip]
        have hseq_both : evaluateHOLFiniteState s1 (.seq sal_ite1 (.seq sal_ite2 cont_kal)) =
            evaluateHOLFiniteState s2 cont_kal := by
          rw [evaluateHOLFiniteState_seq_line780, hite1_ev]; dsimp only
          rw [evaluateHOLFiniteState_seq_line780, hite2_ev]
        rw [hseq_both] at hs1_res
        exact ⟨s2, wbr.toNat :: Nd, hseq_both, hs1_res, NodeStep.trans hAR hstep1 hstep_st1,
          List.mem_cons_self .., hmw3_st1, fun _ _ => rfl⟩
      · -- Case `1 < sal`: `sal_ite1` skips, `sal_ite2` calls `node_new_ext` and stores `ex` into `br`!
        have hsal_gt1 : 1 < wsal.toNat := by omega
        have hwsal_ne1 : wsal ≠ 1 := by intro h; apply hsal1; rw [h]; rfl
        have hite1_ev : evaluateHOLFiniteState s1 sal_ite1 = (none, s1) := by
          dsimp only [sal_ite1]
          rw [evaluateHOLFiniteState_ite, hc1, if_neg hwsal_ne1]; simp [evaluateHOLFiniteState_skip]
        have hc2 : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
            (.cmp .lower (.const (BitVec.ofNat 64 1)) (.var .local (ofString "sal"))) =
            some (.val (.word 1)) := by
          simp [evalHOLExact, hs1_sal, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, hsal_gt1]
        set dc_ex : ProgHOL 64 :=
          .decCall (ofString "ex") .one (ofString "node_new_ext")
            [.op .add [.var .local (ofString "seg"), .var .local (ofString "pl"), .const (BitVec.ofNat 64 1)],
             .op .sub [.var .local (ofString "sal"), .const (BitVec.ofNat 64 1)],
             .var .local (ofString "child")]
            (.store (.op .add [.var .local (ofString "br"), .const (BitVec.ofNat 64 32),
                .panop .mul [.loadByte (.op .add [.var .local (ofString "seg"), .var .local (ofString "pl")]),
                  .const (BitVec.ofNat 64 8)]])
              (.var .local (ofString "ex")))
        have hite2_ev : evaluateHOLFiniteState s1 sal_ite2 = evaluateHOLFiniteState s1 dc_ex := by
          dsimp only [sal_ite2]
          rw [evaluateHOLFiniteState_ite, hc2]
          simp only [if_neg (by decide : (1 : BitVec 64) ≠ 0)]
          rfl
        have hseq_12 : evaluateHOLFiniteState s1 (.seq sal_ite1 (.seq sal_ite2 cont_kal)) =
            evaluateHOLFiniteState s1 (.seq dc_ex cont_kal) := by
          rw [evaluateHOLFiniteState_seq_line780, hite1_ev]; dsimp only
          rw [evaluateHOLFiniteState_seq_line780, hite2_ev, ← evaluateHOLFiniteState_seq_line780]
        rw [hseq_12] at hs1_res
        -- Unfold `dc_ex` via `evaluateHOLFiniteState_decCall_total`
        have hdc_tot := evaluateHOLFiniteState_decCall_total s1 (ofString "ex") .one (ofString "node_new_ext")
          [.op .add [.var .local (ofString "seg"), .var .local (ofString "pl"), .const (BitVec.ofNat 64 1)],
           .op .sub [.var .local (ofString "sal"), .const (BitVec.ofNat 64 1)],
           .var .local (ofString "child")]
          (.store (.op .add [.var .local (ofString "br"), .const (BitVec.ofNat 64 32),
              .panop .mul [.loadByte (.op .add [.var .local (ofString "seg"), .var .local (ofString "pl")]),
                .const (BitVec.ofNat 64 8)]])
            (.var .local (ofString "ex")))
        have hex_args : evalListHOLFinite s1 (h := fun a => Classical.propDecidable (s1.memaddrs a))
            [.op .add [.var .local (ofString "seg"), .var .local (ofString "pl"), .const (BitVec.ofNat 64 1)],
             .op .sub [.var .local (ofString "sal"), .const (BitVec.ofNat 64 1)],
             .var .local (ofString "child")] =
            some [.val (.word (wseg + (wpl + 1))), .val (.word (wsal - 1)), .val (.word wchild)] := by
          rw [evalListHOLFinite_eq_toExact]
          simp [evalListHOLExact, evalHOLExact, hs1_seg, hs1_pl, hs1_sal, hs1_child,
            valueIsWord, valueWord, wordOpHOL, wordOp]
        rw [hex_args] at hdc_tot; dsimp only at hdc_tot
        have hs1_code : s1.code = originalRuntimeCode := hstep1.arena.1.code
        rcases hlk_ex : lookupCodeHOLFinite s1.code.lookup (ofString "node_new_ext")
            [.val (.word (wseg + (wpl + 1))), .val (.word (wsal - 1)), .val (.word wchild)] with _ | ⟨exb, exc, exr⟩
        · rw [hlk_ex] at hdc_tot; dsimp only at hdc_tot
          rw [evaluateHOLFiniteState_seq_line780, hdc_tot] at hs1_res
          exact absurd hs1_res not_resumes_error
        · rw [hlk_ex] at hdc_tot; dsimp only at hdc_tot
          by_cases hcz1 : s1.clock = 0
          · rw [if_pos hcz1] at hdc_tot
            rw [evaluateHOLFiniteState_seq_line780, hdc_tot] at hs1_res
            rcases hs1_res with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
          · rw [if_neg hcz1] at hdc_tot
            have hlk_ex_code : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "node_new_ext")
                [.val (.word (wseg + (wpl + 1))), .val (.word (wsal - 1)), .val (.word wchild)] =
                some (exb, exc, exr) := by rwa [← hs1_code]
            obtain ⟨hbody_ex, hex_nib⟩ := lookup_param_exact lookup_node_new_ext hlk_ex_code
              [] "nib" .one [(ofString "nlen", .one), (ofString "child", .one)]
              [] (.val (.word (wseg + (wpl + 1)))) _ rfl rfl rfl (by decide)
            obtain ⟨_, hex_nlen⟩ := lookup_param_exact lookup_node_new_ext hlk_ex_code
              [(ofString "nib", .one)] "nlen" .one [(ofString "child", .one)]
              [_] (.val (.word (wsal - 1))) _ rfl rfl rfl (by decide)
            obtain ⟨_, hex_ch⟩ := lookup_param_exact lookup_node_new_ext hlk_ex_code
              [(ofString "nib", .one), (ofString "nlen", .one)] "child" .one []
              [_, _] (.val (.word wchild)) [] rfl rfl rfl (by decide)
            subst hbody_ex
            have hrem_ex := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite s1 exc)
              (sourceFnBody Guest.Software.guestFn_node_new_ext)
            rcases hex_run : evaluateHOLFiniteState (callEntryStateHOLFinite s1 exc)
                (sourceFnBody Guest.Software.guestFn_node_new_ext) with ⟨ex_res, ex_post⟩
            have hfix_ex : fixClockHOLFinite (callEntryStateHOLFinite s1 exc)
                (evaluateHOLFiniteState (callEntryStateHOLFinite s1 exc)
                  (sourceFnBody Guest.Software.guestFn_node_new_ext)) = (ex_res, ex_post) := by
              rw [hex_run] at hrem_ex ⊢; simp [fixClockHOLFinite, Nat.not_lt.mpr hrem_ex]
            rw [hfix_ex, hex_run] at hdc_tot; dsimp only at hdc_tot
            rcases ex_res with _ | ex_res'
            · rw [evaluateHOLFiniteState_seq_line780, hdc_tot] at hs1_res
              exact absurd hs1_res not_resumes_error
            · cases ex_res' with
              | returned ex_rv =>
                dsimp only at hdc_tot
                by_cases hsh_ex : (shapeEqHOL (shapeOfHOLExact ex_rv) .one && shapeEqHOL (shapeOfHOLExact ex_rv) exr) = true
                · rw [if_pos hsh_ex] at hdc_tot
                  have hsub_seg : KeyIn s1 (wbr.toNat :: Nd) (wseg + (wpl + 1)).toNat (wsal - 1).toNat := by
                    have heq1 : (wsal - 1).toNat = wsal.toNat - 1 :=
                      BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; change 1 ≤ wsal.toNat; omega)
                    have heq2 : BitVec.ofNat 64 (wseg + wpl).toNat + BitVec.ofNat 64 1 = wseg + (wpl + 1) := by
                      have h0 : BitVec.ofNat 64 (wseg + wpl).toNat = wseg + wpl := by
                        apply BitVec.eq_of_toNat_eq; simp [Nat.mod_eq_of_lt (wseg + wpl).isLt]
                      rw [h0]
                      exact BitVec.add_assoc wseg wpl 1
                    rw [← heq2, heq1]
                    exact keyIn_subslice hkey_seg_pl (by omega)
                  obtain ⟨Nd_ex, hstep_ex, hret_ex⟩ := nodeStep_of_nodeFn nf_node_new_ext s1 hs1_code
                    hstep1.arena hstep1.heap hlk_ex
                    (by intro n hn; rw [List.mem_singleton.mp hn]; simp [locN, callEntryStateHOLFinite, hex_ch]
                        exact hstep1.rootIn hchild_root)
                    (by
                      have h1 : locN (callEntryStateHOLFinite s1 exc) "nib" = (wseg + (wpl + 1)).toNat := by
                        simp [locN, callEntryStateHOLFinite, hex_nib]
                      have h2 : locN (callEntryStateHOLFinite s1 exc) "nlen" = (wsal - 1).toNat := by
                        simp [locN, callEntryStateHOLFinite, hex_nlen]
                      rw [h1, h2]
                      exact hsub_seg)
                    (by rw [hex_run]; exact Or.inl ⟨ex_rv, rfl⟩)
                  rw [hex_run] at hstep_ex hret_ex; dsimp only at hstep_ex hret_ex
                  obtain ⟨wex, rfl, hwex_root⟩ := hret_ex ex_rv rfl
                  set st_ex := setVarHOLFinite (ofString "ex") (.val (.word wex)) { ex_post with locals := s1.locals }
                  have hstep_ex' : NodeStep s1 st_ex (wbr.toNat :: Nd) Nd_ex := hstep_ex.with_locals_clock _ _
                  have hkey_ex_pl : KeyIn st_ex Nd_ex (wseg + wpl).toNat wsal.toNat :=
                    hstep_ex'.keyIn hstep1.arena hstep1.heap hkey_seg_pl
                  have hstex_seg : st_ex.locals.lookup (ofString "seg") = some (.val (.word wseg)) := by
                    simp [st_ex, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs1_seg,
                      show ofString "ex" ≠ ofString "seg" by decide]
                  have hstex_pl : st_ex.locals.lookup (ofString "pl") = some (.val (.word wpl)) := by
                    simp [st_ex, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs1_pl,
                      show ofString "ex" ≠ ofString "pl" by decide]
                  have hstex_br : st_ex.locals.lookup (ofString "br") = some (.val (.word wbr)) := by
                    simp [st_ex, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs1_br,
                      show ofString "ex" ≠ ofString "br" by decide]
                  have hstex_ex : st_ex.locals.lookup (ofString "ex") = some (.val (.word wex)) := by
                    simp [st_ex, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                  have he_seg_pl' : @evalHOLExact 64 F _ st_ex.toExact (fun a => Classical.propDecidable (st_ex.memaddrs a))
                      (.op .add [.var .local (ofString "seg"), .var .local (ofString "pl")]) =
                      some (.val (.word (wseg + wpl))) := by
                    simp [evalHOLExact, evalListHOLExact, hstex_seg, hstex_pl, valueIsWord, valueWord, wordOpHOL, wordOp]
                  obtain ⟨idx1, hlb1, hidx1_lt⟩ := eval_loadByte_nibble hstep_ex'.arena.1 hkey_ex_pl (by omega) he_seg_pl'
                  have hbr_in_ex : wbr.toNat ∈ Nd_ex := hstep_ex'.sub wbr.toNat (List.mem_cons_self ..)
                  have hbr_k_ex : memW st_ex wbr.toNat = 3 := (hstep_ex'.kinds wbr.toNat (List.mem_cons_self ..)).trans hmw0_br
                  obtain ⟨hdom_slot_ex, hstep_st_ex, hmw3_st_ex⟩ :=
                    branch_store_child_step hstep_ex'.arena hstep_ex'.heap hbr_in_ex hbr_k_ex hidx1_lt hwex_root
                  set m_ex := Wave8Contracts.M26.updW st_ex.memory (wbr + BitVec.ofNat 64 32 + idx1 * BitVec.ofNat 64 8) wex
                  set st_ex2 : PanSemStateFiniteExact 64 F := { st_ex with memory := m_ex }
                  have hst_eval_ex : evaluateHOLFiniteState st_ex
                      (.store (.op .add [.var .local (ofString "br"), .const (BitVec.ofNat 64 32),
                          .panop .mul [.loadByte (.op .add [.var .local (ofString "seg"), .var .local (ofString "pl")]),
                            .const (BitVec.ofNat 64 8)]])
                        (.var .local (ofString "ex"))) = (none, st_ex2) := by
                    rw [evaluateHOLFiniteState_store]
                    rw [eval_slot_loadByte_add hstex_br hstex_seg hstex_pl hlb1]
                    have hex_ev : @evalHOLExact 64 F _ st_ex.toExact (fun a => Classical.propDecidable (st_ex.memaddrs a))
                        (.var .local (ofString "ex")) = some (.val (.word wex)) := hstex_ex
                    rw [hex_ev]
                    simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL, hdom_slot_ex, ↓reduceIte]
                    rfl
                  rw [hst_eval_ex] at hdc_tot; dsimp only at hdc_tot
                  set s2 : PanSemStateFiniteExact 64 F :=
                    { st_ex2 with locals := HolFiniteMapExact.resVarEq st_ex.locals (ofString "ex", s1.locals.lookup (ofString "ex")) }
                  have hdc_eq : evaluateHOLFiniteState s1 dc_ex = (none, s2) := hdc_tot
                  have hseq_both : evaluateHOLFiniteState s1 (.seq sal_ite1 (.seq sal_ite2 cont_kal)) =
                      evaluateHOLFiniteState s2 cont_kal := by
                    rw [hseq_12, evaluateHOLFiniteState_seq_line780, hdc_eq]
                  rw [evaluateHOLFiniteState_seq_line780, hdc_eq] at hs1_res
                  dsimp only at hs1_res
                  have hstep_12 : NodeStep s s2 Nd Nd_ex :=
                    (NodeStep.trans hAR hstep1 (NodeStep.trans hstep1.arena hstep_ex' hstep_st_ex)).with_locals_clock _ s2.clock
                  have hs2_loc : ∀ x : MlS, x ≠ ofString "ex" → s2.locals.lookup x = s1.locals.lookup x := by
                    intro x hx; dsimp only [s2]; rw [resVarEq_lookup_ne _ _ _ _ hx]
                    simp [st_ex, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hx]
                  exact ⟨s2, Nd_ex, hseq_both, hs1_res, hstep_12, hbr_in_ex, hmw3_st_ex, hs2_loc⟩
                · rw [if_neg hsh_ex] at hdc_tot
                  rw [evaluateHOLFiniteState_seq_line780, hdc_tot] at hs1_res
                  exact absurd hs1_res not_resumes_error
              | exception eid ev =>
                dsimp only at hdc_tot
                rw [evaluateHOLFiniteState_seq_line780, hdc_tot] at hs1_res
                rcases hs1_res with ⟨_, h⟩ | ⟨eid', ev', h, hne_tr⟩
                · simp at h
                · injection h with h1; injection h1 with he1 he2; subst he1 he2
                  exact absurd (congrArg Prod.fst hex_run)
                    (node_new_ext_no_nonTrap_exn (callEntryStateHOLFinite s1 exc) hs1_code eid ev hne_tr)
              | _ =>
                rw [evaluateHOLFiniteState_seq_line780, hdc_tot] at hs1_res
                rcases hs1_res with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
    obtain ⟨s2, Nd2, hsal_eq, hs2_res, hstep2, hbr_in2, hbr_k2, hs2_loc⟩ := hsal_steps
    -- Step 4: `dec kal := rl - pl` on `s2`
    set wkal : BitVec 64 := wrl - wpl
    have hwkal_nat : wkal.toNat = wrl.toNat - wpl.toNat :=
      BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact hwpl_le_wrl)
    have hs2_rl : s2.locals.lookup (ofString "rl") = some (.val (.word wrl)) := by
      rw [hs2_loc _ (by decide), hs1_other _ (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact hlk_rl
    have hs2_pl : s2.locals.lookup (ofString "pl") = some (.val (.word wpl)) := by
      rw [hs2_loc _ (by decide)]; exact hs1_pl
    set s3 := setVarHOLFinite (ofString "kal") (.val (.word wkal)) s2
    have hdec_kal : evaluateHOLFiniteState s2 cont_kal =
        ((evaluateHOLFiniteState s3 (.seq kal_ite (.return (.var .local (ofString "br"))))).1,
         { (evaluateHOLFiniteState s3 (.seq kal_ite (.return (.var .local (ofString "br"))))).2 with
           locals := HolFiniteMapExact.resVarEq
             (evaluateHOLFiniteState s3 (.seq kal_ite (.return (.var .local (ofString "br"))))).2.locals
             (ofString "kal", s2.locals.lookup (ofString "kal")) }) := by
      dsimp only [cont_kal]; rw [evaluateHOLFiniteState_dec_total]
      have hev : @evalHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a))
          (.op .sub [.var .local (ofString "rl"), .var .local (ofString "pl")]) =
          some (.val (.word wkal)) := by
        simp [evalHOLExact, evalListHOLExact, hs2_rl, hs2_pl, valueIsWord, valueWord, wordOpHOL, wordOp, wkal]
      have hsh : shapeEqHOL .one (shapeOfHOLExact (.val (.word wkal))) = true := by simp [shapeEqHOL, shapeOfHOLExact]
      dsimp only; rw [hev]; dsimp only; rw [if_pos hsh]
    have hstep3 : NodeStep s s3 Nd Nd2 := hstep2.with_locals_clock _ _
    have hs3_res : Resumes (evaluateHOLFiniteState s3 (.seq kal_ite (.return (.var .local (ofString "br"))))).1 := by
      rw [hdec_kal] at hs2_res; exact hs2_res
    have hs3_kal : s3.locals.lookup (ofString "kal") = some (.val (.word wkal)) := by
      simp [s3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hs3_br : s3.locals.lookup (ofString "br") = some (.val (.word wbr)) := by
      have h2_br := hs2_loc (ofString "br") (by decide)
      simp [s3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "kal" ≠ ofString "br" by decide, h2_br, hs1_br]
    have hs3_rk : s3.locals.lookup (ofString "rk") = some (.val (.word wrk)) := by
      have h2_rk := hs2_loc (ofString "rk") (by decide)
      have h1_rk := hs1_other (ofString "rk") (by decide) (by decide) (by decide) (by decide) (by decide)
      simp [s3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "kal" ≠ ofString "rk" by decide, h2_rk, h1_rk, hlk_rk]
    have hs3_pl : s3.locals.lookup (ofString "pl") = some (.val (.word wpl)) := by
      simp [s3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "kal" ≠ ofString "pl" by decide, hs2_pl]
    have hs3_vptr : s3.locals.lookup (ofString "vptr") = some (.val (.word wvptr)) := by
      have h2_vp := hs2_loc (ofString "vptr") (by decide)
      have h1_vp := hs1_other (ofString "vptr") (by decide) (by decide) (by decide) (by decide) (by decide)
      simp [s3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "kal" ≠ ofString "vptr" by decide, h2_vp, h1_vp, hlk_vptr]
    have hs3_vlen : s3.locals.lookup (ofString "vlen") = some (.val (.word wvlen)) := by
      have h2_vl := hs2_loc (ofString "vlen") (by decide)
      have h1_vl := hs1_other (ofString "vlen") (by decide) (by decide) (by decide) (by decide) (by decide)
      simp [s3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "kal" ≠ ofString "vlen" by decide, h2_vl, h1_vl, hlk_vlen]
    -- Helper wrapping the final outcome from `(evaluateHOLFiniteState s3 (.seq kal_ite (.return br)))` back to `res/post`!
    have hwrap_s3 : ∀ {Nd_f : List Nat},
        NodeStep s (evaluateHOLFiniteState s3 (.seq kal_ite (.return (.var .local (ofString "br"))))).2 Nd Nd_f →
        (∀ v, (evaluateHOLFiniteState s3 (.seq kal_ite (.return (.var .local (ofString "br"))))).1 = some (.returned v) →
          ∃ w : BitVec 64, v = .val (.word w) ∧ RootIn Nd_f w.toNat) →
        ∃ Nd', NodeStep s post Nd Nd' ∧
          ∀ v, res = some (.returned v) → ∃ w : BitVec 64, v = .val (.word w) ∧ RootIn Nd' w.toNat := by
      intro Nd_f hns_f hret_f
      have hr_chain : res = (evaluateHOLFiniteState s3 (.seq kal_ite (.return (.var .local (ofString "br"))))).1 := by
        rw [hdec3_unfold.1]; dsimp only [br_prog]
        rw [hbr_eq, hdec_sal]; dsimp only
        rw [hsal_eq, hdec_kal]
      refine ⟨Nd_f, ?_, fun v hv => hret_f v (hr_chain ▸ hv)⟩
      rw [hdec3_unfold.2]; dsimp only [br_prog]
      rw [hbp_eq, hdec_sal]; dsimp only
      rw [hsal_eq, hdec_kal]; dsimp only
      exact (((((hns_f.with_locals_clock _ _).with_locals_clock _ _).with_locals_clock _ _).with_locals_clock _ _).with_locals_clock _ _)
    -- Step 5: Analyze `kal_ite` on `s3`!
    have hc_kal0 : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
        (.cmp .equal (.var .local (ofString "kal")) (.const (BitVec.ofNat 64 0))) =
        some (.val (.word (if wkal = 0 then 1 else 0))) := by
      simp [evalHOLExact, hs3_kal, Compiler.Encoders.Asm.wordCmpHOL]
    by_cases hkal0 : wkal = 0
    · -- `kal == 0`: store `(vptr, vlen)` at `br + 160 / br + 168`, then `return br`!
      obtain ⟨hdom160, hdom168, hstep_val, _⟩ :=
        branch_store_value_step hstep3.arena hstep3.heap hbr_in2 hbr_k2 (wvptr := wvptr) hwvlen_lt
      set m3_1 := Wave8Contracts.M26.updW s3.memory (wbr + BitVec.ofNat 64 160) wvptr
      set m3_2 := Wave8Contracts.M26.updW m3_1 (wbr + BitVec.ofNat 64 168) wvlen
      set s4 : PanSemStateFiniteExact 64 F := { s3 with memory := m3_2 }
      have hite_kal0 : evaluateHOLFiniteState s3 kal_ite = (none, s4) := by
        dsimp only [kal_ite]
        rw [evaluateHOLFiniteState_ite, hc_kal0, if_pos hkal0]; dsimp only
        simp only [if_neg (by decide : (1 : BitVec 64) ≠ 0)]
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_store]
        have hd1 : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
            (.op .add [.var .local (ofString "br"), .const (BitVec.ofNat 64 160)]) =
            some (.val (.word (wbr + BitVec.ofNat 64 160))) := by
          simp [evalHOLExact, evalListHOLExact, hs3_br, valueIsWord, valueWord, wordOpHOL, wordOp]
        have he1 : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
            (.var .local (ofString "vptr")) = some (.val (.word wvptr)) := hs3_vptr
        rw [hd1, he1]
        simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL, hdom160, ↓reduceIte]
        set st3_1 : PanSemStateFiniteExact 64 F := { s3 with memory := m3_1 }
        change evaluateHOLFiniteState st3_1
          (.store (.op .add [.var .local (ofString "br"), .const (BitVec.ofNat 64 168)]) (.var .local (ofString "vlen"))) =
          (none, s4)
        rw [evaluateHOLFiniteState_store]
        have hd2 : @evalHOLExact 64 F _ st3_1.toExact
            (fun a => Classical.propDecidable (st3_1.memaddrs a))
            (.op .add [.var .local (ofString "br"), .const (BitVec.ofNat 64 168)]) =
            some (.val (.word (wbr + BitVec.ofNat 64 168))) := by
          simp [st3_1, evalHOLExact, evalListHOLExact, hs3_br, valueIsWord, valueWord, wordOpHOL, wordOp]
        have he2 : @evalHOLExact 64 F _ st3_1.toExact
            (fun a => Classical.propDecidable (st3_1.memaddrs a))
            (.var .local (ofString "vlen")) = some (.val (.word wvlen)) := hs3_vlen
        rw [hd2, he2]
        have hdom168' : st3_1.memaddrs (wbr + BitVec.ofNat 64 168) := hdom168
        simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL, hdom168', ↓reduceIte]
        rfl
      have hret_s4 : evaluateHOLFiniteState s4 (.return (.var .local (ofString "br"))) =
          (some (.returned (.val (.word wbr))), emptyLocalsHOLFinite s4) := by
        have hs4_br : s4.locals.lookup (ofString "br") = some (.val (.word wbr)) := hs3_br
        simp [evaluateHOLFiniteState_return, evalHOLExact, hs4_br, shapeOfHOLExact, sizeOfShapeWithContextHOL]
      have hseq_kal : evaluateHOLFiniteState s3 (.seq kal_ite (.return (.var .local (ofString "br")))) =
          (some (.returned (.val (.word wbr))), emptyLocalsHOLFinite s4) := by
        rw [evaluateHOLFiniteState_seq_line780, hite_kal0]; dsimp only; exact hret_s4
      apply hwrap_s3 (Nd_f := Nd2)
      · rw [hseq_kal]; exact (NodeStep.trans hAR hstep3 hstep_val).with_locals_clock _ _
      · intro v hv; rw [hseq_kal] at hv; injection hv with h1; injection h1 with h2; subst h2
        exact ⟨wbr, rfl, Or.inr hbr_in2⟩
    · -- `kal ≠ 0`: `dec idx := loadByte(rk + pl); if load(br + 32 + idx * 8) != 0 then mpt_fail(11); decCall lf := node_new_leaf(...); store; return br`
      have hwkal_pos : wkal.toNat ≠ 0 := by intro h; apply hkal0; apply BitVec.eq_of_toNat_eq; simpa using h
      have hkey_rk_pl : KeyIn s3 Nd2 (wrk + wpl).toNat wkal.toNat := by
        have hk0 : KeyIn s3 Nd2 wrk.toNat wrl.toNat := hstep3.keyIn hAR hNd hkey_rk
        have heq_add : BitVec.ofNat 64 wrk.toNat + BitVec.ofNat 64 wpl.toNat = wrk + wpl := by simp
        rw [← heq_add, hwkal_nat]
        exact keyIn_subslice hk0 (by omega)
      have he_rk_pl : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
          (.op .add [.var .local (ofString "rk"), .var .local (ofString "pl")]) =
          some (.val (.word (wrk + wpl))) := by
        simp [evalHOLExact, evalListHOLExact, hs3_rk, hs3_pl, valueIsWord, valueWord, wordOpHOL, wordOp]
      obtain ⟨widx, hlb_rk, hwidx_lt⟩ := eval_loadByte_nibble hstep3.arena.1 hkey_rk_pl hwkal_pos he_rk_pl
      set s_idx := setVarHOLFinite (ofString "idx") (.val (.word widx)) s3
      have hstep_idx : NodeStep s s_idx Nd Nd2 := hstep3.with_locals_clock _ _
      set idx_body : ProgHOL 64 :=
        .seq
          (.ite (.cmp .notEqual
              (.load .one (.op .add [.var .local (ofString "br"), .const (BitVec.ofNat 64 32),
                .panop .mul [.var .local (ofString "idx"), .const (BitVec.ofNat 64 8)]]))
              (.const (BitVec.ofNat 64 0)))
            (.call (some (none, none)) (ofString "mpt_fail") [.const (BitVec.ofNat 64 11)])
            .skip)
          (.decCall (ofString "lf") .one (ofString "node_new_leaf")
            [.op .add [.var .local (ofString "rk"), .var .local (ofString "pl"), .const (BitVec.ofNat 64 1)],
             .op .sub [.var .local (ofString "kal"), .const (BitVec.ofNat 64 1)],
             .var .local (ofString "vptr"),
             .var .local (ofString "vlen")]
            (.store (.op .add [.var .local (ofString "br"), .const (BitVec.ofNat 64 32),
                .panop .mul [.var .local (ofString "idx"), .const (BitVec.ofNat 64 8)]])
              (.var .local (ofString "lf"))))
      have hite_kal_ne : evaluateHOLFiniteState s3 kal_ite =
          ((evaluateHOLFiniteState s_idx idx_body).1,
           { (evaluateHOLFiniteState s_idx idx_body).2 with
             locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState s_idx idx_body).2.locals
               (ofString "idx", s3.locals.lookup (ofString "idx")) }) := by
        dsimp only [kal_ite]
        rw [evaluateHOLFiniteState_ite, hc_kal0, if_neg hkal0]; dsimp only
        simp only [↓reduceIte]
        rw [evaluateHOLFiniteState_dec_total]
        have hsh : shapeEqHOL .one (shapeOfHOLExact (.val (.word widx))) = true := by simp [shapeEqHOL, shapeOfHOLExact]
        dsimp only; rw [hlb_rk]; dsimp only; rw [if_pos hsh]
      -- Evaluate `load .one (br + 32 + idx * 8)` in `s_idx`:
      have hsidx_br : s_idx.locals.lookup (ofString "br") = some (.val (.word wbr)) := by
        simp [s_idx, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_br,
          show ofString "idx" ≠ ofString "br" by decide]
      have hsidx_idx : s_idx.locals.lookup (ofString "idx") = some (.val (.word widx)) := by
        simp [s_idx, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hp_br_idx := hstep_idx.heap.1 wbr.toNat hbr_in2
      have hbr_sz_idx : nodeSize (memW s_idx wbr.toNat) = 176 := by
        have hk3 : memW s_idx wbr.toNat = 3 := hbr_k2
        simp [nodeSize, hk3]
      obtain ⟨wslot_cur, hdom_cur, hm_cur⟩ := hp_br_idx.2.2.2.1.2.2 (4 + widx.toNat)
        (by dsimp [nodeIvl]; omega)
      dsimp [nodeIvl] at hdom_cur hm_cur
      have hslot_addr_eq : wbr + BitVec.ofNat 64 32 + widx * BitVec.ofNat 64 8 =
          BitVec.ofNat 64 (wbr.toNat + 8 * (4 + widx.toNat)) := by
        have hins_br := hp_br_idx.2.2.1
        dsimp [Inside, nodeIvl] at hins_br
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
        omega
      have hdom_cur' : s_idx.memaddrs (wbr + BitVec.ofNat 64 32 + widx * BitVec.ofNat 64 8) := by
        rwa [hslot_addr_eq]
      have hm_cur' : s_idx.memory (wbr + BitVec.ofNat 64 32 + widx * BitVec.ofNat 64 8) = .word wslot_cur := by
        rwa [hslot_addr_eq]
      have hc_slot : @evalHOLExact 64 F _ s_idx.toExact (fun a => Classical.propDecidable (s_idx.memaddrs a))
          (.cmp .notEqual
            (.load .one (.op .add [.var .local (ofString "br"), .const (BitVec.ofNat 64 32),
              .panop .mul [.var .local (ofString "idx"), .const (BitVec.ofNat 64 8)]]))
            (.const (BitVec.ofNat 64 0))) =
          some (.val (.word (if wslot_cur ≠ 0 then 1 else 0))) := by
        have hadd0 : ∀ u : BitVec 64, u + (0 : BitVec 64) = u := BitVec.add_zero
        have hassoc : wbr + (BitVec.ofNat 64 32 + widx * BitVec.ofNat 64 8) =
            wbr + BitVec.ofNat 64 32 + widx * BitVec.ofNat 64 8 :=
          (BitVec.add_assoc wbr (BitVec.ofNat 64 32) (widx * BitVec.ofNat 64 8)).symm
        simp [evalHOLExact, evalListHOLExact, hsidx_br, hsidx_idx,
          valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL, hadd0, hassoc,
          isWfShapeExactHOL, memLoadHOLExact, hdom_cur', hm_cur', Compiler.Encoders.Asm.wordCmpHOL]
      by_cases hwslot_nz : wslot_cur ≠ 0
      · -- `wslot_cur ≠ 0`: calls `mpt_fail(11)`, which raises `MptErr` and aborts!
        have hite_fail : evaluateHOLFiniteState s_idx
            (.ite (.cmp .notEqual
                (.load .one (.op .add [.var .local (ofString "br"), .const (BitVec.ofNat 64 32),
                  .panop .mul [.var .local (ofString "idx"), .const (BitVec.ofNat 64 8)]]))
                (.const (BitVec.ofNat 64 0)))
              (.call (some (none, none)) (ofString "mpt_fail") [.const (BitVec.ofNat 64 11)])
              .skip) =
            evaluateHOLFiniteState s_idx
              (.call (some (none, none)) (ofString "mpt_fail") [.const (BitVec.ofNat 64 11)]) := by
          rw [evaluateHOLFiniteState_ite, hc_slot, if_pos hwslot_nz]; simp
        have hsidx_code : s_idx.code = originalRuntimeCode := hstep_idx.arena.1.code
        have hfail_not_none : (evaluateHOLFiniteState s_idx
            (.call (some (none, none)) (ofString "mpt_fail") [.const (BitVec.ofNat 64 11)])).1 ≠ none := by
          rw [evaluateHOLFiniteState_call]
          simp only [evalListHOLFinite_eq_toExact, evalListHOLExact, evalHOLExact]
          rcases hlk_f : lookupCodeHOLFinite s_idx.code.lookup (ofString "mpt_fail") [.val (.word 11)] with _ | ⟨fb, fc, fr⟩
          · simp
          · dsimp only
            have hsame_f := lookupCodeHOLFinite_installed_body s_idx.code.lookup (ofString "mpt_fail")
              _ _ _ _ _ [.val (.word 11)] fc (by rw [hsidx_code]; exact lookup_mpt_fail) hlk_f
            subst hsame_f
            split
            · simp
            · have hf_body : sourceFnBody Guest.Software.guestFn_mpt_fail =
                  .seq (.raise (ofString "MptErr") (.var .local (ofString "code"))) (.return (.const 0)) := rfl
              have hf_not_ret : ∀ rv,
                  (evaluateHOLFiniteState (callEntryStateHOLFinite s_idx fc)
                    (sourceFnBody Guest.Software.guestFn_mpt_fail)).1 ≠ some (.returned rv) := by
                intro rv hret_f
                rw [hf_body, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_raise] at hret_f
                rcases h_esh : (callEntryStateHOLFinite s_idx fc).eshapes.lookup (ofString "MptErr") with _ | esh
                · rw [h_esh] at hret_f
                  rcases h_cv : @evalHOLExact 64 F _ (callEntryStateHOLFinite s_idx fc).toExact
                      (fun a => Classical.propDecidable ((callEntryStateHOLFinite s_idx fc).memaddrs a))
                      (.var .local (ofString "code")) with _ | cv <;>
                    (rw [h_cv] at hret_f; dsimp only at hret_f; cases hret_f)
                · rw [h_esh] at hret_f
                  rcases h_cv : @evalHOLExact 64 F _ (callEntryStateHOLFinite s_idx fc).toExact
                      (fun a => Classical.propDecidable ((callEntryStateHOLFinite s_idx fc).memaddrs a))
                      (.var .local (ofString "code")) with _ | cv
                  · rw [h_cv] at hret_f; dsimp only at hret_f; cases hret_f
                  · rw [h_cv] at hret_f; dsimp only at hret_f
                    by_cases hcond : shapeOfHOLExact cv = esh ∧
                        sizeOfShapeWithContextHOL (callEntryStateHOLFinite s_idx fc).structs (shapeOfHOLExact cv) ≤ 32
                    · rw [if_pos hcond] at hret_f; dsimp only at hret_f; cases hret_f
                    · rw [if_neg hcond] at hret_f; dsimp only at hret_f; cases hret_f
              rcases hfr_ev : evaluateHOLFiniteState (callEntryStateHOLFinite s_idx fc)
                  (sourceFnBody Guest.Software.guestFn_mpt_fail) with ⟨fr_r, fr_p⟩
              rcases fr_r with _ | fr_r'
              · simp
              · cases fr_r' with
                | returned rv => exact absurd (congrArg Prod.fst hfr_ev) (hf_not_ret rv)
                | _ => simp
        rcases hfail_out : evaluateHOLFiniteState s_idx
            (.call (some (none, none)) (ofString "mpt_fail") [.const (BitVec.ofNat 64 11)]) with ⟨fr_o, fp_o⟩
        have hfail_out' : evaluateHOLFiniteState s_idx
            (.call (some (none, none)) (ofString "mpt_fail") [.const (BitVec.ofNat 64 11)]) = (fr_o, fp_o) := hfail_out
        rcases fr_o with _ | fr_some
        · exact absurd (congrArg Prod.fst hfail_out') hfail_not_none
        · have hidx_eq : evaluateHOLFiniteState s_idx idx_body = (some fr_some, fp_o) := by
            dsimp only [idx_body]
            rw [evaluateHOLFiniteState_seq_line780, hite_fail, hfail_out']
          have hs3_eq : evaluateHOLFiniteState s3 (.seq kal_ite (.return (.var .local (ofString "br")))) =
              (some fr_some,
               { fp_o with locals := HolFiniteMapExact.resVarEq fp_o.locals (ofString "idx", s3.locals.lookup (ofString "idx")) }) := by
            rw [evaluateHOLFiniteState_seq_line780, hite_kal_ne, hidx_eq]
          rw [hs3_eq] at hs3_res
          obtain ⟨eid, ev, hfail_exn, _, hstep_fail⟩ := mpt_fail_call_resumes hstep_idx.arena.1.code
            hstep_idx.arena hstep_idx.heap (by rw [hfail_out']; exact hs3_res)
          rw [hfail_out'] at hfail_exn hstep_fail
          dsimp only at hfail_exn hstep_fail
          injection hfail_exn with hfr_eq; subst hfr_eq
          apply hwrap_s3 (Nd_f := Nd2)
          · rw [hs3_eq]
            exact (NodeStep.trans hAR hstep_idx hstep_fail).with_locals_clock _ _
          · intro v hv; rw [hs3_eq] at hv; cases hv
      · -- `wslot_cur == 0`: skip `mpt_fail`, call `node_new_leaf`, store `lf` into `br`, return `br`!
        have hite_ok : evaluateHOLFiniteState s_idx
            (.ite (.cmp .notEqual
                (.load .one (.op .add [.var .local (ofString "br"), .const (BitVec.ofNat 64 32),
                  .panop .mul [.var .local (ofString "idx"), .const (BitVec.ofNat 64 8)]]))
                (.const (BitVec.ofNat 64 0)))
              (.call (some (none, none)) (ofString "mpt_fail") [.const (BitVec.ofNat 64 11)])
              .skip) = (none, s_idx) := by
          rw [evaluateHOLFiniteState_ite, hc_slot, if_neg hwslot_nz]; simp [evaluateHOLFiniteState_skip]
        set dc_lf : ProgHOL 64 :=
          .decCall (ofString "lf") .one (ofString "node_new_leaf")
            [.op .add [.var .local (ofString "rk"), .var .local (ofString "pl"), .const (BitVec.ofNat 64 1)],
             .op .sub [.var .local (ofString "kal"), .const (BitVec.ofNat 64 1)],
             .var .local (ofString "vptr"),
             .var .local (ofString "vlen")]
            (.store (.op .add [.var .local (ofString "br"), .const (BitVec.ofNat 64 32),
                .panop .mul [.var .local (ofString "idx"), .const (BitVec.ofNat 64 8)]])
              (.var .local (ofString "lf")))
        have hidx_eq_dc : evaluateHOLFiniteState s_idx idx_body = evaluateHOLFiniteState s_idx dc_lf := by
          dsimp only [idx_body]; rw [evaluateHOLFiniteState_seq_line780, hite_ok]
        have hsidx_rk : s_idx.locals.lookup (ofString "rk") = some (.val (.word wrk)) := by
          simp [s_idx, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_rk,
            show ofString "idx" ≠ ofString "rk" by decide]
        have hsidx_pl : s_idx.locals.lookup (ofString "pl") = some (.val (.word wpl)) := by
          simp [s_idx, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_pl,
            show ofString "idx" ≠ ofString "pl" by decide]
        have hsidx_kal : s_idx.locals.lookup (ofString "kal") = some (.val (.word wkal)) := by
          simp [s_idx, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_kal,
            show ofString "idx" ≠ ofString "kal" by decide]
        have hsidx_vptr : s_idx.locals.lookup (ofString "vptr") = some (.val (.word wvptr)) := by
          simp [s_idx, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_vptr,
            show ofString "idx" ≠ ofString "vptr" by decide]
        have hsidx_vlen : s_idx.locals.lookup (ofString "vlen") = some (.val (.word wvlen)) := by
          simp [s_idx, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_vlen,
            show ofString "idx" ≠ ofString "vlen" by decide]
        have hdc_lf := evaluateHOLFiniteState_decCall_total s_idx (ofString "lf") .one (ofString "node_new_leaf")
          [.op .add [.var .local (ofString "rk"), .var .local (ofString "pl"), .const (BitVec.ofNat 64 1)],
           .op .sub [.var .local (ofString "kal"), .const (BitVec.ofNat 64 1)],
           .var .local (ofString "vptr"),
           .var .local (ofString "vlen")]
          (.store (.op .add [.var .local (ofString "br"), .const (BitVec.ofNat 64 32),
              .panop .mul [.var .local (ofString "idx"), .const (BitVec.ofNat 64 8)]])
            (.var .local (ofString "lf")))
        have hlf_args : evalListHOLFinite s_idx (h := fun a => Classical.propDecidable (s_idx.memaddrs a))
            [.op .add [.var .local (ofString "rk"), .var .local (ofString "pl"), .const (BitVec.ofNat 64 1)],
             .op .sub [.var .local (ofString "kal"), .const (BitVec.ofNat 64 1)],
             .var .local (ofString "vptr"),
             .var .local (ofString "vlen")] =
            some [.val (.word (wrk + (wpl + 1))), .val (.word (wkal - 1)), .val (.word wvptr), .val (.word wvlen)] := by
          rw [evalListHOLFinite_eq_toExact]
          simp [evalListHOLExact, evalHOLExact, hsidx_rk, hsidx_pl, hsidx_kal, hsidx_vptr, hsidx_vlen,
            valueIsWord, valueWord, wordOpHOL, wordOp]
        rw [hlf_args] at hdc_lf; dsimp only at hdc_lf
        have hsidx_code : s_idx.code = originalRuntimeCode := hstep_idx.arena.1.code
        rcases hlk_lf : lookupCodeHOLFinite s_idx.code.lookup (ofString "node_new_leaf")
            [.val (.word (wrk + (wpl + 1))), .val (.word (wkal - 1)), .val (.word wvptr), .val (.word wvlen)] with _ | ⟨lfb, lfc, lfr⟩
        · rw [hlk_lf] at hdc_lf; dsimp only at hdc_lf
          rw [evaluateHOLFiniteState_seq_line780, hite_kal_ne, hidx_eq_dc, hdc_lf] at hs3_res
          exact absurd hs3_res not_resumes_error
        · rw [hlk_lf] at hdc_lf; dsimp only at hdc_lf
          by_cases hcz_lf : s_idx.clock = 0
          · rw [if_pos hcz_lf] at hdc_lf
            rw [evaluateHOLFiniteState_seq_line780, hite_kal_ne, hidx_eq_dc, hdc_lf] at hs3_res
            rcases hs3_res with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
          · rw [if_neg hcz_lf] at hdc_lf
            have hlk_lf_code : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "node_new_leaf")
                [.val (.word (wrk + (wpl + 1))), .val (.word (wkal - 1)), .val (.word wvptr), .val (.word wvlen)] =
                some (lfb, lfc, lfr) := by rwa [← hsidx_code]
            obtain ⟨hbody_lf, hlf_nib⟩ := lookup_param_exact lookup_node_new_leaf hlk_lf_code
              [] "nib" .one [(ofString "nlen", .one), (ofString "vptr", .one), (ofString "vlen", .one)]
              [] (.val (.word (wrk + (wpl + 1)))) _ rfl rfl rfl (by decide)
            obtain ⟨_, hlf_nlen⟩ := lookup_param_exact lookup_node_new_leaf hlk_lf_code
              [(ofString "nib", .one)] "nlen" .one [(ofString "vptr", .one), (ofString "vlen", .one)]
              [_] (.val (.word (wkal - 1))) _ rfl rfl rfl (by decide)
            obtain ⟨_, hlf_vlen⟩ := lookup_param_exact lookup_node_new_leaf hlk_lf_code
              [(ofString "nib", .one), (ofString "nlen", .one), (ofString "vptr", .one)] "vlen" .one []
              [_, _, _] (.val (.word wvlen)) [] rfl rfl rfl (by decide)
            subst hbody_lf
            have hrem_lf := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite s_idx lfc)
              (sourceFnBody Guest.Software.guestFn_node_new_leaf)
            rcases hlf_run : evaluateHOLFiniteState (callEntryStateHOLFinite s_idx lfc)
                (sourceFnBody Guest.Software.guestFn_node_new_leaf) with ⟨lf_res, lf_post⟩
            have hfix_lf : fixClockHOLFinite (callEntryStateHOLFinite s_idx lfc)
                (evaluateHOLFiniteState (callEntryStateHOLFinite s_idx lfc)
                  (sourceFnBody Guest.Software.guestFn_node_new_leaf)) = (lf_res, lf_post) := by
              rw [hlf_run] at hrem_lf ⊢; simp [fixClockHOLFinite, Nat.not_lt.mpr hrem_lf]
            rw [hfix_lf, hlf_run] at hdc_lf; dsimp only at hdc_lf
            rcases lf_res with _ | lf_res'
            · rw [evaluateHOLFiniteState_seq_line780, hite_kal_ne, hidx_eq_dc, hdc_lf] at hs3_res
              exact absurd hs3_res not_resumes_error
            · cases lf_res' with
              | returned lf_rv =>
                dsimp only at hdc_lf
                by_cases hsh_lf : (shapeEqHOL (shapeOfHOLExact lf_rv) .one && shapeEqHOL (shapeOfHOLExact lf_rv) lfr) = true
                · rw [if_pos hsh_lf] at hdc_lf
                  have hsub_rk : KeyIn s_idx Nd2 (wrk + (wpl + 1)).toNat (wkal - 1).toNat := by
                    have hk_idx : KeyIn s_idx Nd2 (wrk + wpl).toNat wkal.toNat := hkey_rk_pl
                    have heq1 : (wkal - 1).toNat = wkal.toNat - 1 :=
                      BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; change 1 ≤ wkal.toNat; omega)
                    have heq2 : BitVec.ofNat 64 (wrk + wpl).toNat + BitVec.ofNat 64 1 = wrk + (wpl + 1) := by
                      have h0 : BitVec.ofNat 64 (wrk + wpl).toNat = wrk + wpl := by
                        apply BitVec.eq_of_toNat_eq; simp [Nat.mod_eq_of_lt (wrk + wpl).isLt]
                      rw [h0]
                      exact BitVec.add_assoc wrk wpl 1
                    rw [← heq2, heq1]
                    exact keyIn_subslice hk_idx (by omega)
                  obtain ⟨Nd_lf, hstep_lf, hret_lf⟩ := nodeStep_of_nodeFn nf_node_new_leaf s_idx hsidx_code
                    hstep_idx.arena hstep_idx.heap hlk_lf
                    (by intro _ h; simp at h)
                    (by
                      have h1 : locN (callEntryStateHOLFinite s_idx lfc) "nib" = (wrk + (wpl + 1)).toNat := by
                        simp [locN, callEntryStateHOLFinite, hlf_nib]
                      have h2 : locN (callEntryStateHOLFinite s_idx lfc) "nlen" = (wkal - 1).toNat := by
                        simp [locN, callEntryStateHOLFinite, hlf_nlen]
                      have h3 : locN (callEntryStateHOLFinite s_idx lfc) "vlen" = wvlen.toNat := by
                        simp [locN, callEntryStateHOLFinite, hlf_vlen]
                      rw [h1, h2, h3]
                      exact ⟨hsub_rk, hwvlen_lt⟩)
                    (by rw [hlf_run]; exact Or.inl ⟨lf_rv, rfl⟩)
                  rw [hlf_run] at hstep_lf hret_lf; dsimp only at hstep_lf hret_lf
                  obtain ⟨wlf, rfl, hwlf_root⟩ := hret_lf lf_rv rfl
                  set st_lf := setVarHOLFinite (ofString "lf") (.val (.word wlf)) { lf_post with locals := s_idx.locals }
                  have hstep_lf' : NodeStep s_idx st_lf Nd2 Nd_lf := hstep_lf.with_locals_clock _ _
                  have hbr_in_lf : wbr.toNat ∈ Nd_lf := hstep_lf'.sub wbr.toNat hbr_in2
                  have hbr_k_lf : memW st_lf wbr.toNat = 3 := (hstep_lf'.kinds wbr.toNat hbr_in2).trans hbr_k2
                  obtain ⟨hdom_slot_lf, hstep_st_lf, _⟩ :=
                    branch_store_child_step hstep_lf'.arena hstep_lf'.heap hbr_in_lf hbr_k_lf hwidx_lt hwlf_root
                  set m_lf := Wave8Contracts.M26.updW st_lf.memory (wbr + BitVec.ofNat 64 32 + widx * BitVec.ofNat 64 8) wlf
                  set st_lf2 : PanSemStateFiniteExact 64 F := { st_lf with memory := m_lf }
                  have hstlf_br : st_lf.locals.lookup (ofString "br") = some (.val (.word wbr)) := by
                    simp [st_lf, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsidx_br,
                      show ofString "lf" ≠ ofString "br" by decide]
                  have hstlf_idx : st_lf.locals.lookup (ofString "idx") = some (.val (.word widx)) := by
                    simp [st_lf, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsidx_idx,
                      show ofString "lf" ≠ ofString "idx" by decide]
                  have hstlf_lf : st_lf.locals.lookup (ofString "lf") = some (.val (.word wlf)) := by
                    simp [st_lf, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                  have hst_eval_lf : evaluateHOLFiniteState st_lf
                      (.store (.op .add [.var .local (ofString "br"), .const (BitVec.ofNat 64 32),
                          .panop .mul [.var .local (ofString "idx"), .const (BitVec.ofNat 64 8)]])
                        (.var .local (ofString "lf"))) = (none, st_lf2) := by
                    rw [evaluateHOLFiniteState_store]
                    rw [eval_slot_var hstlf_br hstlf_idx]
                    have hlf_ev : @evalHOLExact 64 F _ st_lf.toExact (fun a => Classical.propDecidable (st_lf.memaddrs a))
                        (.var .local (ofString "lf")) = some (.val (.word wlf)) := hstlf_lf
                    rw [hlf_ev]
                    simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL, hdom_slot_lf, ↓reduceIte]
                    rfl
                  rw [hst_eval_lf] at hdc_lf; dsimp only at hdc_lf
                  set loc_sak :=
                    HolFiniteMapExact.resVarEq
                      (HolFiniteMapExact.resVarEq st_lf.locals (ofString "lf", s_idx.locals.lookup (ofString "lf")))
                      (ofString "idx", s3.locals.lookup (ofString "idx"))
                  set s_after_kal : PanSemStateFiniteExact 64 F :=
                    { st_lf2 with locals := loc_sak }
                  have hkal_eq : evaluateHOLFiniteState s3 kal_ite = (none, s_after_kal) := by
                    rw [hite_kal_ne, hidx_eq_dc, hdc_lf]
                  have hsak_br : s_after_kal.locals.lookup (ofString "br") = some (.val (.word wbr)) := by
                    dsimp only [s_after_kal, loc_sak]
                    rw [resVarEq_lookup_ne _ _ _ _ (by decide), resVarEq_lookup_ne _ _ _ _ (by decide)]
                    exact hstlf_br
                  have hret_sak : evaluateHOLFiniteState s_after_kal (.return (.var .local (ofString "br"))) =
                      (some (.returned (.val (.word wbr))), emptyLocalsHOLFinite s_after_kal) := by
                    simp [evaluateHOLFiniteState_return, evalHOLExact, hsak_br, shapeOfHOLExact, sizeOfShapeWithContextHOL]
                  have hs3_done : evaluateHOLFiniteState s3 (.seq kal_ite (.return (.var .local (ofString "br")))) =
                      (some (.returned (.val (.word wbr))), emptyLocalsHOLFinite s_after_kal) := by
                    rw [evaluateHOLFiniteState_seq_line780, hkal_eq]; dsimp only; exact hret_sak
                  apply hwrap_s3 (Nd_f := Nd_lf)
                  · rw [hs3_done]
                    exact ((NodeStep.trans hAR hstep_idx (NodeStep.trans hstep_idx.arena hstep_lf' hstep_st_lf)).with_locals_clock _ _).with_locals_clock _ _
                  · intro v hv; rw [hs3_done] at hv; injection hv with h1; injection h1 with h2; subst h2
                    exact ⟨wbr, rfl, Or.inr hbr_in_lf⟩
                · rw [if_neg hsh_lf] at hdc_lf
                  rw [evaluateHOLFiniteState_seq_line780, hite_kal_ne, hidx_eq_dc, hdc_lf] at hs3_res
                  exact absurd hs3_res not_resumes_error
              | exception eid ev =>
                dsimp only at hdc_lf
                rw [evaluateHOLFiniteState_seq_line780, hite_kal_ne, hidx_eq_dc, hdc_lf] at hs3_res
                rcases hs3_res with ⟨_, h⟩ | ⟨eid', ev', h, hne_tr⟩
                · simp at h
                · injection h with h1; injection h1 with he1 he2; subst he1 he2
                  exact absurd (congrArg Prod.fst hlf_run)
                    (node_new_leaf_no_nonTrap_exn (callEntryStateHOLFinite s_idx lfc) hsidx_code eid ev hne_tr)
              | _ =>
                rw [evaluateHOLFiniteState_seq_line780, hite_kal_ne, hidx_eq_dc, hdc_lf] at hs3_res
                rcases hs3_res with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h

end InitECandidate.Solver.Wave8GuestInv.R16Shards
