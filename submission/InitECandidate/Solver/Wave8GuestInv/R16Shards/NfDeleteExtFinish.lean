import InitECandidate.Solver.Wave8GuestInv.R16Shards.NibblesConcatHelper

/-! `nf__delete_ext_finish`: `_delete_ext_finish(node, seg, sl, nc)` preserves typed node heaps
(`NodeFn ["node", "nc"]` under `NodeKind s Nd "node" 2 ∧ KeyIn s Nd (locN s "seg") (locN s "sl")`). -/

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
open InitECandidate.Solver.Wave8GuestInv.R14Shards

/-- `_delete_ext_finish` (AST line 10727): typed nodes in, typed nodes out (MPT tier);
requirement: `NodeKind s Nd "node" 2 ∧ KeyIn s Nd (locN s "seg") (locN s "sl")`. -/
theorem «nf__delete_ext_finish» :
    NodeFn ["node", "nc"]
    (fun s Nd =>
      NodeKind s Nd "node" 2 ∧ KeyIn s Nd (locN s "seg") (locN s "sl"))
    (ofString "_delete_ext_finish") := by
  refine ⟨_, _, _, lookup__delete_ext_finish, ?_⟩
  intro F s hcode hP ⟨callVals, hcallL⟩ _hnt hres
  have hAR : ArenaReady s := hP.1
  obtain ⟨Nd_wit, hNd_wit, hroots_wit, hnk_wit, hkseg_wit⟩ := hP.2
  obtain ⟨wnode, hlk_node, hloc_node⟩ := lookup_param_word lookup__delete_ext_finish hcallL
    [] "node" [(ofString "seg", .one), (ofString "sl", .one), (ofString "nc", .one)]
    rfl (by decide)
  obtain ⟨wseg, hlk_seg, hloc_seg⟩ := lookup_param_word lookup__delete_ext_finish hcallL
    [(ofString "node", .one)] "seg" [(ofString "sl", .one), (ofString "nc", .one)]
    rfl (by decide)
  obtain ⟨wsl, hlk_sl, hloc_sl⟩ := lookup_param_word lookup__delete_ext_finish hcallL
    [(ofString "node", .one), (ofString "seg", .one)] "sl" [(ofString "nc", .one)]
    rfl (by decide)
  obtain ⟨wnc, hlk_nc, hloc_nc⟩ := lookup_param_word lookup__delete_ext_finish hcallL
    [(ofString "node", .one), (ofString "seg", .one), (ofString "sl", .one)] "nc" []
    rfl (by decide)
  set res := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn__delete_ext_finish)).1
  set post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn__delete_ext_finish)).2
  suffices hmain : ∀ Nd, NodeHeap s Nd →
      RootIn Nd wnc.toNat → NodeKind s Nd "node" 2 →
      KeyIn s Nd (locN s "seg") (locN s "sl") →
      ∃ Nd', NodeStep s post Nd Nd' ∧
        ∀ v, res = some (.returned v) → ∃ w : BitVec 64, v = .val (.word w) ∧ RootIn Nd' w.toNat by
    have hnc_wit : RootIn Nd_wit wnc.toNat := by
      have := hroots_wit "nc" (by simp)
      rwa [hloc_nc s rfl] at this
    obtain ⟨Nd0', hns0, _⟩ := hmain Nd_wit hNd_wit hnc_wit hnk_wit hkseg_wit
    refine ⟨hns0.arena, hns0.hp_le, hns0.sp_le, ?_⟩
    intro Nd hNd hroots ⟨hnk, hkseg⟩
    have hnc_root : RootIn Nd wnc.toNat := by
      have := hroots "nc" (by simp)
      rwa [hloc_nc s rfl] at this
    obtain ⟨Nd', hns, hret⟩ := hmain Nd hNd hnc_root hnk hkseg
    exact ⟨Nd', hns.heap, hns.sub, hns.kinds, hns.fresh, hns.frame, hns.globals, hret⟩
  intro Nd hNd hnc_root hnk hkseg
  have hnode_in : wnode.toNat ∈ Nd := by rw [← hloc_node s rfl]; exact hnk.1
  have hnode_k2 : memW s wnode.toNat = 2 := by rw [← hloc_node s rfl]; exact hnk.2
  have hp_node := hNd.1 wnode.toNat hnode_in
  have hkey_seg : KeyIn s Nd wseg.toNat wsl.toNat := by
    rwa [hloc_seg s rfl, hloc_sl s rfl] at hkseg
  have hhl_lt : heapLimit < 2 ^ 64 := by decide
  have hbody : sourceFnBody Guest.Software.guestFn__delete_ext_finish =
      .seq
        (.ite (.cmp .equal (.var .local (ofString "nc")) (.const (BitVec.ofNat 64 0)))
          (.return (.const (BitVec.ofNat 64 0)))
          .skip)
        (.dec (ofString "ck") .one (.load .one (.op .add [.var .local (ofString "nc"), .const (BitVec.ofNat 64 0)]))
          (.seq
            (.ite (.cmp .equal (.var .local (ofString "ck")) (.const (BitVec.ofNat 64 3)))
              (.seq
                (.store (.op .add [.var .local (ofString "node"), .const (BitVec.ofNat 64 48)]) (.var .local (ofString "nc")))
                (.return (.var .local (ofString "node"))))
              .skip)
            (.seq
              (.ite (.cmp .equal (.var .local (ofString "ck")) (.const (BitVec.ofNat 64 0)))
                (.call (some (none, none)) (ofString "mpt_fail") [.const (BitVec.ofNat 64 2)])
                .skip)
              (.decCall (ofString "cat") .one (ofString "nibbles_concat")
                [.var .local (ofString "seg"), .var .local (ofString "sl"),
                 .load .one (.op .add [.var .local (ofString "nc"), .const (BitVec.ofNat 64 32)]),
                 .load .one (.op .add [.var .local (ofString "nc"), .const (BitVec.ofNat 64 40)])]
                (.dec (ofString "cl") .one
                  (.op .add [.var .local (ofString "sl"),
                    .load .one (.op .add [.var .local (ofString "nc"), .const (BitVec.ofNat 64 40)])])
                  (.seq
                    (.ite (.cmp .equal (.var .local (ofString "ck")) (.const (BitVec.ofNat 64 2)))
                      (.call none (ofString "node_new_ext")
                        [.var .local (ofString "cat"), .var .local (ofString "cl"),
                         .load .one (.op .add [.var .local (ofString "nc"), .const (BitVec.ofNat 64 48)])])
                      .skip)
                    (.call none (ofString "node_new_leaf")
                      [.var .local (ofString "cat"), .var .local (ofString "cl"),
                       .load .one (.op .add [.var .local (ofString "nc"), .const (BitVec.ofNat 64 48)]),
                       .load .one (.op .add [.var .local (ofString "nc"), .const (BitVec.ofNat 64 56)])]))))))) := rfl
  -- Step 1: check `nc == 0`
  have hc_nc0 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .equal (.var .local (ofString "nc")) (.const (BitVec.ofNat 64 0))) =
      some (.val (.word (if wnc = 0 then 1 else 0))) := by
    simp [evalHOLExact, hlk_nc, Compiler.Encoders.Asm.wordCmpHOL]
  by_cases hnc0 : wnc = 0
  · -- Branch 1: `nc == 0` -> `return 0`!
    have hite_nc0 : evaluateHOLFiniteState s
        (.ite (.cmp .equal (.var .local (ofString "nc")) (.const (BitVec.ofNat 64 0)))
          (.return (.const (BitVec.ofNat 64 0)))
          .skip) =
        (some (.returned (.val (.word 0))), emptyLocalsHOLFinite s) := by
      rw [evaluateHOLFiniteState_ite, hc_nc0, if_pos hnc0]
      simp [evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL]
    have hout_eq : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn__delete_ext_finish) =
        (some (.returned (.val (.word 0))), emptyLocalsHOLFinite s) := by
      rw [hbody, evaluateHOLFiniteState_seq_line780, hite_nc0]
    refine ⟨Nd, ?_, ?_⟩
    · change NodeStep s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn__delete_ext_finish)).2 Nd Nd
      rw [hout_eq]; exact (NodeStep.refl hAR hNd).with_locals_clock _ _
    · intro v hv
      change (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn__delete_ext_finish)).1 = _ at hv
      rw [hout_eq] at hv; injection hv with h1; injection h1 with h2; subst h2
      exact ⟨0, rfl, Or.inl rfl⟩
  · -- `nc != 0`, so `wnc.toNat ∈ Nd`!
    have hwnc_nz_nat : wnc.toNat ≠ 0 := fun hz => hnc0 (BitVec.eq_of_toNat_eq hz)
    have hnc_in : wnc.toNat ∈ Nd := hnc_root.resolve_left hwnc_nz_nat
    have hp_nc := hNd.1 wnc.toNat hnc_in
    obtain ⟨hsz_nc32, _, _⟩ := nodeSize_bounds (memW s wnc.toNat)
    have hnc_ins := hp_nc.2.2.1
    have hnc_add : ∀ k : Nat, k < nodeSize (memW s wnc.toNat) →
        wnc + BitVec.ofNat 64 k = BitVec.ofNat 64 (wnc.toNat + k) ∧
        (wnc + BitVec.ofNat 64 k).toNat = wnc.toNat + k := by
      intro k hk
      have hlt : wnc.toNat + k < 2 ^ 64 := by dsimp [Inside, nodeIvl] at hnc_ins; omega
      have heq : wnc + BitVec.ofNat 64 k = BitVec.ofNat 64 (wnc.toNat + k) := by
        apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      exact ⟨heq, by rw [heq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]⟩
    have hload_nc_off : ∀ (st : PanSemStateFiniteExact 64 F) (k : Nat),
        (∀ c : BitVec 64, c.toNat < globN s "heap_ptr" → st.memory c = s.memory c) →
        st.memaddrs = s.memaddrs →
        st.locals.lookup (ofString "nc") = some (.val (.word wnc)) →
        k < nodeSize (memW s wnc.toNat) → k % 8 = 0 →
        @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a))
          (.load .one (.op .add [.var .local (ofString "nc"), .const (BitVec.ofNat 64 k)])) =
          some (.val (.word (BitVec.ofNat 64 (memW s (wnc.toNat + k))))) := by
      intro st k hmem_lt hma hnc_lk hk hk8
      have hnc_in_hp : Inside (nodeIvl s wnc.toNat) sourceBase (globN s "heap_ptr") := by
        rcases hp_nc.2.1 with h1 | h2
        · exact h1
        · have := hp_nc.2.2.1.2; have := hAR.2.2.2.1; have := hAR.2.2.2.2.1
          have hsep : heapLimit ≤ scratchStart := by decide
          dsimp [nodeIvl, Inside] at *; omega
      obtain ⟨w_at, hdom_at, hm_at⟩ := hp_nc.2.2.2.1.2.2 (k / 8) (by dsimp [nodeIvl]; omega)
      dsimp [nodeIvl] at hdom_at hm_at
      have hmul : wnc.toNat + 8 * (k / 8) = wnc.toNat + k := by omega
      rw [hmul] at hdom_at hm_at
      have hdom_st : st.memaddrs (wnc + BitVec.ofNat 64 k) := by
        rw [hma, (hnc_add k hk).1]; exact hdom_at
      have hm_st : st.memory (wnc + BitVec.ofNat 64 k) = .word w_at := by
        rw [hmem_lt _ (by rw [(hnc_add k hk).2]; dsimp [nodeIvl, Inside] at hnc_in_hp; omega),
            (hnc_add k hk).1]
        exact hm_at
      have hmw_eq : BitVec.ofNat 64 (memW s (wnc.toNat + k)) = w_at := by
        unfold memW; rw [hm_at]; simp
      simp [evalHOLExact, evalListHOLExact, hnc_lk, valueIsWord, valueWord, wordOpHOL, wordOp,
        isWfShapeExactHOL, memLoadHOLExact, hdom_st, hm_st, hmw_eq]
    have hite_nc_skip : evaluateHOLFiniteState s
        (.ite (.cmp .equal (.var .local (ofString "nc")) (.const (BitVec.ofNat 64 0)))
          (.return (.const (BitVec.ofNat 64 0)))
          .skip) = (none, s) := by
      rw [evaluateHOLFiniteState_ite, hc_nc0, if_neg hnc0]; simp [evaluateHOLFiniteState_skip]
    -- Step 2: `dec ck := load(nc + 0)`
    set wck : BitVec 64 := BitVec.ofNat 64 (memW s (wnc.toNat + 0))
    have hwck_le3 : memW s wnc.toNat ≤ 3 := hp_nc.1
    have hwck_nat : wck.toNat = memW s wnc.toNat := by
      dsimp [wck]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hev_ck : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.load .one (.op .add [.var .local (ofString "nc"), .const (BitVec.ofNat 64 0)])) =
        some (.val (.word wck)) :=
      hload_nc_off s 0 (fun _ _ => rfl) rfl hlk_nc (by omega) (by decide)
    set s_ck := setVarHOLFinite (ofString "ck") (.val (.word wck)) s
    set ck_body : ProgHOL 64 :=
      .seq
        (.ite (.cmp .equal (.var .local (ofString "ck")) (.const (BitVec.ofNat 64 3)))
          (.seq
            (.store (.op .add [.var .local (ofString "node"), .const (BitVec.ofNat 64 48)]) (.var .local (ofString "nc")))
            (.return (.var .local (ofString "node"))))
          .skip)
        (.seq
          (.ite (.cmp .equal (.var .local (ofString "ck")) (.const (BitVec.ofNat 64 0)))
            (.call (some (none, none)) (ofString "mpt_fail") [.const (BitVec.ofNat 64 2)])
            .skip)
          (.decCall (ofString "cat") .one (ofString "nibbles_concat")
            [.var .local (ofString "seg"), .var .local (ofString "sl"),
             .load .one (.op .add [.var .local (ofString "nc"), .const (BitVec.ofNat 64 32)]),
             .load .one (.op .add [.var .local (ofString "nc"), .const (BitVec.ofNat 64 40)])]
            (.dec (ofString "cl") .one
              (.op .add [.var .local (ofString "sl"),
                .load .one (.op .add [.var .local (ofString "nc"), .const (BitVec.ofNat 64 40)])])
              (.seq
                (.ite (.cmp .equal (.var .local (ofString "ck")) (.const (BitVec.ofNat 64 2)))
                  (.call none (ofString "node_new_ext")
                    [.var .local (ofString "cat"), .var .local (ofString "cl"),
                     .load .one (.op .add [.var .local (ofString "nc"), .const (BitVec.ofNat 64 48)])])
                  .skip)
                (.call none (ofString "node_new_leaf")
                  [.var .local (ofString "cat"), .var .local (ofString "cl"),
                   .load .one (.op .add [.var .local (ofString "nc"), .const (BitVec.ofNat 64 48)]),
                   .load .one (.op .add [.var .local (ofString "nc"), .const (BitVec.ofNat 64 56)])])))))
    have hbody_ck : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn__delete_ext_finish)).1 =
        (evaluateHOLFiniteState s_ck ck_body).1 ∧
        (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn__delete_ext_finish)).2 =
        { (evaluateHOLFiniteState s_ck ck_body).2 with
          locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState s_ck ck_body).2.locals
            (ofString "ck", s.locals.lookup (ofString "ck")) } := by
      rw [hbody, evaluateHOLFiniteState_seq_line780, hite_nc_skip]
      dsimp only
      rw [evaluateHOLFiniteState_dec_total]
      dsimp only
      rw [hev_ck]
      simp [shapeEqHOL, shapeOfHOLExact, s_ck]
    have hsck_res : Resumes (evaluateHOLFiniteState s_ck ck_body).1 := by
      rw [← hbody_ck.1]; exact hres
    have hsck_ck : s_ck.locals.lookup (ofString "ck") = some (.val (.word wck)) := by
      simp [s_ck, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hsck_node : s_ck.locals.lookup (ofString "node") = some (.val (.word wnode)) := by
      simp [s_ck, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlk_node,
        show ofString "ck" ≠ ofString "node" by decide]
    have hsck_seg : s_ck.locals.lookup (ofString "seg") = some (.val (.word wseg)) := by
      simp [s_ck, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlk_seg,
        show ofString "ck" ≠ ofString "seg" by decide]
    have hsck_sl : s_ck.locals.lookup (ofString "sl") = some (.val (.word wsl)) := by
      simp [s_ck, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlk_sl,
        show ofString "ck" ≠ ofString "sl" by decide]
    have hsck_nc : s_ck.locals.lookup (ofString "nc") = some (.val (.word wnc)) := by
      simp [s_ck, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlk_nc,
        show ofString "ck" ≠ ofString "nc" by decide]
    -- Step 3: check `ck == 3`
    have hc_ck3 : @evalHOLExact 64 F _ s_ck.toExact (fun a => Classical.propDecidable (s_ck.memaddrs a))
        (.cmp .equal (.var .local (ofString "ck")) (.const (BitVec.ofNat 64 3))) =
        some (.val (.word (if wck = 3 then 1 else 0))) := by
      simp [evalHOLExact, hsck_ck, Compiler.Encoders.Asm.wordCmpHOL]
    by_cases hck3 : wck = 3
    · -- Branch 2: `ck == 3` -> `st node + 48, nc; return node`!
      have hsz_nd2 : nodeSize (memW s wnode.toNat) = 56 := by simp [nodeSize, hnode_k2]
      have hnd_ins := hp_node.2.2.1
      have hnd48_lt : wnode.toNat + 48 < 2 ^ 64 := by dsimp [Inside, nodeIvl] at hnd_ins; omega
      have hnd48_eq : wnode + BitVec.ofNat 64 48 = BitVec.ofNat 64 (wnode.toNat + 48) ∧
          (wnode + BitVec.ofNat 64 48).toNat = wnode.toNat + 48 := by
        have heq : wnode + BitVec.ofNat 64 48 = BitVec.ofNat 64 (wnode.toNat + 48) := by
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
        exact ⟨heq, by rw [heq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnd48_lt]⟩
      have hdom48 : s_ck.memaddrs (wnode + BitVec.ofNat 64 48) := by
        obtain ⟨_, hd, _⟩ := hp_node.2.2.2.1.2.2 6 (by dsimp [nodeIvl]; omega)
        dsimp [nodeIvl] at hd
        change s.memaddrs (wnode + BitVec.ofNat 64 48)
        rw [hnd48_eq.1]; exact hd
      set m_st := Wave8Contracts.M26.updW s.memory (wnode + BitVec.ofNat 64 48) wnc
      have hst_eval : evaluateHOLFiniteState s_ck
          (.seq
            (.store (.op .add [.var .local (ofString "node"), .const (BitVec.ofNat 64 48)]) (.var .local (ofString "nc")))
            (.return (.var .local (ofString "node")))) =
          (some (.returned (.val (.word wnode))), emptyLocalsHOLFinite { s_ck with memory := m_st }) := by
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_store]
        have hd : @evalHOLExact 64 F _ s_ck.toExact (fun a => Classical.propDecidable (s_ck.memaddrs a))
            (.op .add [.var .local (ofString "node"), .const (BitVec.ofNat 64 48)]) =
            some (.val (.word (wnode + BitVec.ofNat 64 48))) := by
          simp [evalHOLExact, evalListHOLExact, hsck_node, valueIsWord, valueWord, wordOpHOL, wordOp]
        have he : @evalHOLExact 64 F _ s_ck.toExact (fun a => Classical.propDecidable (s_ck.memaddrs a))
            (.var .local (ofString "nc")) = some (.val (.word wnc)) := hsck_nc
        rw [hd, he]
        simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL, hdom48, ↓reduceIte]
        rw [evaluateHOLFiniteState_return]
        simp [evalHOLExact, hsck_node, shapeOfHOLExact, sizeOfShapeWithContextHOL]
        rfl
      have hck_eval : evaluateHOLFiniteState s_ck ck_body =
          (some (.returned (.val (.word wnode))), emptyLocalsHOLFinite { s_ck with memory := m_st }) := by
        dsimp only [ck_body]
        rw [evaluateHOLFiniteState_seq_line780]
        have hite3 : evaluateHOLFiniteState s_ck
            (.ite (.cmp .equal (.var .local (ofString "ck")) (.const (BitVec.ofNat 64 3)))
              (.seq
                (.store (.op .add [.var .local (ofString "node"), .const (BitVec.ofNat 64 48)]) (.var .local (ofString "nc")))
                (.return (.var .local (ofString "node"))))
              .skip) =
            (some (.returned (.val (.word wnode))), emptyLocalsHOLFinite { s_ck with memory := m_st }) := by
          rw [evaluateHOLFiniteState_ite, hc_ck3, if_pos hck3]
          dsimp only
          have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
          rw [if_neg h10]
          exact hst_eval
        rw [hite3]
      have hmw_other : ∀ off : Nat, off < 48 →
          memW ({ s with memory := m_st } : PanSemStateFiniteExact 64 F) (wnode.toNat + off) = memW s (wnode.toNat + off) := by
        intro off hoff
        have hlt : wnode.toNat + off < 2 ^ 64 := by omega
        have hne : BitVec.ofNat 64 (wnode.toNat + off) ≠ wnode + BitVec.ofNat 64 48 := by
          intro heq
          have := congrArg BitVec.toNat heq
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt, hnd48_eq.2] at this
          omega
        unfold memW; simp [m_st, Wave8Contracts.M26.updW, if_neg hne]
      have hmw_48 : memW ({ s with memory := m_st } : PanSemStateFiniteExact 64 F) (wnode.toNat + 48) = wnc.toNat := by
        unfold memW; rw [← hnd48_eq.1]; simp [m_st, Wave8Contracts.M26.updW]
      have hstep_mod : NodeStep s { s with memory := m_st } Nd Nd := by
        refine nodeStep_modify_node hAR hNd hnode_in rfl rfl rfl rfl rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_
        · intro a hout
          by_cases ha48 : a = wnode + BitVec.ofNat 64 48
          · exfalso; apply hout; rw [ha48, hnd48_eq.2, hsz_nd2]; omega
          · simp [m_st, Wave8Contracts.M26.updW, if_neg ha48]
        · intro _; rw [hmw_48]; exact Or.inr hnc_in
        · rw [hnode_k2]; intro h; cases h
        · intro _; exact ⟨hmw_other 32 (by decide), hmw_other 40 (by decide)⟩
        · rw [hmw_other 16 (by decide)]; exact hp_node.2.2.2.2.2.2.2.1
        · rw [hnode_k2]; intro h; cases h
        · rw [hnode_k2]; intro h; cases h
      refine ⟨Nd, ?_, ?_⟩
      · change NodeStep s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn__delete_ext_finish)).2 Nd Nd
        rw [hbody_ck.2, hck_eval]
        exact (hstep_mod.with_locals_clock _ _).with_locals_clock _ _
      · intro v hv
        change (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn__delete_ext_finish)).1 = _ at hv
        rw [hbody_ck.1, hck_eval] at hv
        injection hv with h1; injection h1 with h2; subst h2
        exact ⟨wnode, rfl, Or.inr hnode_in⟩
    · -- `ck != 3`
      have hite_ck3_skip : evaluateHOLFiniteState s_ck
          (.ite (.cmp .equal (.var .local (ofString "ck")) (.const (BitVec.ofNat 64 3)))
            (.seq
              (.store (.op .add [.var .local (ofString "node"), .const (BitVec.ofNat 64 48)]) (.var .local (ofString "nc")))
              (.return (.var .local (ofString "node"))))
            .skip) = (none, s_ck) := by
        rw [evaluateHOLFiniteState_ite, hc_ck3, if_neg hck3]; simp [evaluateHOLFiniteState_skip]
      -- Step 4: check `ck == 0`
      have hc_ck0 : @evalHOLExact 64 F _ s_ck.toExact (fun a => Classical.propDecidable (s_ck.memaddrs a))
          (.cmp .equal (.var .local (ofString "ck")) (.const (BitVec.ofNat 64 0))) =
          some (.val (.word (if wck = 0 then 1 else 0))) := by
        simp [evalHOLExact, hsck_ck, Compiler.Encoders.Asm.wordCmpHOL]
      by_cases hck0 : wck = 0
      · -- Branch 3: `ck == 0` -> `mpt_fail(2)`!
        have hite_ck0 : evaluateHOLFiniteState s_ck
            (.ite (.cmp .equal (.var .local (ofString "ck")) (.const (BitVec.ofNat 64 0)))
              (.call (some (none, none)) (ofString "mpt_fail") [.const (BitVec.ofNat 64 2)])
              .skip) =
            evaluateHOLFiniteState s_ck
              (.call (some (none, none)) (ofString "mpt_fail") [.const (BitVec.ofNat 64 2)]) := by
          rw [evaluateHOLFiniteState_ite, hc_ck0, if_pos hck0]; simp
        have hfail_nn := mpt_fail_ne_none s_ck hcode (.const (BitVec.ofNat 64 2))
        rcases hfail_out : evaluateHOLFiniteState s_ck
            (.call (some (none, none)) (ofString "mpt_fail") [.const (BitVec.ofNat 64 2)]) with ⟨fr_o, fp_o⟩
        have hfail_out' : evaluateHOLFiniteState s_ck
            (.call (some (none, none)) (ofString "mpt_fail") [.const (BitVec.ofNat 64 2)]) = (fr_o, fp_o) := hfail_out
        rcases fr_o with _ | fr_some
        · exact absurd (congrArg Prod.fst hfail_out') hfail_nn
        · have hck_eq : evaluateHOLFiniteState s_ck ck_body = (some fr_some, fp_o) := by
            dsimp only [ck_body]
            rw [evaluateHOLFiniteState_seq_line780, hite_ck3_skip]
            dsimp only
            rw [evaluateHOLFiniteState_seq_line780, hite_ck0, hfail_out']
          rw [hck_eq] at hsck_res
          have hsck_AR : ArenaReady s_ck := localsFree_arenaReady s _ _ hAR
          have hsck_code : s_ck.code = originalRuntimeCode := hcode
          obtain ⟨eid, ev, hfail_exn, _, hstep_fail⟩ := mpt_fail_call_resumes hsck_code hsck_AR hNd
            (by rw [hfail_out']; exact hsck_res)
          rw [hfail_out'] at hfail_exn hstep_fail
          dsimp only at hfail_exn hstep_fail
          injection hfail_exn with hfr_eq; subst hfr_eq
          refine ⟨Nd, ?_, ?_⟩
          · change NodeStep s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn__delete_ext_finish)).2 Nd Nd
            rw [hbody_ck.2, hck_eq]
            exact (NodeStep.from_locals_clock hstep_fail).with_locals_clock _ _
          · intro v hv
            change (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn__delete_ext_finish)).1 = _ at hv
            rw [hbody_ck.1, hck_eq] at hv; cases hv
      · -- `ck ∈ {1, 2}`!
        have hwck_12 : memW s wnc.toNat = 1 ∨ memW s wnc.toNat = 2 := by
          have hne0 : memW s wnc.toNat ≠ 0 := by
            intro h0; apply hck0; apply BitVec.eq_of_toNat_eq; rw [hwck_nat]; exact h0
          have hne3 : memW s wnc.toNat ≠ 3 := by
            intro h3; apply hck3; apply BitVec.eq_of_toNat_eq; rw [hwck_nat]; simpa using h3
          omega
        have hsz_nc56 : 56 ≤ nodeSize (memW s wnc.toNat) := by
          rcases hwck_12 with hk1 | hk2 <;> simp [nodeSize, *]
        have hite_ck0_skip : evaluateHOLFiniteState s_ck
            (.ite (.cmp .equal (.var .local (ofString "ck")) (.const (BitVec.ofNat 64 0)))
              (.call (some (none, none)) (ofString "mpt_fail") [.const (BitVec.ofNat 64 2)])
              .skip) = (none, s_ck) := by
          rw [evaluateHOLFiniteState_ite, hc_ck0, if_neg hck0]; simp [evaluateHOLFiniteState_skip]
        set dc_cat : ProgHOL 64 :=
          .decCall (ofString "cat") .one (ofString "nibbles_concat")
            [.var .local (ofString "seg"), .var .local (ofString "sl"),
             .load .one (.op .add [.var .local (ofString "nc"), .const (BitVec.ofNat 64 32)]),
             .load .one (.op .add [.var .local (ofString "nc"), .const (BitVec.ofNat 64 40)])]
            (.dec (ofString "cl") .one
              (.op .add [.var .local (ofString "sl"),
                .load .one (.op .add [.var .local (ofString "nc"), .const (BitVec.ofNat 64 40)])])
              (.seq
                (.ite (.cmp .equal (.var .local (ofString "ck")) (.const (BitVec.ofNat 64 2)))
                  (.call none (ofString "node_new_ext")
                    [.var .local (ofString "cat"), .var .local (ofString "cl"),
                     .load .one (.op .add [.var .local (ofString "nc"), .const (BitVec.ofNat 64 48)])])
                  .skip)
                (.call none (ofString "node_new_leaf")
                  [.var .local (ofString "cat"), .var .local (ofString "cl"),
                   .load .one (.op .add [.var .local (ofString "nc"), .const (BitVec.ofNat 64 48)]),
                   .load .one (.op .add [.var .local (ofString "nc"), .const (BitVec.ofNat 64 56)])])))
        have hck_eq_cat : evaluateHOLFiniteState s_ck ck_body = evaluateHOLFiniteState s_ck dc_cat := by
          dsimp only [ck_body]
          rw [evaluateHOLFiniteState_seq_line780, hite_ck3_skip]
          dsimp only
          rw [evaluateHOLFiniteState_seq_line780, hite_ck0_skip]
        rw [hck_eq_cat] at hsck_res
        -- Step 5: `decCall cat := nibbles_concat(seg, sl, nc+32, nc+40)`
        set wnc32 : BitVec 64 := BitVec.ofNat 64 (memW s (wnc.toNat + 32))
        set wnc40 : BitVec 64 := BitVec.ofNat 64 (memW s (wnc.toNat + 40))
        have hwnc32_nat : wnc32.toNat = memW s (wnc.toNat + 32) := by
          dsimp [wnc32]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold memW; rcases s.memory _ with ⟨w⟩; exact w.isLt)]
        have hwnc40_nat : wnc40.toNat = memW s (wnc.toNat + 40) := by
          dsimp [wnc40]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold memW; rcases s.memory _ with ⟨w⟩; exact w.isLt)]
        have hkey_nc : KeyIn s Nd wnc32.toNat wnc40.toNat := by
          rw [hwnc32_nat, hwnc40_nat]
          exact hp_nc.2.2.2.2.2.2.1 hwck_12
        have hcat_args_ev : evalListHOLFinite s_ck (h := fun a => Classical.propDecidable (s_ck.memaddrs a))
            [.var .local (ofString "seg"), .var .local (ofString "sl"),
             .load .one (.op .add [.var .local (ofString "nc"), .const (BitVec.ofNat 64 32)]),
             .load .one (.op .add [.var .local (ofString "nc"), .const (BitVec.ofNat 64 40)])] =
            some [.val (.word wseg), .val (.word wsl), .val (.word wnc32), .val (.word wnc40)] := by
          rw [evalListHOLFinite_eq_toExact]
          have h32 := hload_nc_off s_ck 32 (fun _ _ => rfl) rfl hsck_nc (by omega) (by decide)
          have h40 := hload_nc_off s_ck 40 (fun _ _ => rfl) rfl hsck_nc (by omega) (by decide)
          have h1 : @evalHOLExact 64 F _ s_ck.toExact (fun a => Classical.propDecidable (s_ck.memaddrs a))
              (.var .local (ofString "seg")) = some (.val (.word wseg)) := hsck_seg
          have h2 : @evalHOLExact 64 F _ s_ck.toExact (fun a => Classical.propDecidable (s_ck.memaddrs a))
              (.var .local (ofString "sl")) = some (.val (.word wsl)) := hsck_sl
          dsimp only [evalListHOLExact]
          rw [h1, h2, h32, h40]
        obtain ⟨cvals, cbody, ccallee, cret, _, hcargs, hcl, hcexn | ⟨crv, cpost, hcrun, _, hccont_res, hcr_eq, hcp_eq⟩⟩ :=
          decCall_resumes_inv hsck_res
        · obtain ⟨eid, ev, hc_exn, hne_tr, _⟩ := hcexn
          have hsame := lookupCodeHOLFinite_installed_body s_ck.code.lookup (ofString "nibbles_concat")
            _ _ _ _ _ cvals ccallee (by change s.code.lookup _ = _; rw [hcode]; exact lookup_nibbles_concat) hcl
          subst hsame
          exact absurd (congrArg Prod.fst hc_exn)
            (nibbles_concat_no_nonTrap_exn (callEntryStateHOLFinite s_ck ccallee) hcode eid ev hne_tr)
        · have hcvals : cvals = [.val (.word wseg), .val (.word wsl), .val (.word wnc32), .val (.word wnc40)] :=
            Option.some.inj (hcargs.symm.trans hcat_args_ev)
          subst hcvals
          have hcl_ex := pan_four_word_lookup s_ck.code.lookup (ofString "nibbles_concat")
            (ofString "a") (ofString "al") (ofString "b") (ofString "bl")
            (sourceFnBody Guest.Software.guestFn_nibbles_concat) wseg wsl wnc32 wnc40
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by change s.code.lookup _ = _; rw [hcode]; exact lookup_nibbles_concat)
          rw [hcl_ex] at hcl
          obtain ⟨rfl, hrest_c⟩ := Prod.mk.inj (Option.some.inj hcl.symm)
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrest_c
          let centry := callEntryStateHOLFinite s_ck
            ((((HolFiniteMapExact.empty.update (ofString "a", .val (.word wseg))).update
              (ofString "al", .val (.word wsl))).update (ofString "b", .val (.word wnc32))).update
              (ofString "bl", .val (.word wnc40)))
          have hc_spec := nibbles_concat_body_spec centry Nd wseg wsl wnc32 wnc40
            hcode (localsFree_arenaReady s _ _ hAR) hNd hkey_seg hkey_nc
            (by simp [centry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                  show ofString "bl" ≠ ofString "a" by decide,
                  show ofString "b" ≠ ofString "a" by decide,
                  show ofString "al" ≠ ofString "a" by decide])
            (by simp [centry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                  show ofString "bl" ≠ ofString "al" by decide,
                  show ofString "b" ≠ ofString "al" by decide])
            (by simp [centry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                  show ofString "bl" ≠ ofString "b" by decide])
            (by simp [centry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
            crv (by rw [hcrun])
          rw [hcrun] at hc_spec
          obtain ⟨wcat, rfl, hcl_sum, hstep_cat_ent, hKey_cat, hmem_lt_cpost⟩ := hc_spec
          dsimp only at hstep_cat_ent hKey_cat hmem_lt_cpost
          have hstep_cat : NodeStep s cpost Nd Nd := NodeStep.from_locals_clock hstep_cat_ent
          set s_cat := setVarHOLFinite (ofString "cat") (.val (.word wcat)) { cpost with locals := s_ck.locals }
          have hscat_code : s_cat.code = originalRuntimeCode := hstep_cat.arena.1.code
          have hscat_ma : s_cat.memaddrs = s.memaddrs :=
            hstep_cat.arena.1.memaddrs.trans hAR.1.memaddrs.symm
          have hscat_cat : s_cat.locals.lookup (ofString "cat") = some (.val (.word wcat)) := by
            simp [s_cat, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          have hscat_ck : s_cat.locals.lookup (ofString "ck") = some (.val (.word wck)) := by
            simp [s_cat, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsck_ck,
              show ofString "cat" ≠ ofString "ck" by decide]
          have hscat_sl : s_cat.locals.lookup (ofString "sl") = some (.val (.word wsl)) := by
            simp [s_cat, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsck_sl,
              show ofString "cat" ≠ ofString "sl" by decide]
          have hscat_nc : s_cat.locals.lookup (ofString "nc") = some (.val (.word wnc)) := by
            simp [s_cat, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsck_nc,
              show ofString "cat" ≠ ofString "nc" by decide]
          -- Step 6: `dec cl := sl + load(nc + 40)` on `s_cat`
          set wcl : BitVec 64 := wsl + wnc40
          have hev_cl : @evalHOLExact 64 F _ s_cat.toExact (fun a => Classical.propDecidable (s_cat.memaddrs a))
              (.op .add [.var .local (ofString "sl"),
                .load .one (.op .add [.var .local (ofString "nc"), .const (BitVec.ofNat 64 40)])]) =
              some (.val (.word wcl)) := by
            have h40 := hload_nc_off s_cat 40 hmem_lt_cpost hscat_ma hscat_nc (by omega) (by decide)
            have hsl_ev : @evalHOLExact 64 F _ s_cat.toExact (fun a => Classical.propDecidable (s_cat.memaddrs a))
                (.var .local (ofString "sl")) = some (.val (.word wsl)) := hscat_sl
            have hlst : @evalListHOLExact 64 F _ s_cat.toExact (fun a => Classical.propDecidable (s_cat.memaddrs a))
                [.var .local (ofString "sl"),
                 .load .one (.op .add [.var .local (ofString "nc"), .const (BitVec.ofNat 64 40)])] =
                some [.val (.word wsl), .val (.word wnc40)] := by
              dsimp only [evalListHOLExact]; rw [hsl_ev, h40]
            conv_lhs => unfold evalHOLExact
            rw [hlst]
            simp [wcl, valueIsWord, valueWord, wordOpHOL, wordOp]
          set s_cl := setVarHOLFinite (ofString "cl") (.val (.word wcl)) s_cat
          set cl_body : ProgHOL 64 :=
            .seq
              (.ite (.cmp .equal (.var .local (ofString "ck")) (.const (BitVec.ofNat 64 2)))
                (.call none (ofString "node_new_ext")
                  [.var .local (ofString "cat"), .var .local (ofString "cl"),
                   .load .one (.op .add [.var .local (ofString "nc"), .const (BitVec.ofNat 64 48)])])
                .skip)
              (.call none (ofString "node_new_leaf")
                [.var .local (ofString "cat"), .var .local (ofString "cl"),
                 .load .one (.op .add [.var .local (ofString "nc"), .const (BitVec.ofNat 64 48)]),
                 .load .one (.op .add [.var .local (ofString "nc"), .const (BitVec.ofNat 64 56)])])
          have hcat_cl : (evaluateHOLFiniteState s_cat (.dec (ofString "cl") .one
                (.op .add [.var .local (ofString "sl"),
                  .load .one (.op .add [.var .local (ofString "nc"), .const (BitVec.ofNat 64 40)])])
                cl_body)).1 = (evaluateHOLFiniteState s_cl cl_body).1 ∧
              (evaluateHOLFiniteState s_cat (.dec (ofString "cl") .one
                (.op .add [.var .local (ofString "sl"),
                  .load .one (.op .add [.var .local (ofString "nc"), .const (BitVec.ofNat 64 40)])])
                cl_body)).2 =
              { (evaluateHOLFiniteState s_cl cl_body).2 with
                locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState s_cl cl_body).2.locals
                  (ofString "cl", s_cat.locals.lookup (ofString "cl")) } := by
            rw [evaluateHOLFiniteState_dec_total]
            dsimp only
            rw [hev_cl]
            simp [shapeEqHOL, shapeOfHOLExact, s_cl]
          have hscl_res : Resumes (evaluateHOLFiniteState s_cl cl_body).1 := by
            rwa [← hcat_cl.1]
          have hscl_code : s_cl.code = originalRuntimeCode := hscat_code
          have hscl_ma : s_cl.memaddrs = s.memaddrs := hscat_ma
          have hscl_AR : ArenaReady s_cl := localsFree_arenaReady cpost _ _ hstep_cat.arena
          have hscl_cat : s_cl.locals.lookup (ofString "cat") = some (.val (.word wcat)) := by
            simp [s_cl, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hscat_cat,
              show ofString "cl" ≠ ofString "cat" by decide]
          have hscl_cl : s_cl.locals.lookup (ofString "cl") = some (.val (.word wcl)) := by
            simp [s_cl, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          have hscl_ck : s_cl.locals.lookup (ofString "ck") = some (.val (.word wck)) := by
            simp [s_cl, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hscat_ck,
              show ofString "cl" ≠ ofString "ck" by decide]
          have hscl_nc : s_cl.locals.lookup (ofString "nc") = some (.val (.word wnc)) := by
            simp [s_cl, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hscat_nc,
              show ofString "cl" ≠ ofString "nc" by decide]
          have hKey_cat_cl : KeyIn s_cl Nd wcat.toNat wcl.toNat := by
            dsimp only [wcl]; rw [hcl_sum]; exact hKey_cat
          -- Step 7: branch on `ck == 2` vs `ck == 1`!
          have hc_ck2 : @evalHOLExact 64 F _ s_cl.toExact (fun a => Classical.propDecidable (s_cl.memaddrs a))
              (.cmp .equal (.var .local (ofString "ck")) (.const (BitVec.ofNat 64 2))) =
              some (.val (.word (if wck = 2 then 1 else 0))) := by
            simp [evalHOLExact, hscl_ck, Compiler.Encoders.Asm.wordCmpHOL]
          by_cases hck2 : wck = 2
          · -- Branch 4: `ck == 2` -> tail call `node_new_ext(cat, cl, load(nc + 48))`!
            have hnc_k2 : memW s wnc.toNat = 2 := by
              have := congrArg BitVec.toNat hck2; rw [hwck_nat] at this; simpa using this
            have hite_ck2 : evaluateHOLFiniteState s_cl
                (.ite (.cmp .equal (.var .local (ofString "ck")) (.const (BitVec.ofNat 64 2)))
                  (.call none (ofString "node_new_ext")
                    [.var .local (ofString "cat"), .var .local (ofString "cl"),
                     .load .one (.op .add [.var .local (ofString "nc"), .const (BitVec.ofNat 64 48)])])
                  .skip) =
                evaluateHOLFiniteState s_cl
                  (.call none (ofString "node_new_ext")
                    [.var .local (ofString "cat"), .var .local (ofString "cl"),
                     .load .one (.op .add [.var .local (ofString "nc"), .const (BitVec.ofNat 64 48)])]) := by
              rw [evaluateHOLFiniteState_ite, hc_ck2, if_pos hck2]; simp
            set ext_call : ProgHOL 64 :=
              .call none (ofString "node_new_ext")
                [.var .local (ofString "cat"), .var .local (ofString "cl"),
                 .load .one (.op .add [.var .local (ofString "nc"), .const (BitVec.ofNat 64 48)])]
            have hnn_ext := call_none_ne_none s_cl (ofString "node_new_ext")
              [.var .local (ofString "cat"), .var .local (ofString "cl"),
               .load .one (.op .add [.var .local (ofString "nc"), .const (BitVec.ofNat 64 48)])]
            have hcl_eq_ext : evaluateHOLFiniteState s_cl cl_body = evaluateHOLFiniteState s_cl ext_call := by
              dsimp only [cl_body]
              rw [evaluateHOLFiniteState_seq_line780, hite_ck2]
              rcases h_ec : evaluateHOLFiniteState s_cl ext_call with ⟨er, ep⟩
              cases er with
              | none => exact absurd (congrArg Prod.fst h_ec) hnn_ext
              | some _ => rfl
            rw [hcl_eq_ext] at hscl_res
            set wnc48 : BitVec 64 := BitVec.ofNat 64 (memW s (wnc.toNat + 48))
            have hwnc48_root : RootIn Nd wnc48.toNat := by
              dsimp [wnc48]
              rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold memW; rcases s.memory _ with ⟨w⟩; exact w.isLt)]
              exact hp_nc.2.2.2.2.1 hnc_k2
            have hext_args : evalListHOLFinite s_cl (h := fun a => Classical.propDecidable (s_cl.memaddrs a))
                [.var .local (ofString "cat"), .var .local (ofString "cl"),
                 .load .one (.op .add [.var .local (ofString "nc"), .const (BitVec.ofNat 64 48)])] =
                some [.val (.word wcat), .val (.word wcl), .val (.word wnc48)] := by
              rw [evalListHOLFinite_eq_toExact]
              have h48 := hload_nc_off s_cl 48 hmem_lt_cpost hscl_ma hscl_nc (by omega) (by decide)
              have h1 : @evalHOLExact 64 F _ s_cl.toExact (fun a => Classical.propDecidable (s_cl.memaddrs a))
                  (.var .local (ofString "cat")) = some (.val (.word wcat)) := hscl_cat
              have h2 : @evalHOLExact 64 F _ s_cl.toExact (fun a => Classical.propDecidable (s_cl.memaddrs a))
                  (.var .local (ofString "cl")) = some (.val (.word wcl)) := hscl_cl
              dsimp only [evalListHOLExact]
              rw [h1, h2, h48]
            obtain ⟨Nd_ext, hstep_ext, hret_ext⟩ := tail_call_node_new_ext s_cl Nd
              _ _ _ wcat wcl wnc48 hscl_code hscl_AR hstep_cat.heap hext_args hKey_cat_cl hwnc48_root hscl_res
            refine ⟨Nd_ext, ?_, ?_⟩
            · change NodeStep s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn__delete_ext_finish)).2 Nd Nd_ext
              rw [hbody_ck.2, hck_eq_cat, hcp_eq, hcat_cl.2, hcl_eq_ext]
              exact (((NodeStep.trans hAR hstep_cat (NodeStep.from_locals_clock (NodeStep.from_locals_clock hstep_ext))).with_locals_clock _ _).with_locals_clock _ _).with_locals_clock _ _
            · intro v hv
              change (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn__delete_ext_finish)).1 = _ at hv
              rw [hbody_ck.1, hck_eq_cat, hcr_eq, hcat_cl.1, hcl_eq_ext] at hv
              exact hret_ext v hv
          · -- Branch 5: `ck != 2`, hence `ck == 1` -> tail call `node_new_leaf(cat, cl, nc+48, nc+56)`!
            have hnc_k1 : memW s wnc.toNat = 1 := by
              rcases hwck_12 with hk1 | hk2
              · exact hk1
              · exfalso; apply hck2; apply BitVec.eq_of_toNat_eq; rw [hwck_nat]; simpa using hk2
            have hsz_nc64 : nodeSize (memW s wnc.toNat) = 64 := by simp [nodeSize, hnc_k1]
            have hite_ck2_skip : evaluateHOLFiniteState s_cl
                (.ite (.cmp .equal (.var .local (ofString "ck")) (.const (BitVec.ofNat 64 2)))
                  (.call none (ofString "node_new_ext")
                    [.var .local (ofString "cat"), .var .local (ofString "cl"),
                     .load .one (.op .add [.var .local (ofString "nc"), .const (BitVec.ofNat 64 48)])])
                  .skip) = (none, s_cl) := by
              rw [evaluateHOLFiniteState_ite, hc_ck2, if_neg hck2]; simp [evaluateHOLFiniteState_skip]
            set lf_call : ProgHOL 64 :=
              .call none (ofString "node_new_leaf")
                [.var .local (ofString "cat"), .var .local (ofString "cl"),
                 .load .one (.op .add [.var .local (ofString "nc"), .const (BitVec.ofNat 64 48)]),
                 .load .one (.op .add [.var .local (ofString "nc"), .const (BitVec.ofNat 64 56)])]
            have hcl_eq_lf : evaluateHOLFiniteState s_cl cl_body = evaluateHOLFiniteState s_cl lf_call := by
              dsimp only [cl_body]
              rw [evaluateHOLFiniteState_seq_line780, hite_ck2_skip]
            rw [hcl_eq_lf] at hscl_res
            set wnc48 : BitVec 64 := BitVec.ofNat 64 (memW s (wnc.toNat + 48))
            set wnc56 : BitVec 64 := BitVec.ofNat 64 (memW s (wnc.toNat + 56))
            have hwnc56_lt : wnc56.toNat < 2 ^ 40 := by
              have h56 := hp_nc.2.2.2.2.2.2.2.2.1 hnc_k1
              have hlt64 : memW s (wnc.toNat + 56) < 2 ^ 64 := lt_trans h56 (by decide)
              dsimp [wnc56]; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64]; exact h56
            have hlf_args : evalListHOLFinite s_cl (h := fun a => Classical.propDecidable (s_cl.memaddrs a))
                [.var .local (ofString "cat"), .var .local (ofString "cl"),
                 .load .one (.op .add [.var .local (ofString "nc"), .const (BitVec.ofNat 64 48)]),
                 .load .one (.op .add [.var .local (ofString "nc"), .const (BitVec.ofNat 64 56)])] =
                some [.val (.word wcat), .val (.word wcl), .val (.word wnc48), .val (.word wnc56)] := by
              rw [evalListHOLFinite_eq_toExact]
              have h48 := hload_nc_off s_cl 48 hmem_lt_cpost hscl_ma hscl_nc (by omega) (by decide)
              have h56 := hload_nc_off s_cl 56 hmem_lt_cpost hscl_ma hscl_nc (by omega) (by decide)
              have h1 : @evalHOLExact 64 F _ s_cl.toExact (fun a => Classical.propDecidable (s_cl.memaddrs a))
                  (.var .local (ofString "cat")) = some (.val (.word wcat)) := hscl_cat
              have h2 : @evalHOLExact 64 F _ s_cl.toExact (fun a => Classical.propDecidable (s_cl.memaddrs a))
                  (.var .local (ofString "cl")) = some (.val (.word wcl)) := hscl_cl
              dsimp only [evalListHOLExact]
              rw [h1, h2, h48, h56]
            obtain ⟨Nd_lf, hstep_lf, hret_lf⟩ := tail_call_node_new_leaf s_cl Nd
              _ _ _ _ wcat wcl wnc48 wnc56 hscl_code hscl_AR hstep_cat.heap hlf_args hKey_cat_cl hwnc56_lt hscl_res
            refine ⟨Nd_lf, ?_, ?_⟩
            · change NodeStep s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn__delete_ext_finish)).2 Nd Nd_lf
              rw [hbody_ck.2, hck_eq_cat, hcp_eq, hcat_cl.2, hcl_eq_lf]
              exact (((NodeStep.trans hAR hstep_cat (NodeStep.from_locals_clock (NodeStep.from_locals_clock hstep_lf))).with_locals_clock _ _).with_locals_clock _ _).with_locals_clock _ _
            · intro v hv
              change (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn__delete_ext_finish)).1 = _ at hv
              rw [hbody_ck.1, hck_eq_cat, hcr_eq, hcat_cl.1, hcl_eq_lf] at hv
              exact hret_lf v hv

end InitECandidate.Solver.Wave8GuestInv.R16Shards
