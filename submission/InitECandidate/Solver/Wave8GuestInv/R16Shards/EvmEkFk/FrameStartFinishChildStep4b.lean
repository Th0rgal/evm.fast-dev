import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.FrameStartFinishChildStep4a

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8Contracts.M23 (EvmStep EvmKeeps EvmAvoids GlobalsKept)
open InitECandidate.Solver.Wave8GuestInv.R11Shards
open InitECandidate.Solver.Wave8M19 (evalAt)

def FcSetRetdataStepW_local : Prop :=
  ∀ {F : Type} {s0 st : PanSemStateFiniteExact 64 F} {S : List Nat},
    FcBranchState s0 st S →
    Inside (globN s0 "ev", 280) (globN st "scratch_ptr") scratchEnd →
    WordsOK st (globN s0 "ev", 280) →
    ∀ (pExp nExp : ExpHOL 64) (pw nw : BitVec 64),
    evalAt st pExp = some (.val (.word pw)) →
    evalAt st nExp = some (.val (.word nw)) →
    (evaluateHOLFiniteState st
      (.call (some (none, none)) (ofString "set_retdata") [pExp, nExp])).1 ≠ some .timeOut →
    let prog : ProgHOL 64 := .call (some (none, none)) (ofString "set_retdata") [pExp, nExp]
    (∀ u, (evaluateHOLFiniteState st prog).1 ≠ some (.returned u)) ∧
    ¬ OpDispatchSpec.IsEvmErr (evaluateHOLFiniteState st prog).1 ∧
    ((evaluateHOLFiniteState st prog).1 = none →
      let post := (evaluateHOLFiniteState st prog).2
      FcBranchState s0 post S ∧
      post.locals = st.locals ∧
      (∀ g : String, ofString g ≠ ofString "heap_ptr" → globN post g = globN st g) ∧
      evmChain post = evmChain st ∧
      OpDispatchSpec.evmR post ≤ OpDispatchSpec.evmR st ∧
      memW post (globN post "ev" + 16) = memW st (globN st "ev" + 16) ∧
      memW post (globN post "ev" + 40) = memW st (globN st "ev" + 40) ∧
      memW post (globN post "ev" + 232) = memW st (globN st "ev" + 232))

private theorem ev_head_facts_srd {F : Type} {s : PanSemStateFiniteExact 64 F} {S : List Nat}
    (hA : ArenaReady s) (hInv : InitECandidate.Solver.Wave8Contracts.M23.EvmInvAt s S) :
    globN s "ev" + 280 ≤ 2 ^ 64 ∧
    WordsOK s (globN s "ev", 280) ∧
    s.globals.lookup (ofString "ev") =
      some (.val (.word (BitVec.ofNat 64 (globN s "ev")))) ∧
    memW s (globN s "ev" + 16) ≤ memW s (globN s "ev" + 232) ∧
    OpDispatchSpec.evmR s =
      memW s (globN s "ev" + 64) + memW s (globN s "ev" + 192) +
        (((evmChain s).tail.map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)).sum) := by
  have hhead : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by
    rw [evmChain_cons]; exact List.mem_cons_self
  have hFW := hInv.2.2.2.2.1 _ hhead
  have hbnd := (InitECandidate.Solver.Wave8Contracts.M23.frameWF_bounds hA.2 hFW).1
  dsimp only at hbnd
  have hwok : WordsOK s (globN s "ev", 280) := (hFW.1 (globN s "ev", 280) (by simp)).2
  obtain ⟨evw, hevw⟩ := hA.2.2.2.2.2.2.2.2.2 "ev" (by decide)
  have hevw_eq : evw = BitVec.ofNat 64 (globN s "ev") := by
    apply BitVec.eq_of_toNat_eq
    unfold GlobalWord at hevw
    have hgn : globN s "ev" = evw.toNat := by simp [globN, hevw]
    rw [BitVec.toNat_ofNat, hgn, Nat.mod_eq_of_lt evw.isLt]
  subst hevw_eq
  unfold GlobalWord at hevw
  have hsp : memW s (globN s "ev" + 16) ≤ memW s (globN s "ev" + 232) := hFW.2.2.2.2.1
  have hR : OpDispatchSpec.evmR s =
      memW s (globN s "ev" + 64) + memW s (globN s "ev" + 192) +
        (((evmChain s).tail.map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)).sum) := by
    unfold OpDispatchSpec.evmR
    conv_lhs => rw [evmChain_cons]
    conv_rhs => rw [evmChain_cons]
    simp [Nat.add_assoc]
  exact ⟨hbnd, hwok, hevw, hsp, hR⟩

private abbrev R14W_srd := InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.updW

private theorem fc_updW3_memory_ne_srd (x a1 a2 a3 : BitVec 64)
    (m : BitVec 64 → HolWordLab 64) (w1 w2 w3 : BitVec 64)
    (h1 : x ≠ a1) (h2 : x ≠ a2) (h3 : x ≠ a3) :
    R14W_srd (R14W_srd (R14W_srd m a1 w1) a2 w2) a3 w3 x = m x := by
  simp [R14W_srd, R14Shards.OpHandlersA.updW, h1, h2, h3]

private theorem store_global_off_word_run_srd {F : Type} (t : PanSemStateFiniteExact 64 F)
    {gname : String} {gbase off : Nat} {gw w : BitVec 64} {valExp : ExpHOL 64}
    (hg_lk : t.globals.lookup (ofString gname) = some (.val (.word gw)))
    (hg_nat : gw.toNat = gbase)
    (hbnd : gbase + off < 2 ^ 64)
    (hdom : t.memaddrs (BitVec.ofNat 64 (gbase + off)))
    (hvalEval : @evalHOLExact 64 F _ t.toExact
        (fun a => Classical.propDecidable (t.memaddrs a)) valExp = some (.val (.word w))) :
    evaluateHOLFiniteState t
        (.store (.op .add [.var .global (ofString gname), .const (BitVec.ofNat 64 off)]) valExp) =
      (none, { t with memory := R14W_srd t.memory (BitVec.ofNat 64 (gbase + off)) w }) := by
  have hdst : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
      (.op .add [.var .global (ofString gname), .const (BitVec.ofNat 64 off)]) =
      some (.val (.word (BitVec.ofNat 64 (gbase + off)))) := by
    simp only [evalHOLExact, evalListHOLExact, hg_lk, wordOpHOL, wordOp, valueIsWord, valueWord,
      List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr]
    congr 3
    apply BitVec.eq_of_toNat_eq
    have hz0 : (0 : BitVec 64).toNat = 0 := rfl
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hg_nat, hz0, Nat.add_zero,
      Nat.mod_eq_of_lt (show off < 2 ^ 64 by omega), Nat.mod_eq_of_lt hbnd]
  rw [evaluateHOLFiniteState_store, hdst, hvalEval]
  dsimp only
  have hmem : @panMemStoresHOL 64 _ (BitVec.ofNat 64 (gbase + off)) (flattenHOL (.val (.word w)))
      t.memaddrs (fun a => Classical.propDecidable (t.memaddrs a)) t.memory
      = some (R14W_srd t.memory (BitVec.ofNat 64 (gbase + off)) w) := by
    simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL, hdom, ↓reduceIte]
    rfl
  rw [hmem]

private theorem call_assign_local_ne_returned_srd {F : Type}
    (s : PanSemStateFiniteExact 64 F) (x : MlS) (fn : MlS) (args : List (ExpHOL 64))
    (u : ValueHOL 64) :
    (evaluateHOLFiniteState s (.call (some (some (.local, x), none)) fn args)).1 ≠
      some (.returned u) := by
  rw [evaluateHOLFiniteState_call]
  cases evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with
  | none => simp
  | some vs =>
    dsimp only
    cases lookupCodeHOLFinite s.code.lookup fn vs with
    | none => simp
    | some found =>
      rcases found with ⟨body, callee, rsh⟩
      dsimp only
      by_cases hc : s.clock = 0
      · rw [if_pos hc]; simp
      · rw [if_neg hc]
        rcases evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨r, post⟩
        cases r with
        | none => simp
        | some r' =>
          cases r' with
          | timeOut | «break» | «continue» | error | finalFfi _ | exception _ _ =>
            simp [emptyLocalsHOLFinite]
          | returned v =>
            dsimp only
            by_cases hs : shapeEqHOL (shapeOfHOLExact v) rsh = true
            · rw [if_pos hs]
              split <;> simp [setVarHOLFinite]
            · rw [if_neg hs]; simp [emptyLocalsHOLFinite]

theorem fcSetRetdataStepW : FcSetRetdataStepW_local := by
  intro F s0 st S hBS _ _ pExp nExp pv nw hp hn hnt
  dsimp only
  have hcode : st.code = originalRuntimeCode := hBS.arena.1.code
  refine ⟨fun u => call0_ne_returned_fc st (ofString "set_retdata") [pExp, nExp] u, ?_, ?_⟩
  · rintro ⟨errCode, herr⟩
    have hncr := StateRestoreEpilogue.evaluate_noCatchableRaise srdSetCallees_fc srdSetCallees_fc_good
      (.call (some (none, none)) (ofString "set_retdata") [pExp, nExp])
      (by simp [StateRestoreEpilogue.noCatchableRaise, srdSetCallees_fc])
      st hcode (ofString "EvmErr") errCode (by decide)
    exact hncr herr
  · intro hnone
    by_cases hnw0 : nw = 0#64
    · subst hnw0
      obtain ⟨hbnd, hwok, hlk, hsp, hRdec⟩ := ev_head_facts_srd hBS.arena hBS.inv
      obtain ⟨evw, hev_empty⟩ := hBS.arena.2.2.2.2.2.2.2.2.2 "evm_empty" (by decide)
      set e : BitVec 64 := BitVec.ofNat 64 (globN st "ev") with he_def
      have he_nat : e.toNat = globN st "ev" := by
        rw [he_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have he_lk : st.globals.lookup (ofString "ev") = some (.val (.word e)) := by
        rw [he_def]; exact hlk
      have hclk : st.clock ≠ 0 := by
        intro h0; apply hnt
        rw [evaluateHOLFiniteState_call]
        have hargs : evalListHOLFinite st (h := fun a => Classical.propDecidable (st.memaddrs a))
            [pExp, nExp] = some [.val (.word pv), .val (.word 0#64)] := by
          rw [evalListHOLFinite_eq_toExact]
          simp [evalListHOLExact, hp, hn]
        rw [hargs]; dsimp only
        have hl := pan_two_word_lookup st.code.lookup (ofString "set_retdata") (ofString "p")
          (ofString "n") (sourceFnBody Guest.Software.guestFn_set_retdata) pv 0#64
          (by decide) (by rw [hcode]; exact lookup_set_retdata_fc)
        rw [hl]; dsimp only; simp [h0]
      have hbnd232 : e.toNat + 232 < 2 ^ 64 := by rw [he_nat]; omega
      have hdom144 : st.memaddrs (e + 144#64) := by
        obtain ⟨_, hdom, _⟩ := hwok.2.2 18 (by omega)
        have heq : e + 144#64 = BitVec.ofNat 64 (globN st "ev" + 8 * 18) := by
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_add, he_nat, show (144#64 : BitVec 64).toNat = 144 from rfl, BitVec.toNat_ofNat]
        rw [heq]; exact hdom
      have hdom152 : st.memaddrs (e + 152#64) := by
        obtain ⟨_, hdom, _⟩ := hwok.2.2 19 (by omega)
        have heq : e + 152#64 = BitVec.ofNat 64 (globN st "ev" + 8 * 19) := by
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_add, he_nat, show (152#64 : BitVec 64).toNat = 152 from rfl, BitVec.toNat_ofNat]
        rw [heq]; exact hdom
      have hdom216 : st.memaddrs (e + 216#64) := by
        obtain ⟨_, hdom, _⟩ := hwok.2.2 27 (by omega)
        have heq : e + 216#64 = BitVec.ofNat 64 (globN st "ev" + 8 * 27) := by
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_add, he_nat, show (216#64 : BitVec 64).toNat = 216 from rfl, BitVec.toNat_ofNat]
        rw [heq]; exact hdom
      have hrun := set_retdata_zero_call_run st pExp nExp pv e evw hcode hp hn hclk
        he_lk hev_empty hbnd232 hdom144 hdom152 hdom216
      rw [hrun]; dsimp only
      have hA1 : BitVec.ofNat 64 (e.toNat + 144) = BitVec.ofNat 64 (globN st "ev" + 144) := by
        apply congrArg (BitVec.ofNat 64); rw [he_nat]
      have hA2 : BitVec.ofNat 64 (e.toNat + 152) = BitVec.ofNat 64 (globN st "ev" + 152) := by
        apply congrArg (BitVec.ofNat 64); rw [he_nat]
      have hA3 : BitVec.ofNat 64 (e.toNat + 216) = BitVec.ofNat 64 (globN st "ev" + 216) := by
        apply congrArg (BitVec.ofNat 64); rw [he_nat]
      have hne12 : BitVec.ofNat 64 (globN st "ev" + 144) ≠ BitVec.ofNat 64 (globN st "ev" + 152) := by
        intro heq; have h := congrArg BitVec.toNat heq; simp only [BitVec.toNat_ofNat] at h; omega
      have hne13 : BitVec.ofNat 64 (globN st "ev" + 144) ≠ BitVec.ofNat 64 (globN st "ev" + 216) := by
        intro heq; have h := congrArg BitVec.toNat heq; simp only [BitVec.toNat_ofNat] at h; omega
      have hne23 : BitVec.ofNat 64 (globN st "ev" + 152) ≠ BitVec.ofNat 64 (globN st "ev" + 216) := by
        intro heq; have h := congrArg BitVec.toNat heq; simp only [BitVec.toNat_ofNat] at h; omega
      set post0 : PanSemStateFiniteExact 64 F := { st with clock := st.clock - 1, memory :=
        (R14W_srd (R14W_srd (R14W_srd st.memory (BitVec.ofNat 64 (e.toNat + 144)) evw)
          (BitVec.ofNat 64 (e.toNat + 152)) 0#64)
          (BitVec.ofNat 64 (e.toNat + 216)) 0#64) }
      have hmem_out : ∀ x : BitVec 64,
          (∀ off ∈ headRetZeroOffs, x ≠ BitVec.ofNat 64 (globN st "ev" + off)) →
          post0.memory x = st.memory x := by
        intro x hx
        have hx1 : x ≠ BitVec.ofNat 64 (e.toNat + 144) := by rw [hA1]; exact hx 144 (by decide)
        have hx2 : x ≠ BitVec.ofNat 64 (e.toNat + 152) := by rw [hA2]; exact hx 152 (by decide)
        have hx3 : x ≠ BitVec.ofNat 64 (e.toNat + 216) := by rw [hA3]; exact hx 216 (by decide)
        show R14W_srd (R14W_srd (R14W_srd st.memory (BitVec.ofNat 64 (e.toNat + 144)) evw)
            (BitVec.ofNat 64 (e.toNat + 152)) 0#64)
          (BitVec.ofNat 64 (e.toNat + 216)) 0#64 x = st.memory x
        exact fc_updW3_memory_ne_srd x _ _ _ _ _ _ _ hx1 hx2 hx3
      have hmem144 : post0.memory (BitVec.ofNat 64 (globN st "ev" + 144)) = .word evw := by
        show R14W_srd (R14W_srd (R14W_srd st.memory (BitVec.ofNat 64 (e.toNat + 144)) evw)
          (BitVec.ofNat 64 (e.toNat + 152)) 0#64)
          (BitVec.ofNat 64 (e.toNat + 216)) 0#64 (BitVec.ofNat 64 (globN st "ev" + 144)) = .word evw
        rw [hA1, hA2, hA3]; simp [R14W_srd, R14Shards.OpHandlersA.updW, hne12, hne13]
      have hmem216 : post0.memory (BitVec.ofNat 64 (globN st "ev" + 216)) = .word 0#64 := by
        show R14W_srd (R14W_srd (R14W_srd st.memory (BitVec.ofNat 64 (e.toNat + 144)) evw)
          (BitVec.ofNat 64 (e.toNat + 152)) 0#64)
          (BitVec.ofNat 64 (e.toNat + 216)) 0#64 (BitVec.ofNat 64 (globN st "ev" + 216)) = .word 0#64
        rw [hA1, hA2, hA3]; simp [R14W_srd, R14Shards.OpHandlersA.updW]
      have h144 : memW post0 (globN st "ev" + 144) = globN st "evm_empty" := by
        unfold memW; rw [hmem144]
        unfold globN; rw [show st.globals.lookup (ofString "evm_empty") = some (.val (.word evw)) from hev_empty]
      have h216 : memW post0 (globN st "ev" + 216) = 0 := by
        unfold memW; rw [hmem216]; simp
      have hcell : ∀ off : Nat, off + 8 ≤ 280 → off % 8 = 0 → off ≠ 144 → off ≠ 152 → off ≠ 216 →
          memW post0 (globN st "ev" + off) = memW st (globN st "ev" + off) := by
        intro off hoff _ hn144 hn152 hn216
        have hnot : ∀ hoff' ∈ headRetZeroOffs,
            BitVec.ofNat 64 (globN st "ev" + off) ≠ BitVec.ofNat 64 (globN st "ev" + hoff') := by
          intro hoff' hm heq
          have hm' : hoff' = 144 ∨ hoff' = 152 ∨ hoff' = 216 := by simpa [headRetZeroOffs] using hm
          have h := congrArg BitVec.toNat heq
          rcases hm' with rfl | rfl | rfl
          · rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h
            omega
          · rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h
            omega
          · rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h
            omega
        unfold memW
        rw [hmem_out _ hnot]
      have hGp : GuestInv post0 := ⟨hcode, hBS.arena.1.memaddrs, hBS.arena.1.shMemaddrs, hBS.arena.1.baseAddr⟩
      have hsp_le : memW post0 (globN st "ev" + 16) ≤ memW st (globN st "ev" + 232) := by
        rw [hcell 16 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hsp
      have hgas_sum : OpDispatchSpec.evmR st + 1 < 2 ^ 64 := by
        unfold OpDispatchSpec.evmR; exact hBS.inv.2.2.2.2.2.2.2.2.2.2.2.2
      have hgas_le : memW post0 (globN st "ev" + 64) + memW post0 (globN st "ev" + 192) +
          (((evmChain st).tail.map fun ec => memW st (ec.1 + 64) + memW st (ec.1 + 192)).sum) + 1 < 2 ^ 64 := by
        rw [hcell 64 (by omega) (by omega) (by omega) (by omega) (by omega),
            hcell 192 (by omega) (by omega) (by omega) (by omega) (by omega), ← hRdec]
        exact hgas_sum
      obtain ⟨hAp', hIp', hch, hfix, htab, hframes, _, _, _, hRp'⟩ :=
        evmInvAt_of_head_ret_zero hBS.arena hBS.inv hGp rfl rfl hmem_out h216 h144 hsp_le hgas_le
      have hhp : globN st "heap_ptr" ≤ globN post0 "heap_ptr" := le_refl _
      have hRel := releaseReadyAt_transport hBS.release hhp hch
        (fun ec hec => (hframes ec hec).1)
        (fun ec hec => ⟨(hframes ec hec).2.2.1, (hframes ec hec).2.2.2.2.1⟩)
        (fun ec hec => Or.inl (hframes ec hec).2.1)
        (fun ec hec => (hframes ec hec).2.2.2.2.2.1)
        (fun t ht => Or.inl (htab t ht)) hfix
      have hcells : ∀ ec ∈ evmChain post0,
          memW post0 (ec.1 + 24) = memW s0 (ec.1 + 24) ∧
          memW post0 (ec.1 + 32) = memW s0 (ec.1 + 32) ∧
          memW post0 (ec.1 + 40) = memW s0 (ec.1 + 40) ∧
          memW post0 (ec.2 + 56) = memW s0 (ec.2 + 56) := by
        intro ec hec; rw [hch] at hec
        obtain ⟨a, b, c, d⟩ := hBS.cells ec hec
        have hf := (hframes ec hec).2.2
        exact ⟨hf.1.trans a, hf.2.1.trans b, hf.2.2.1.trans c, hf.2.2.2.2.trans d⟩
      have hRp_eq : OpDispatchSpec.evmR post0 = OpDispatchSpec.evmR st := by
        rw [hRp', hcell 64 (by omega) (by omega) (by omega) (by omega) (by omega),
            hcell 192 (by omega) (by omega) (by omega) (by omega) (by omega), ← hRdec]
      refine ⟨?_, rfl, fun _ _ => rfl, hch, le_of_eq hRp_eq,
        hcell 16 (by omega) (by omega) (by omega) (by omega) (by omega),
        hcell 40 (by omega) (by omega) (by omega) (by omega) (by omega),
        hcell 232 (by omega) (by omega) (by omega) (by omega) (by omega)⟩
      refine ⟨hAp', hIp', hRel, fcEntryLocals_congr_locals (s1 := st) (s2 := post0) rfl hBS.locals_ok, hch.trans hBS.chain_eq, ?_, ?_, hcells, hBS.ev_eq⟩
      · rw [hch]; exact hBS.length_eq
      · rw [hRp_eq]; exact hBS.r_le
    · -- `nw ≠ 0`
      have hnw_pos : 0 < nw.toNat := by
        by_contra hz; apply hnw0; apply BitVec.eq_of_toNat_eq; simp; omega
      obtain ⟨hbnd, hwok, hlk, hsp, hRdec⟩ := ev_head_facts_srd hBS.arena hBS.inv
      set e : BitVec 64 := BitVec.ofNat 64 (globN st "ev") with he_def
      have he_nat : e.toNat = globN st "ev" := by
        rw [he_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have he_lk : st.globals.lookup (ofString "ev") = some (.val (.word e)) := by
        rw [he_def]; exact hlk
      have hhead_mem : (globN st "ev", globN st "cur_cont") ∈ evmChain st := by
        simp [evmChain, evmChainFrom]
      have hhead_FW := hBS.inv.2.2.2.2.1 _ hhead_mem
      have hdom144 : st.memaddrs (e + 144#64) := by
        obtain ⟨_, hdom, _⟩ := hwok.2.2 18 (by omega)
        have heq : e + 144#64 = BitVec.ofNat 64 (globN st "ev" + 8 * 18) := by
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_add, he_nat, show (144#64 : BitVec 64).toNat = 144 from rfl, BitVec.toNat_ofNat]
        rw [heq]; exact hdom
      have hdom152 : st.memaddrs (e + 152#64) := by
        obtain ⟨_, hdom, _⟩ := hwok.2.2 19 (by omega)
        have heq : e + 152#64 = BitVec.ofNat 64 (globN st "ev" + 8 * 19) := by
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_add, he_nat, show (152#64 : BitVec 64).toNat = 152 from rfl, BitVec.toNat_ofNat]
        rw [heq]; exact hdom
      have hdom216 : st.memaddrs (e + 216#64) := by
        obtain ⟨_, hdom, _⟩ := hwok.2.2 27 (by omega)
        have heq : e + 216#64 = BitVec.ofNat 64 (globN st "ev" + 8 * 27) := by
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_add, he_nat, show (216#64 : BitVec 64).toNat = 216 from rfl, BitVec.toNat_ofNat]
        rw [heq]; exact hdom
      have h144_bv : e + 144#64 = BitVec.ofNat 64 (globN st "ev" + 144) := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_add, he_nat, show (144#64 : BitVec 64).toNat = 144 from rfl,
            BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have h152_bv : e + 152#64 = BitVec.ofNat 64 (globN st "ev" + 152) := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_add, he_nat, show (152#64 : BitVec 64).toNat = 152 from rfl,
            BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have h216_bv : e + 216#64 = BitVec.ofNat 64 (globN st "ev" + 216) := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_add, he_nat, show (216#64 : BitVec 64).toNat = 216 from rfl,
            BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      obtain ⟨d0w, _, hm144_bv⟩ := hwok.2.2 18 (by omega)
      have hm144 : st.memory (e + 144#64) = .word d0w := by rw [h144_bv]; exact hm144_bv
      obtain ⟨capw, _, hm216_bv⟩ := hwok.2.2 27 (by omega)
      have hm216 : st.memory (e + 216#64) = .word capw := by rw [h216_bv]; exact hm216_bv
      have hd0w_nat : d0w.toNat = memW st (globN st "ev" + 144) := by
        unfold memW; rw [← h144_bv, hm144]
      have hcapw_nat : capw.toNat = memW st (globN st "ev" + 216) := by
        unfold memW; rw [← h216_bv, hm216]
      -- Unpack the call to set_retdata
      have hcall_eq : evaluateHOLFiniteState st
          (.call (some (none, none)) (ofString "set_retdata") [pExp, nExp]) =
          (none, (evaluateHOLFiniteState st
            (.call (some (none, none)) (ofString "set_retdata") [pExp, nExp])).2) :=
        Prod.ext hnone rfl
      set post := (evaluateHOLFiniteState st
        (.call (some (none, none)) (ofString "set_retdata") [pExp, nExp])).2
      rw [evaluateHOLFiniteState_call] at hcall_eq
      have hargs : evalListHOLFinite st (h := fun a => Classical.propDecidable (st.memaddrs a))
          [pExp, nExp] = some [.val (.word pv), .val (.word nw)] := by
        simp [evalListHOLFinite, evalListHOLExact, evalAt] at hp hn ⊢
        simp [hp, hn]
      have hlook := pan_two_word_lookup st.code.lookup (ofString "set_retdata")
        (ofString "p") (ofString "n") (sourceFnBody Guest.Software.guestFn_set_retdata) pv nw
        (by decide) (by rw [hcode]; exact lookup_set_retdata_fc)
      rw [hargs] at hcall_eq; dsimp only at hcall_eq
      rw [hlook] at hcall_eq; dsimp only at hcall_eq
      by_cases hclk0 : st.clock = 0
      · rw [if_pos hclk0] at hcall_eq; simp at hcall_eq
      · rw [if_neg hclk0] at hcall_eq
        let cmap := (HolFiniteMapExact.empty.update (ofString "p", ValueHOL.val (.word pv))).update
          (ofString "n", ValueHOL.val (.word nw))
        let ent := callEntryStateHOLFinite st cmap
        have hent_p : ent.locals.lookup (ofString "p") = some (.val (.word pv)) := by
          have h1 : ofString "n" ≠ ofString "p" := by decide
          simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, h1]
        have hent_n : ent.locals.lookup (ofString "n") = some (.val (.word nw)) := by
          simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        rcases hbody : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_set_retdata) with ⟨rb, sb⟩
        have hbody' : evaluateHOLFiniteState (callEntryStateHOLFinite st cmap)
            (sourceFnBody Guest.Software.guestFn_set_retdata) = (rb, sb) := hbody
        rw [hbody'] at hcall_eq
        cases rb with
        | none => simp at hcall_eq
        | some rb' =>
          cases rb' with
          | timeOut | «break» | «continue» | error | finalFfi _ | exception _ _ => simp at hcall_eq
          | returned vb =>
            dsimp only at hcall_eq
            by_cases hsh_vb : shapeEqHOL (shapeOfHOLExact vb) .one = true
            · rw [if_pos hsh_vb] at hcall_eq
              injection hcall_eq with _ hpost_sb
              have hpost_eq : post = { sb with locals := st.locals } := hpost_sb.symm
              -- Now step `ent` through `guestFn_set_retdata`
              let e1 := setVarHOLFinite (ofString "cap") (.val (.word capw)) ent
              let e2 := setVarHOLFinite (ofString "dst") (.val (.word d0w)) e1
              let growProg : ProgHOL 64 :=
                .seq
                  (.call (some (some (.local, ofString "dst"), none)) (ofString "alloc")
                    [.op .add [.var .local (ofString "n"), .const 8#64]])
                  (.seq
                    (.store (.op .add [.var .global (ofString "ev"), .const 144#64])
                      (.var .local (ofString "dst")))
                    (.store (.op .add [.var .global (ofString "ev"), .const 216#64])
                      (.var .local (ofString "n"))))
              let tailProg : ProgHOL 64 :=
                .seq
                  (.call (some (none, none)) (ofString "memcpy")
                    [.var .local (ofString "dst"),
                     .var .local (ofString "p"),
                     .var .local (ofString "n")])
                  (.seq
                    (.store (.op .add [.var .global (ofString "ev"), .const 152#64])
                      (.var .local (ofString "n")))
                    (.return (.const 0#64)))
              have hbody_e2 : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_set_retdata) =
                  (let out := evaluateHOLFiniteState e2
                    (.seq (.ite (.cmp .lower (.var .local (ofString "cap")) (.var .local (ofString "n")))
                            growProg .skip)
                          tailProg);
                   (out.1, { out.2 with
                     locals := HolFiniteMapExact.resVarEq
                       (HolFiniteMapExact.resVarEq out.2.locals (ofString "dst", e1.locals.lookup (ofString "dst")))
                       (ofString "cap", ent.locals.lookup (ofString "cap")) })) := by
                have hb : sourceFnBody Guest.Software.guestFn_set_retdata =
                    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
                      (extractFn Guest.Software.guestFn_set_retdata).body := rfl
                rw [hb]
                dsimp only [extractFn, Guest.Software.guestFn_set_retdata,
                  InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
                  InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
                  InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
                  InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
                  InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural,
                  List.map, Option.map]
                rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
                have hcmp0 : @evalHOLExact 64 F _ ent.toExact
                    (fun a => Classical.propDecidable (ent.memaddrs a))
                    (.cmp .equal (.var .local (ofString "n")) (.const 0#64)) =
                    some (.val (.word 0#64)) := by
                  simp [evalHOLExact, hent_n, Compiler.Encoders.Asm.wordCmpHOL, hnw0]
                rw [hcmp0]; dsimp only
                have hz0_eq : (0#64 : BitVec 64) = 0 := rfl
                rw [if_pos hz0_eq, evaluateHOLFiniteState_skip]; dsimp only
                rw [evaluateHOLFiniteState_dec_total]; dsimp only
                have hz_216 : (216#64 : BitVec 64) + 0 = 216#64 := BitVec.add_zero _
                have hz_144 : (144#64 : BitVec 64) + 0 = 144#64 := BitVec.add_zero _
                have hev1 : @evalHOLExact 64 F _ ent.toExact
                    (fun a => Classical.propDecidable (ent.memaddrs a))
                    (.load .one (.op .add [.var .global (ofString "ev"), .const 216#64])) =
                    some (.val (.word capw)) := by
                  have hed216 : ent.memaddrs (e + 216#64) := hdom216
                  have hem216 : ent.memory (e + 216#64) = .word capw := hm216
                  have he_ent : ent.globals.lookup (ofString "ev") = some (.val (.word e)) := he_lk
                  simp only [evalHOLExact, evalListHOLExact, he_ent, valueIsWord, valueWord,
                    wordOpHOL, wordOp, List.all, List.map, Option.map, Bool.and_self, List.foldr, hz_216,
                    memLoadHOLExact, isWfShapeExactHOL, hed216, hem216, ↓reduceIte]
                rw [hev1]; dsimp only
                rw [if_pos (by simp [shapeOfHOLExact, shapeEqHOL])]
                have he1_def : setVarHOLFinite (ofString "cap") (.val (.word capw)) ent = e1 := rfl
                rw [he1_def, evaluateHOLFiniteState_dec_total]; dsimp only
                have he1_ev : e1.globals.lookup (ofString "ev") = some (.val (.word e)) := he_lk
                have he1_dom144 : e1.memaddrs (e + 144#64) := hdom144
                have he1_m144 : e1.memory (e + 144#64) = .word d0w := hm144
                have hev2 : @evalHOLExact 64 F _ e1.toExact
                    (fun a => Classical.propDecidable (e1.memaddrs a))
                    (.load .one (.op .add [.var .global (ofString "ev"), .const 144#64])) =
                    some (.val (.word d0w)) := by
                  simp only [evalHOLExact, evalListHOLExact, he1_ev, valueIsWord, valueWord,
                    wordOpHOL, wordOp, List.all, List.map, Option.map, Bool.and_self, List.foldr, hz_144,
                    memLoadHOLExact, isWfShapeExactHOL, he1_dom144, he1_m144, ↓reduceIte]
                rw [hev2]; dsimp only
                rw [if_pos (by simp [shapeOfHOLExact, shapeEqHOL])]
              rw [hbody_e2] at hbody; dsimp only at hbody
              rcases hout_e2 : evaluateHOLFiniteState e2
                  (.seq (.ite (.cmp .lower (.var .local (ofString "cap")) (.var .local (ofString "n")))
                          growProg .skip)
                        tailProg) with ⟨ro2, so2⟩
              rw [hout_e2] at hbody; dsimp only at hbody
              injection hbody with hro2 hsb_eq
              subst hro2
              have hpost_so2 : post = { so2 with locals := st.locals } := by
                rw [hpost_eq, ← hsb_eq]
              have he2_AR : ArenaReady e2 := ⟨guestInv_with_locals_clock st e2.locals (st.clock - 1) hBS.arena.1, hBS.arena.2⟩
              have he2_p : e2.locals.lookup (ofString "p") = some (.val (.word pv)) := by
                simp [e2, e1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                  show ofString "dst" ≠ ofString "p" by decide,
                  show ofString "cap" ≠ ofString "p" by decide, hent_p]
              have he2_n : e2.locals.lookup (ofString "n") = some (.val (.word nw)) := by
                simp [e2, e1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                  show ofString "dst" ≠ ofString "n" by decide,
                  show ofString "cap" ≠ ofString "n" by decide, hent_n]
              have he2_c : e2.locals.lookup (ofString "cap") = some (.val (.word capw)) := by
                simp [e2, e1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                  show ofString "dst" ≠ ofString "cap" by decide]
              have he2_d : e2.locals.lookup (ofString "dst") = some (.val (.word d0w)) := by
                simp [e2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
              have hcmp_l : @evalHOLExact 64 F _ e2.toExact (fun a => Classical.propDecidable (e2.memaddrs a))
                  (.cmp .lower (.var .local (ofString "cap")) (.var .local (ofString "n"))) =
                  some (.val (.word (if capw.toNat < nw.toNat then 1#64 else 0#64))) := by
                simp only [evalHOLExact, he2_c, he2_n, Compiler.Encoders.Asm.wordCmpHOL]
                by_cases hlt : capw.toNat < nw.toNat
                · have hlt_bv : capw < nw := (BitVec.lt_def).2 hlt
                  simp [hlt, hlt_bv]
                · have hlt_f : ¬ (capw < nw) := fun h => hlt ((BitVec.lt_def).1 h)
                  simp [hlt, hlt_f]
              rw [evaluateHOLFiniteState_seq_line780] at hout_e2
              rcases hite_out : evaluateHOLFiniteState e2
                  (.ite (.cmp .lower (.var .local (ofString "cap")) (.var .local (ofString "n")))
                    growProg .skip) with ⟨ri, si⟩
              rw [hite_out] at hout_e2
              cases ri with
              | some ri' =>
                dsimp only at hout_e2
                injection hout_e2 with hri _
                injection hri with hri'
                exfalso
                have hnr := ite_ne_returned_fc
                  (c := .cmp .lower (.var .local (ofString "cap")) (.var .local (ofString "n")))
                  (y := growProg) (n := .skip)
                  (seq_ne_returned_fc
                    (fun t u => call_assign_local_ne_returned_srd t (ofString "dst") (ofString "alloc") _ u)
                    (seq_ne_returned_fc (fun t u => store_ne_returned_fc t _ _ u)
                      (fun t u => store_ne_returned_fc t _ _ u)))
                  (fun t u => skip_ne_returned_fc t u)
                  e2 vb
                rw [hite_out, hri'] at hnr
                exact hnr rfl
              | none =>
                dsimp only at hout_e2
                -- Unpack `tailProg` from `si`: `memcpy(dst, p, n); *(ev+152) := n; return 0`
                dsimp only [tailProg] at hout_e2
                rw [evaluateHOLFiniteState_seq_line780] at hout_e2
                rcases hmc_out : evaluateHOLFiniteState si
                    (.call (some (none, none)) (ofString "memcpy")
                      [.var .local (ofString "dst"),
                       .var .local (ofString "p"),
                       .var .local (ofString "n")]) with ⟨rmc, smc⟩
                rw [hmc_out] at hout_e2
                cases rmc with
                | some rmc' =>
                  dsimp only at hout_e2
                  injection hout_e2 with hrmc _
                  injection hrmc with hrmc'
                  exact absurd (hmc_out.trans (by rw [hrmc']))
                    (fun h => call0_ne_returned_fc si _ _ vb (congrArg Prod.fst h))
                | none =>
                  dsimp only at hout_e2
                  rw [evaluateHOLFiniteState_ite, hcmp_l] at hite_out
                  dsimp only at hite_out
                  by_cases hlt_cap : capw.toNat < nw.toNat
                  · -- Branch 1: `cap < n` (reallocating)
                    rw [if_pos hlt_cap, if_neg (by decide : (1#64 : BitVec 64) ≠ 0)] at hite_out
                    dsimp only [growProg] at hite_out
                    rw [evaluateHOLFiniteState_seq_line780] at hite_out
                    rcases halloc_out : evaluateHOLFiniteState e2
                        (.call (some (some (.local, ofString "dst"), none)) (ofString "alloc")
                          [.op .add [.var .local (ofString "n"), .const 8#64]]) with ⟨ra0, sa0⟩
                    rw [halloc_out] at hite_out
                    cases ra0 with
                    | some _ => dsimp only at hite_out; simp at hite_out
                    | none =>
                      dsimp only at hite_out
                      -- Unpack `.call (some (some (.local, "dst"), none)) "alloc" [n + 8]`
                      rw [evaluateHOLFiniteState_call] at halloc_out
                      have hev_a : evalListHOLFinite e2 (h := fun a => Classical.propDecidable (e2.memaddrs a))
                          [.op .add [.var .local (ofString "n"), .const 8#64]] =
                          some [.val (.word (nw + 8#64))] := by
                        simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, he2_n,
                          valueIsWord, valueWord, wordOpHOL, wordOp]
                      have hlk_a := pan_one_word_lookup e2.code.lookup (ofString "alloc") (ofString "n")
                        (sourceFnBody Guest.Software.guestFn_alloc) (nw + 8#64)
                        (by rw [he2_AR.1.code]; exact lookup_alloc_fc)
                      rw [hev_a] at halloc_out; dsimp only at halloc_out
                      rw [hlk_a] at halloc_out; dsimp only at halloc_out
                      by_cases hc_e2 : e2.clock = 0
                      · rw [if_pos hc_e2] at halloc_out; simp at halloc_out
                      · rw [if_neg hc_e2] at halloc_out
                        let cmap_a := HolFiniteMapExact.empty.update (ofString "n", ValueHOL.val (.word (nw + 8#64)))
                        let ent_a := callEntryStateHOLFinite e2 cmap_a
                        rcases hrun_a : evaluateHOLFiniteState ent_a (sourceFnBody Guest.Software.guestFn_alloc) with ⟨ra, sa⟩
                        have hrun_a' : evaluateHOLFiniteState (callEntryStateHOLFinite e2 cmap_a)
                            (sourceFnBody Guest.Software.guestFn_alloc) = (ra, sa) := hrun_a
                        rw [hrun_a'] at halloc_out
                        cases ra with
                        | none => simp at halloc_out
                        | some ra' =>
                          cases ra' with
                          | timeOut | «break» | «continue» | error | finalFfi _ | exception _ _ => simp at halloc_out
                          | returned va =>
                            obtain ⟨hpw, qw, rfl, hhpw_hp, hhpw8, hhpw_add_le, hqw_lim, hqw8,
                              hAsa, _, hfb_sa, hsa_mem_e2, hsa_be_e2, hsa_glob_e2⟩ :=
                              alloc_entry_returned_fc e2 (nw + 8#64) he2_AR va (congrArg Prod.fst hrun_a)
                            rw [hrun_a] at hAsa hfb_sa hsa_mem_e2 hsa_be_e2 hsa_glob_e2
                            dsimp only at hAsa hfb_sa hsa_mem_e2 hsa_be_e2 hsa_glob_e2 halloc_out
                            -- Unpack shape check of `.call (some (some (.local, "dst"), none))`
                            have hvalid_dst : isValidValueHOLExact e2.toExact .local (ofString "dst") (.val (.word hpw)) = true := by
                              simp [isValidValueHOLExact, lookupKvarHOLExact, he2_d, shapeOfHOLExact, shapeEqHOL]
                            rw [if_pos (by simp [shapeOfHOLExact, shapeEqHOL]), if_pos hvalid_dst] at halloc_out
                            injection halloc_out with _ hsa0_eq
                            have hsa0_def : sa0 = setVarHOLFinite (ofString "dst") (.val (.word hpw))
                                { sa with locals := e2.locals } := hsa0_eq.symm
                            -- Now `hite_out` is `*(ev+144) := dst; *(ev+216) := n` from `sa0` to `si`
                            rw [evaluateHOLFiniteState_seq_line780] at hite_out
                            have hsa0_ev : sa0.globals.lookup (ofString "ev") = some (.val (.word e)) := by
                              rw [hsa0_def]; dsimp only [setVarHOLFinite]
                              rw [hsa_glob_e2]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
                                show ofString "heap_ptr" ≠ ofString "ev" by decide]
                              exact he_lk
                            have hsa0_dst : sa0.locals.lookup (ofString "dst") = some (.val (.word hpw)) := by
                              rw [hsa0_def]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                            have hsa0_n : sa0.locals.lookup (ofString "n") = some (.val (.word nw)) := by
                              rw [hsa0_def]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                                show ofString "dst" ≠ ofString "n" by decide, he2_n]
                            have hsa0_p : sa0.locals.lookup (ofString "p") = some (.val (.word pv)) := by
                              rw [hsa0_def]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                                show ofString "dst" ≠ ofString "p" by decide, he2_p]
                            have hsa0_dom : sa0.memaddrs = st.memaddrs := by
                              rw [hsa0_def]; dsimp only [setVarHOLFinite]; exact hAsa.1.memaddrs.trans hBS.arena.1.memaddrs.symm
                            have hsa0_mem : sa0.memory = st.memory := by
                              rw [hsa0_def]; dsimp only [setVarHOLFinite]; exact hsa_mem_e2
                            have hsa0_be : sa0.be = st.be := by
                              rw [hsa0_def]; dsimp only [setVarHOLFinite]; exact hsa_be_e2
                            have hst144 : evaluateHOLFiniteState sa0
                                (.store (.op .add [.var .global (ofString "ev"), .const 144#64])
                                  (.var .local (ofString "dst"))) =
                                (none, { sa0 with memory := R14W_srd sa0.memory (BitVec.ofNat 64 (globN st "ev" + 144)) hpw }) :=
                              store_global_off_word_run_srd sa0 hsa0_ev he_nat (by omega)
                                (by rw [hsa0_dom, ← h144_bv]; exact hdom144)
                                (by simp [evalHOLExact, hsa0_dst])
                            rw [hst144] at hite_out; dsimp only at hite_out
                            set sa1 := { sa0 with memory := R14W_srd sa0.memory (BitVec.ofNat 64 (globN st "ev" + 144)) hpw }
                            have hst216 : evaluateHOLFiniteState sa1
                                (.store (.op .add [.var .global (ofString "ev"), .const 216#64])
                                  (.var .local (ofString "n"))) =
                                (none, { sa1 with memory := R14W_srd sa1.memory (BitVec.ofNat 64 (globN st "ev" + 216)) nw }) :=
                              store_global_off_word_run_srd sa1 hsa0_ev he_nat (by omega)
                                (by change sa0.memaddrs _; rw [hsa0_dom, ← h216_bv]; exact hdom216)
                                (by simp [evalHOLExact, show sa1.locals = sa0.locals from rfl, hsa0_n])
                            rw [hst216] at hite_out
                            injection hite_out with _ hsi_eq
                            have hsi_def : si = { sa1 with memory := R14W_srd sa1.memory (BitVec.ofNat 64 (globN st "ev" + 216)) nw } := hsi_eq.symm
                            -- Step `si` through `memcpy(hpw, pv, nw)` to get `hpw + nw ≤ heapEnd` and `ByteRegionEffect`
                            have hsi_code : si.code = originalRuntimeCode := by
                              rw [hsi_def]; change sa0.code = _; rw [hsa0_def]; exact hAsa.1.code
                            have hsi_G : GuestInv si := by
                              refine ⟨hsi_code, ?_, ?_, ?_⟩
                              · rw [hsi_def]; change sa0.memaddrs = _; rw [hsa0_def]; exact hAsa.1.memaddrs
                              · rw [hsi_def]; change sa0.shMemaddrs = _; rw [hsa0_def]; exact hAsa.1.shMemaddrs
                              · rw [hsi_def]; change sa0.baseAddr = _; rw [hsa0_def]; exact hAsa.1.baseAddr
                            have hsi_dst : @evalHOLExact 64 F _ si.toExact (fun a => Classical.propDecidable (si.memaddrs a))
                                (.var .local (ofString "dst")) = some (.val (.word hpw)) := by
                              simp [evalHOLExact, show si.locals = sa0.locals by rw [hsi_def], hsa0_dst]
                            have hsi_p : @evalHOLExact 64 F _ si.toExact (fun a => Classical.propDecidable (si.memaddrs a))
                                (.var .local (ofString "p")) = some (.val (.word pv)) := by
                              simp [evalHOLExact, show si.locals = sa0.locals by rw [hsi_def], hsa0_p]
                            have hsi_n : @evalHOLExact 64 F _ si.toExact (fun a => Classical.propDecidable (si.memaddrs a))
                                (.var .local (ofString "n")) = some (.val (.word nw)) := by
                              simp [evalHOLExact, show si.locals = sa0.locals by rw [hsi_def], hsa0_n]
                            obtain ⟨hsmc_loc, hmc_bounds⟩ :=
                              call_memcpy_bounds_srd si
                                (.var .local (ofString "dst")) (.var .local (ofString "p")) (.var .local (ofString "n"))
                                hpw pv nw hsi_code hsi_G hsi_dst hsi_p hsi_n smc hmc_out
                            obtain ⟨_, hhpw_nw_he⟩ := hmc_bounds hnw_pos
                            have hhe_val : heapEnd = 33806089704 := R11Shards.heapEnd_val
                            have hnw8_nat : (nw + 8#64).toNat = nw.toNat + 8 := by
                              rw [BitVec.toNat_add, show (8#64 : BitVec 64).toNat = 8 from rfl,
                                  Nat.mod_eq_of_lt (by omega)]
                            -- Now step `st` -> `sa0'` (fresh heap step)
                            set sa0' : PanSemStateFiniteExact 64 F := { sa0 with locals := st.locals }
                            have hsa0'_eq_sa : sa0' = { sa with locals := st.locals } := by
                              dsimp only [sa0']; rw [hsa0_def]; rfl
                            have hsa0'_AR : ArenaReady sa0' := by
                              rw [hsa0'_eq_sa]
                              exact ⟨guestInv_with_locals_clock sa st.locals sa.clock hAsa.1, arenaOK_congr rfl hAsa.2⟩
                            have hsa0'_glob_eq : sa0'.globals = st.globals.update (ofString "heap_ptr", .val (.word qw)) := by
                              change sa0.globals = _; rw [hsa0_def]; exact hsa_glob_e2
                            have hsa0'_hp : globN sa0' "heap_ptr" = qw.toNat := by
                              unfold globN; rw [hsa0'_glob_eq]
                              simp [HolFiniteMapExact.lookup_update, FUPDATE]
                            have hst_hp : globN st "heap_ptr" = hpw.toNat := hhpw_hp.symm
                            have hhp_le : globN st "heap_ptr" ≤ globN sa0' "heap_ptr" := by
                              rw [hst_hp, hsa0'_hp]; omega
                            have hg_kept : GlobalsKept ["heap_ptr"] st sa0' := by
                              intro k hk
                              rw [hsa0'_glob_eq]
                              have hkne : k ≠ ofString "heap_ptr" := by simpa using hk
                              simp [HolFiniteMapExact.lookup_update, FUPDATE, hkne.symm]
                            have hsa0'_mem : sa0'.memory = st.memory := hsa0_mem
                            have hsa0'_be : sa0'.be = st.be := hsa0_be
                            have hbyte_eq : ∀ b : Nat, b < 2 ^ 64 →
                                ¬ (globN st "heap_ptr" ≤ b ∧ b < globN sa0' "heap_ptr") →
                                memB sa0' b = memB st b := by
                              intro b _ _
                              unfold memB; rw [hsa0'_mem, hsa0'_be]
                            obtain ⟨hInv_sa0', hch_sa0', hR_sa0'⟩ :=
                              OpHandlersB.evmInvAt_of_fresh_heap_step hBS.arena hBS.inv hsa0'_AR hsa0'_be
                                hhp_le hg_kept (fun a _ => by rw [hsa0'_mem]) hbyte_eq
                            have hret_sz_le : hpw.toNat + (nw.toNat + 15) / 8 * 8 ≤ qw.toNat := by
                              rw [hnw8_nat] at hhpw_add_le
                              omega
                            have hin_fresh : Inside (hpw.toNat, (nw.toNat + 15) / 8 * 8)
                                (globN st "heap_ptr") (globN sa0' "heap_ptr") := by
                              rw [hst_hp, hsa0'_hp]
                              exact ⟨le_rfl, hret_sz_le⟩
                            obtain ⟨hret_in, hret_disj_fo, hret_disj_ht, hret_disj_fix, hret_avoids, hret_disj_msg⟩ :=
                              fresh_heap_ivl_props_fc hBS.arena hBS.inv hsa0'_AR hsa0'_be
                                hhp_le hg_kept (fun a _ => by rw [hsa0'_mem]) hbyte_eq hin_fresh
                            have hret_wok : WordsOK sa0' (hpw.toNat, (nw.toNat + 15) / 8 * 8) := by
                              have hw0 := hfb_sa.2.2
                              have hsz_eq : ((nw + 8#64).toNat + 7) / 8 * 8 = (nw.toNat + 15) / 8 * 8 := by
                                rw [hnw8_nat]
                              rw [hsz_eq] at hw0
                              refine ⟨hw0.1, hw0.2.1, fun i hi => ?_⟩
                              obtain ⟨w, hdom_i, hm_i⟩ := hw0.2.2 i hi
                              refine ⟨w, ?_, ?_⟩
                              · rw [hsa0'_AR.1.memaddrs, ← hAsa.1.memaddrs]; exact hdom_i
                              · rw [hsa0'_mem]; rw [hsa_mem_e2] at hm_i; exact hm_i
                            have hglob_nonHeap_sa0' : ∀ g : String, ofString g ≠ ofString "heap_ptr" →
                                globN sa0' g = globN st g := by
                              intro g hne
                              exact InitECandidate.Solver.Wave8Contracts.M08.globN_eq_of_lookup
                                (hg_kept (ofString g) (by simp [hne]))
                            have hmw_sa0' : ∀ a, memW sa0' a = memW st a := fun a => by
                              unfold memW; rw [hsa0'_mem]
                            have hRel_sa0' : ReleaseReadyAt sa0' S
                                (memW s0 (globN s0 "cur_cont" + 48))
                                (memW s0 (globN s0 "cur_cont" + 56)) := by
                              have hfs_eq : ∀ ec ∈ evmChain st, frameScratch sa0' ec = frameScratch st ec := by
                                intro ec _; unfold frameScratch; simp only [hmw_sa0']
                              have hfl_eq : ∀ ec ∈ evmChain st, frameLogs sa0' ec = frameLogs st ec := by
                                intro ec _; unfold frameLogs; simp only [hmw_sa0']
                              have hfp_eq : ∀ t ∈ S, htabFootprint sa0' t = htabFootprint st t := by
                                intro t _; unfold htabFootprint hdr; simp only [hmw_sa0']
                              have hfix_eq : fixedObjects sa0' = fixedObjects st := by
                                unfold fixedObjects blockOutObjects balObjects balRecords lstObjects htabValues hdr nodeF
                                simp only [hmw_sa0', hglob_nonHeap_sa0' "bo" (by decide),
                                  hglob_nonHeap_sa0' "bal_accounts" (by decide),
                                  hglob_nonHeap_sa0' "journal" (by decide),
                                  hglob_nonHeap_sa0' "journal_cap" (by decide)]
                                congr 3
                                apply List.map_congr_left
                                intro gn hgn
                                have hne : ofString gn.1 ≠ ofString "heap_ptr" := by revert gn hgn; decide
                                rw [hglob_nonHeap_sa0' gn.1 hne]
                              exact releaseReadyAt_transport hBS.release hhp_le hch_sa0'
                                hfs_eq (fun ec _ => ⟨hmw_sa0' _, hmw_sa0' _⟩)
                                (fun ec hec => Or.inl (hfl_eq ec hec))
                                (fun ec _ => hmw_sa0' _)
                                (fun t ht => Or.inl (hfp_eq t ht)) hfix_eq
                            have hBS_sa0' : FcBranchState s0 sa0' S := by
                              refine ⟨hsa0'_AR, hInv_sa0', hRel_sa0', fcEntryLocals_congr_locals (s1 := st) (s2 := sa0') rfl hBS.locals_ok,
                                hch_sa0'.trans hBS.chain_eq, ?_, ?_, ?_, ?_⟩
                              · rw [hch_sa0']; exact hBS.length_eq
                              · change evmR sa0' ≤ evmR s0; rw [hR_sa0']; exact hBS.r_le
                              · intro ec hec; rw [hch_sa0'] at hec
                                obtain ⟨a, b, c, d⟩ := hBS.cells ec hec
                                exact ⟨(hmw_sa0' _).trans a, (hmw_sa0' _).trans b,
                                  (hmw_sa0' _).trans c, (hmw_sa0' _).trans d⟩
                              · exact (hglob_nonHeap_sa0' "ev" (by decide)).trans hBS.ev_eq
                            -- Step `sa0'` -> `si'` (`*(ev+144) := hpw; *(ev+216) := nw`)
                            set si' : PanSemStateFiniteExact 64 F := { si with locals := st.locals }
                            have hsi'_G : GuestInv si' :=
                              ⟨hsi_G.code, hsi_G.memaddrs, hsi_G.shMemaddrs, hsi_G.baseAddr⟩
                            have hsi'_glob : si'.globals = sa0'.globals := by
                              change si.globals = sa0.globals; rw [hsi_def]
                            have hsi'_be : si'.be = sa0'.be := by
                              change si.be = sa0.be; rw [hsi_def]
                            have hev_sa0' : globN sa0' "ev" = globN st "ev" :=
                              hglob_nonHeap_sa0' "ev" (by decide)
                            have hcc_sa0' : globN sa0' "cur_cont" = globN st "cur_cont" :=
                              hglob_nonHeap_sa0' "cur_cont" (by decide)
                            have hne_144_216 : BitVec.ofNat 64 (globN st "ev" + 144) ≠
                                BitVec.ofNat 64 (globN st "ev" + 216) := by
                              intro heq; have h := congrArg BitVec.toNat heq
                              simp only [BitVec.toNat_ofNat] at h; omega
                            have hsi'_mem_out : ∀ x : BitVec 64,
                                (∀ off ∈ headRetZeroOffs, x ≠ BitVec.ofNat 64 (globN sa0' "ev" + off)) →
                                si'.memory x = sa0'.memory x := by
                              intro x hx
                              rw [hev_sa0'] at hx
                              have hx144 : x ≠ BitVec.ofNat 64 (globN st "ev" + 144) := hx 144 (by decide)
                              have hx216 : x ≠ BitVec.ofNat 64 (globN st "ev" + 216) := hx 216 (by decide)
                              dsimp only [si', sa0']
                              rw [hsi_def]; dsimp only [sa1]
                              simp [R14W_srd, R14Shards.OpHandlersA.updW, hx144, hx216]
                            have hsi'_216 : memW si' (globN sa0' "ev" + 216) = nw.toNat := by
                              rw [hev_sa0']; unfold memW
                              dsimp only [si']
                              rw [hsi_def]; dsimp only [sa1]
                              simp [R14W_srd, R14Shards.OpHandlersA.updW]
                            have hsi'_144 : memW si' (globN sa0' "ev" + 144) = hpw.toNat := by
                              rw [hev_sa0']; unfold memW
                              dsimp only [si']
                              rw [hsi_def]; dsimp only [sa1]
                              simp [R14W_srd, R14Shards.OpHandlersA.updW, hne_144_216]
                            have hsi'_cell : ∀ off : Nat, off + 8 ≤ 280 → off % 8 = 0 →
                                off ≠ 144 → off ≠ 152 → off ≠ 216 →
                                memW si' (globN sa0' "ev" + off) = memW sa0' (globN sa0' "ev" + off) := by
                              intro off hoff _ hn144 hn152 hn216
                              have hnot : ∀ hoff' ∈ headRetZeroOffs,
                                  BitVec.ofNat 64 (globN sa0' "ev" + off) ≠ BitVec.ofNat 64 (globN sa0' "ev" + hoff') := by
                                intro hoff' hm heq
                                rw [hev_sa0'] at heq
                                have hm' : hoff' = 144 ∨ hoff' = 152 ∨ hoff' = 216 := by simpa [headRetZeroOffs] using hm
                                have h := congrArg BitVec.toNat heq
                                rcases hm' with rfl | rfl | rfl <;>
                                  (rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
                                       Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h; omega)
                              unfold memW; rw [hsi'_mem_out _ hnot]
                            have hgas_sum : OpDispatchSpec.evmR st + 1 < 2 ^ 64 := by
                              unfold OpDispatchSpec.evmR; exact hBS.inv.2.2.2.2.2.2.2.2.2.2.2.2
                            have htail_sum_sa0' :
                                (((evmChain sa0').tail.map fun ec => memW sa0' (ec.1 + 64) + memW sa0' (ec.1 + 192)).sum) =
                                (((evmChain st).tail.map fun ec => memW st (ec.1 + 64) + memW st (ec.1 + 192)).sum) := by
                              rw [hch_sa0']; congr 1; apply List.map_congr_left
                              intro ec _; rw [hmw_sa0', hmw_sa0']
                            have hsi'_sp_le : memW si' (globN sa0' "ev" + 16) ≤ memW sa0' (globN sa0' "ev" + 232) := by
                              rw [hsi'_cell 16 (by omega) (by omega) (by omega) (by omega) (by omega),
                                  hmw_sa0', hmw_sa0', hev_sa0']; exact hsp
                            have hsi'_gas_le : memW si' (globN sa0' "ev" + 64) + memW si' (globN sa0' "ev" + 192) +
                                (((evmChain sa0').tail.map fun ec => memW sa0' (ec.1 + 64) + memW sa0' (ec.1 + 192)).sum) + 1 < 2 ^ 64 := by
                              rw [hsi'_cell 64 (by omega) (by omega) (by omega) (by omega) (by omega),
                                  hsi'_cell 192 (by omega) (by omega) (by omega) (by omega) (by omega),
                                  htail_sum_sa0', hmw_sa0', hmw_sa0', hev_sa0', ← hRdec]
                              exact hgas_sum
                            have hsi'_R_le : memW si' (globN sa0' "ev" + 64) + memW si' (globN sa0' "ev" + 192) +
                                (((evmChain sa0').tail.map fun ec => memW sa0' (ec.1 + 64) + memW sa0' (ec.1 + 192)).sum) ≤
                                  OpDispatchSpec.evmR s0 := by
                              rw [hsi'_cell 64 (by omega) (by omega) (by omega) (by omega) (by omega),
                                  hsi'_cell 192 (by omega) (by omega) (by omega) (by omega) (by omega),
                                  htail_sum_sa0', hmw_sa0', hmw_sa0', hev_sa0', ← hRdec]
                              exact hBS.r_le
                            obtain ⟨hBS_si', hch_si', hR_si'_dec, hret_si'⟩ :=
                              fcBranchState_of_head_ret_set_fc hBS_sa0' hsi'_G hsi'_glob hsi'_be rfl
                                hsi'_mem_out hnw_pos hsi'_216 hsi'_144
                                hret_in hret_wok hret_disj_fo hret_disj_ht hret_disj_fix hret_avoids hret_disj_msg
                                hsi'_sp_le hsi'_gas_le hsi'_R_le
                            have hR_si' : OpDispatchSpec.evmR si' = OpDispatchSpec.evmR st := by
                              rw [hR_si'_dec,
                                  hsi'_cell 64 (by omega) (by omega) (by omega) (by omega) (by omega),
                                  hsi'_cell 192 (by omega) (by omega) (by omega) (by omega) (by omega),
                                  htail_sum_sa0', hmw_sa0', hmw_sa0', hev_sa0', ← hRdec]
                            -- Step `si'` -> `smc'` (`memcpy(hpw, pv, nw)`)
                            set smc' : PanSemStateFiniteExact 64 F := { smc with locals := st.locals }
                            have hsi_dom : si.memaddrs = ordinaryDomain := hBS_si'.arena.1.memaddrs
                            have hnt_mc : (evaluateHOLFiniteState si
                                (.call (some (none, none)) (ofString "memcpy")
                                  [.var .local (ofString "dst"),
                                   .var .local (ofString "p"),
                                   .var .local (ofString "n")])).1 ≠ some .timeOut := by
                              rw [hmc_out]; simp
                            have hmc_bre_pair :=
                              InitECandidate.Solver.Wave8GuestInv.M11.eval_call_memcpy_bre
                                si (.var .local (ofString "dst")) (.var .local (ofString "p")) (.var .local (ofString "n"))
                                hpw pv nw [frameRet si' (globN si' "ev", globN si' "cur_cont")]
                                hsi_code hsi_dom hsi_dst hsi_p hsi_n
                                (fun _ => ⟨frameRet si' (globN si' "ev", globN si' "cur_cont"), List.mem_singleton.2 rfl, by
                                  have hev_si' : globN si' "ev" = globN sa0' "ev" := by unfold globN; rw [hsi'_glob]
                                  have hcc_si' : globN si' "cur_cont" = globN sa0' "cur_cont" := by unfold globN; rw [hsi'_glob]
                                  rw [hev_si', hcc_si', hret_si']; dsimp only; omega⟩)
                                hnt_mc
                            have hbre_si_smc : InitECandidate.Solver.Wave8Contracts.M23.ByteRegionEffect si smc
                                [frameRet si' (globN si' "ev", globN si' "cur_cont")] := by
                              have h1 := hmc_bre_pair.1 (by rw [hmc_out])
                              rw [hmc_out] at h1
                              exact ⟨h1.1.code, h1.1.memaddrs, h1.1.shMemaddrs, h1.1.baseAddr,
                                h1.1.be, h1.1.globals, h1.1.out_dom, h1.1.cell_frame, h1.1.byte_frame⟩
                            have hbre_si'_smc' : InitECandidate.Solver.Wave8Contracts.M23.ByteRegionEffect si' smc'
                                [frameRet si' (globN si' "ev", globN si' "cur_cont")] :=
                              ⟨hbre_si_smc.code, hbre_si_smc.memaddrs, hbre_si_smc.shMemaddrs,
                               hbre_si_smc.baseAddr, hbre_si_smc.be, hbre_si_smc.globals,
                               hbre_si_smc.out_dom, hbre_si_smc.cell_frame, hbre_si_smc.byte_frame⟩
                            obtain ⟨hBS_smc', hch_smc', hR_smc', hcell_smc'⟩ :=
                              fcBranchState_of_head_payload_bre hBS_si' hbre_si'_smc' rfl (Or.inr (Or.inr rfl))
                            -- Step `smc'` -> `post` (`*(ev+152) := nw; return 0`)
                            rw [evaluateHOLFiniteState_seq_line780] at hout_e2
                            have hsmc_ev : smc.globals.lookup (ofString "ev") = some (.val (.word e)) := by
                              rw [hbre_si_smc.globals]; change si'.globals.lookup _ = _
                              rw [hsi'_glob]; exact hsa0_ev
                            have hsmc_n : smc.locals.lookup (ofString "n") = some (.val (.word nw)) := by
                              rw [hsmc_loc, show si.locals = sa0.locals by rw [hsi_def]]; exact hsa0_n
                            have hsmc_dom152 : smc.memaddrs (BitVec.ofNat 64 (globN st "ev" + 152)) := by
                              rw [hbre_si_smc.memaddrs, hsi_dom, ← hBS.arena.1.memaddrs, ← h152_bv]; exact hdom152
                            have hst152 : evaluateHOLFiniteState smc
                                (.store (.op .add [.var .global (ofString "ev"), .const 152#64])
                                  (.var .local (ofString "n"))) =
                                (none, { smc with memory := R14W_srd smc.memory (BitVec.ofNat 64 (globN st "ev" + 152)) nw }) :=
                              store_global_off_word_run_srd smc hsmc_ev he_nat (by omega) hsmc_dom152
                                (by simp [evalHOLExact, hsmc_n])
                            rw [hst152] at hout_e2; dsimp only at hout_e2
                            rw [evaluateHOLFiniteState_return] at hout_e2
                            simp only [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL,
                              Nat.reduceLeDiff, ↓reduceIte] at hout_e2
                            injection hout_e2 with _ hso2_eq
                            have hpost_final : post = { smc' with
                                memory := R14W_srd smc'.memory (BitVec.ofNat 64 (globN st "ev" + 152)) nw,
                                clock := smc.clock } := by
                              rw [hpost_so2, ← hso2_eq]; rfl
                            have hev_smc' : globN smc' "ev" = globN st "ev" := by
                              have h1 : globN smc' "ev" = globN si' "ev" := by unfold globN; rw [hbre_si'_smc'.globals]
                              have h2 : globN si' "ev" = globN sa0' "ev" := by unfold globN; rw [hsi'_glob]
                              rw [h1, h2, hev_sa0']
                            have hpost_G : GuestInv post := by
                              rw [hpost_final]
                              exact ⟨hBS_smc'.arena.1.code, hBS_smc'.arena.1.memaddrs,
                                hBS_smc'.arena.1.shMemaddrs, hBS_smc'.arena.1.baseAddr⟩
                            have hpost_glob : post.globals = smc'.globals := by rw [hpost_final]
                            have hpost_be : post.be = smc'.be := by rw [hpost_final]
                            have hpost_loc : post.locals = smc'.locals := by rw [hpost_final]
                            have hpost_mem_out : ∀ x : BitVec 64,
                                (∀ off ∈ headSimpleOffs, x ≠ BitVec.ofNat 64 (globN smc' "ev" + off)) →
                                post.memory x = smc'.memory x := by
                              intro x hx
                              rw [hev_smc'] at hx
                              have hx152 : x ≠ BitVec.ofNat 64 (globN st "ev" + 152) := hx 152 (by decide)
                              rw [hpost_final]
                              change R14W_srd smc'.memory (BitVec.ofNat 64 (globN st "ev" + 152)) nw x = smc'.memory x
                              simp [R14W_srd, R14Shards.OpHandlersA.updW, hx152]
                            have hpost_cell_ne152 : ∀ off : Nat, off + 8 ≤ 280 → off ≠ 152 →
                                memW post (globN st "ev" + off) = memW smc' (globN st "ev" + off) := by
                              intro off hoff hn152
                              have hne_bv : BitVec.ofNat 64 (globN st "ev" + off) ≠
                                  BitVec.ofNat 64 (globN st "ev" + 152) := by
                                intro heq; have h := congrArg BitVec.toNat heq
                                rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
                                    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h
                                omega
                              unfold memW; rw [hpost_final]; dsimp only
                              simp [R14W_srd, R14Shards.OpHandlersA.updW, hne_bv]
                            have hev_si' : globN si' "ev" = globN st "ev" := by
                              have h2 : globN si' "ev" = globN sa0' "ev" := by unfold globN; rw [hsi'_glob]
                              rw [h2, hev_sa0']
                            have hsmc'_st_cell : ∀ off : Nat, off + 8 ≤ 280 → off % 8 = 0 →
                                off ≠ 144 → off ≠ 152 → off ≠ 216 →
                                memW smc' (globN st "ev" + off) = memW st (globN st "ev" + off) := by
                              intro off hoff hmod hn144 hn152 hn216
                              have h1 := hcell_smc' off hoff hmod
                              rw [hev_si'] at h1
                              have h2 := hsi'_cell off hoff hmod hn144 hn152 hn216
                              rw [hev_sa0'] at h2
                              exact h1.trans (h2.trans (hmw_sa0' _))
                            have htail_sum_smc' :
                                (((evmChain smc').tail.map fun ec => memW smc' (ec.1 + 64) + memW smc' (ec.1 + 192)).sum) =
                                (((evmChain st).tail.map fun ec => memW st (ec.1 + 64) + memW st (ec.1 + 192)).sum) := by
                              have h_ev_smc' : OpDispatchSpec.evmR smc' =
                                  memW smc' (globN smc' "ev" + 64) + memW smc' (globN smc' "ev" + 192) +
                                    (((evmChain smc').tail.map fun ec => memW smc' (ec.1 + 64) + memW smc' (ec.1 + 192)).sum) :=
                                (ev_head_facts_srd hBS_smc'.arena hBS_smc'.inv).2.2.2.2
                              have hc64 := hsmc'_st_cell 64 (by omega) (by omega) (by omega) (by omega) (by omega)
                              have hc192 := hsmc'_st_cell 192 (by omega) (by omega) (by omega) (by omega) (by omega)
                              rw [hev_smc', hc64, hc192, hR_smc', hR_si', hRdec] at h_ev_smc'
                              omega
                            have hpost_sp_le : memW post (globN smc' "ev" + 16) ≤ memW smc' (globN smc' "ev" + 232) := by
                              rw [hev_smc', hpost_cell_ne152 16 (by omega) (by omega),
                                  hsmc'_st_cell 16 (by omega) (by omega) (by omega) (by omega) (by omega),
                                  hsmc'_st_cell 232 (by omega) (by omega) (by omega) (by omega) (by omega)]
                              exact hsp
                            have hpost_gas_le : memW post (globN smc' "ev" + 64) + memW post (globN smc' "ev" + 192) +
                                (((evmChain smc').tail.map fun ec => memW smc' (ec.1 + 64) + memW smc' (ec.1 + 192)).sum) + 1 < 2 ^ 64 := by
                              rw [hev_smc', hpost_cell_ne152 64 (by omega) (by omega),
                                  hpost_cell_ne152 192 (by omega) (by omega),
                                  hsmc'_st_cell 64 (by omega) (by omega) (by omega) (by omega) (by omega),
                                  hsmc'_st_cell 192 (by omega) (by omega) (by omega) (by omega) (by omega),
                                  htail_sum_smc', ← hRdec]
                              exact hgas_sum
                            have hpost_R_le : memW post (globN smc' "ev" + 64) + memW post (globN smc' "ev" + 192) +
                                (((evmChain smc').tail.map fun ec => memW smc' (ec.1 + 64) + memW smc' (ec.1 + 192)).sum) ≤
                                  OpDispatchSpec.evmR s0 := by
                              rw [hev_smc', hpost_cell_ne152 64 (by omega) (by omega),
                                  hpost_cell_ne152 192 (by omega) (by omega),
                                  hsmc'_st_cell 64 (by omega) (by omega) (by omega) (by omega) (by omega),
                                  hsmc'_st_cell 192 (by omega) (by omega) (by omega) (by omega) (by omega),
                                  htail_sum_smc', ← hRdec]
                              exact hBS.r_le
                            have hBS_post := fcBranchState_of_head_simple hBS_smc' hpost_G hpost_glob hpost_be
                              hpost_loc hpost_mem_out hpost_sp_le hpost_gas_le hpost_R_le
                            obtain ⟨_, _, hch_post, _, _, _, hR_post_dec⟩ :=
                              evmInvAt_of_head_simple hBS_smc'.arena hBS_smc'.inv hpost_G hpost_glob hpost_be
                                hpost_mem_out hpost_sp_le hpost_gas_le
                            have hev_post : globN post "ev" = globN st "ev" := by
                              have h1 : globN post "ev" = globN smc' "ev" := by unfold globN; rw [hpost_glob]
                              rw [h1, hev_smc']
                            have hR_post_eq : OpDispatchSpec.evmR post = OpDispatchSpec.evmR st := by
                              rw [hR_post_dec, hev_smc',
                                  hpost_cell_ne152 64 (by omega) (by omega),
                                  hpost_cell_ne152 192 (by omega) (by omega),
                                  hsmc'_st_cell 64 (by omega) (by omega) (by omega) (by omega) (by omega),
                                  hsmc'_st_cell 192 (by omega) (by omega) (by omega) (by omega) (by omega),
                                  htail_sum_smc', ← hRdec]
                            refine ⟨hBS_post, hpost_loc, ?_,
                              hch_post.trans (hch_smc'.trans (hch_si'.trans hch_sa0')),
                              le_of_eq hR_post_eq, ?_, ?_, ?_⟩
                            · intro g hne
                              have h1 : globN post g = globN smc' g := by unfold globN; rw [hpost_glob]
                              have h2 : globN smc' g = globN si' g := by unfold globN; rw [hbre_si'_smc'.globals]
                              have h3 : globN si' g = globN sa0' g := by unfold globN; rw [hsi'_glob]
                              rw [h1, h2, h3, hglob_nonHeap_sa0' g hne]
                            · rw [hev_post, hpost_cell_ne152 16 (by omega) (by omega)]
                              exact hsmc'_st_cell 16 (by omega) (by omega) (by omega) (by omega) (by omega)
                            · rw [hev_post, hpost_cell_ne152 40 (by omega) (by omega)]
                              exact hsmc'_st_cell 40 (by omega) (by omega) (by omega) (by omega) (by omega)
                            · rw [hev_post, hpost_cell_ne152 232 (by omega) (by omega)]
                              exact hsmc'_st_cell 232 (by omega) (by omega) (by omega) (by omega) (by omega)
                  · -- Branch 2: `n ≤ cap` (in-place)
                    have hle_cap : nw.toNat ≤ capw.toNat := Nat.le_of_not_lt hlt_cap
                    have hz0_eq : (0#64 : BitVec 64) = 0 := rfl
                    rw [if_neg hlt_cap, if_pos hz0_eq, evaluateHOLFiniteState_skip] at hite_out
                    injection hite_out with _ hsi_eq
                    have hsi_def : si = e2 := hsi_eq.symm
                    subst hsi_def
                    have he2_code : e2.code = originalRuntimeCode := he2_AR.1.code
                    have he2_dom : e2.memaddrs = ordinaryDomain := he2_AR.1.memaddrs
                    have he2_dst_ev : @evalHOLExact 64 F _ e2.toExact (fun a => Classical.propDecidable (e2.memaddrs a))
                        (.var .local (ofString "dst")) = some (.val (.word d0w)) := by
                      simp [evalHOLExact, he2_d]
                    have he2_p_ev : @evalHOLExact 64 F _ e2.toExact (fun a => Classical.propDecidable (e2.memaddrs a))
                        (.var .local (ofString "p")) = some (.val (.word pv)) := by
                      simp [evalHOLExact, he2_p]
                    have he2_n_ev : @evalHOLExact 64 F _ e2.toExact (fun a => Classical.propDecidable (e2.memaddrs a))
                        (.var .local (ofString "n")) = some (.val (.word nw)) := by
                      simp [evalHOLExact, he2_n]
                    have hnt_mc2 : (evaluateHOLFiniteState e2
                        (.call (some (none, none)) (ofString "memcpy")
                          [.var .local (ofString "dst"),
                           .var .local (ofString "p"),
                           .var .local (ofString "n")])).1 ≠ some .timeOut := by
                      rw [hmc_out]; simp
                    have hcap_pos : 0 < memW st (globN st "ev" + 216) := by
                      rw [← hcapw_nat]; omega
                    have hret_st : frameRet st (globN st "ev", globN st "cur_cont") =
                        (d0w.toNat, (capw.toNat + 15) / 8 * 8) := by
                      unfold frameRet; dsimp only
                      rw [if_neg (by omega), hd0w_nat, hcapw_nat]
                    have hmc2_pair :=
                      InitECandidate.Solver.Wave8GuestInv.M11.eval_call_memcpy_bre
                        e2 (.var .local (ofString "dst")) (.var .local (ofString "p")) (.var .local (ofString "n"))
                        d0w pv nw [frameRet st (globN st "ev", globN st "cur_cont")]
                        he2_code he2_dom he2_dst_ev he2_p_ev he2_n_ev
                        (fun _ => ⟨frameRet st (globN st "ev", globN st "cur_cont"), List.mem_singleton.2 rfl, by
                          rw [hret_st]; dsimp only; omega⟩)
                        hnt_mc2
                    have hbre_e2_smc : InitECandidate.Solver.Wave8Contracts.M23.ByteRegionEffect e2 smc
                        [frameRet st (globN st "ev", globN st "cur_cont")] := by
                      have h1 := hmc2_pair.1 (by rw [hmc_out])
                      rw [hmc_out] at h1
                      exact ⟨h1.1.code, h1.1.memaddrs, h1.1.shMemaddrs, h1.1.baseAddr,
                        h1.1.be, h1.1.globals, h1.1.out_dom, h1.1.cell_frame, h1.1.byte_frame⟩
                    have hsmc_loc2 : smc.locals = e2.locals := by
                      have h1 := hmc2_pair.1 (by rw [hmc_out])
                      rw [hmc_out] at h1; exact h1.2
                    set smc' : PanSemStateFiniteExact 64 F := { smc with locals := st.locals }
                    have hbre_st_smc' : InitECandidate.Solver.Wave8Contracts.M23.ByteRegionEffect st smc'
                        [frameRet st (globN st "ev", globN st "cur_cont")] :=
                      ⟨hbre_e2_smc.code, hbre_e2_smc.memaddrs, hbre_e2_smc.shMemaddrs,
                       hbre_e2_smc.baseAddr, hbre_e2_smc.be, hbre_e2_smc.globals,
                       hbre_e2_smc.out_dom, hbre_e2_smc.cell_frame, hbre_e2_smc.byte_frame⟩
                    obtain ⟨hBS_smc', hch_smc', hR_smc', hcell_smc'⟩ :=
                      fcBranchState_of_head_payload_bre hBS hbre_st_smc' rfl (Or.inr (Or.inr rfl))
                    -- Step `smc'` -> `post` (`*(ev+152) := nw; return 0`)
                    rw [evaluateHOLFiniteState_seq_line780] at hout_e2
                    have hsmc_ev : smc.globals.lookup (ofString "ev") = some (.val (.word e)) := by
                      rw [hbre_e2_smc.globals]; exact he_lk
                    have hsmc_n : smc.locals.lookup (ofString "n") = some (.val (.word nw)) := by
                      rw [hsmc_loc2]; exact he2_n
                    have hsmc_dom152 : smc.memaddrs (BitVec.ofNat 64 (globN st "ev" + 152)) := by
                      rw [hbre_e2_smc.memaddrs, ← h152_bv]; exact hdom152
                    have hst152 : evaluateHOLFiniteState smc
                        (.store (.op .add [.var .global (ofString "ev"), .const 152#64])
                          (.var .local (ofString "n"))) =
                        (none, { smc with memory := R14W_srd smc.memory (BitVec.ofNat 64 (globN st "ev" + 152)) nw }) :=
                      store_global_off_word_run_srd smc hsmc_ev he_nat (by omega) hsmc_dom152
                        (by simp [evalHOLExact, hsmc_n])
                    rw [hst152] at hout_e2; dsimp only at hout_e2
                    rw [evaluateHOLFiniteState_return] at hout_e2
                    simp only [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL,
                      Nat.reduceLeDiff, ↓reduceIte] at hout_e2
                    injection hout_e2 with _ hso2_eq
                    have hpost_final : post = { smc' with
                        memory := R14W_srd smc'.memory (BitVec.ofNat 64 (globN st "ev" + 152)) nw,
                        clock := smc.clock } := by
                      rw [hpost_so2, ← hso2_eq]; rfl
                    have hev_smc' : globN smc' "ev" = globN st "ev" := by
                      unfold globN; rw [hbre_st_smc'.globals]
                    have hpost_G : GuestInv post := by
                      rw [hpost_final]
                      exact ⟨hBS_smc'.arena.1.code, hBS_smc'.arena.1.memaddrs,
                        hBS_smc'.arena.1.shMemaddrs, hBS_smc'.arena.1.baseAddr⟩
                    have hpost_glob : post.globals = smc'.globals := by rw [hpost_final]
                    have hpost_be : post.be = smc'.be := by rw [hpost_final]
                    have hpost_loc : post.locals = smc'.locals := by rw [hpost_final]
                    have hpost_mem_out : ∀ x : BitVec 64,
                        (∀ off ∈ headSimpleOffs, x ≠ BitVec.ofNat 64 (globN smc' "ev" + off)) →
                        post.memory x = smc'.memory x := by
                      intro x hx
                      rw [hev_smc'] at hx
                      have hx152 : x ≠ BitVec.ofNat 64 (globN st "ev" + 152) := hx 152 (by decide)
                      rw [hpost_final]
                      change R14W_srd smc'.memory (BitVec.ofNat 64 (globN st "ev" + 152)) nw x = smc'.memory x
                      simp [R14W_srd, R14Shards.OpHandlersA.updW, hx152]
                    have hpost_cell_ne152 : ∀ off : Nat, off + 8 ≤ 280 → off ≠ 152 →
                        memW post (globN st "ev" + off) = memW smc' (globN st "ev" + off) := by
                      intro off hoff hn152
                      have hne_bv : BitVec.ofNat 64 (globN st "ev" + off) ≠
                          BitVec.ofNat 64 (globN st "ev" + 152) := by
                        intro heq; have h := congrArg BitVec.toNat heq
                        rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
                            Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h
                        omega
                      unfold memW; rw [hpost_final]; dsimp only
                      simp [R14W_srd, R14Shards.OpHandlersA.updW, hne_bv]
                    have hgas_sum : OpDispatchSpec.evmR st + 1 < 2 ^ 64 := by
                      unfold OpDispatchSpec.evmR; exact hBS.inv.2.2.2.2.2.2.2.2.2.2.2.2
                    have htail_sum_smc' :
                        (((evmChain smc').tail.map fun ec => memW smc' (ec.1 + 64) + memW smc' (ec.1 + 192)).sum) =
                        (((evmChain st).tail.map fun ec => memW st (ec.1 + 64) + memW st (ec.1 + 192)).sum) := by
                      have h_ev_smc' : OpDispatchSpec.evmR smc' =
                          memW smc' (globN smc' "ev" + 64) + memW smc' (globN smc' "ev" + 192) +
                            (((evmChain smc').tail.map fun ec => memW smc' (ec.1 + 64) + memW smc' (ec.1 + 192)).sum) :=
                        (ev_head_facts_srd hBS_smc'.arena hBS_smc'.inv).2.2.2.2
                      rw [hev_smc', hcell_smc' 64 (by omega) (by omega),
                          hcell_smc' 192 (by omega) (by omega), hR_smc', hRdec] at h_ev_smc'
                      omega
                    have hpost_sp_le : memW post (globN smc' "ev" + 16) ≤ memW smc' (globN smc' "ev" + 232) := by
                      rw [hev_smc', hpost_cell_ne152 16 (by omega) (by omega),
                          hcell_smc' 16 (by omega) (by omega),
                          hcell_smc' 232 (by omega) (by omega)]
                      exact hsp
                    have hpost_gas_le : memW post (globN smc' "ev" + 64) + memW post (globN smc' "ev" + 192) +
                        (((evmChain smc').tail.map fun ec => memW smc' (ec.1 + 64) + memW smc' (ec.1 + 192)).sum) + 1 < 2 ^ 64 := by
                      rw [hev_smc', hpost_cell_ne152 64 (by omega) (by omega),
                          hpost_cell_ne152 192 (by omega) (by omega),
                          hcell_smc' 64 (by omega) (by omega),
                          hcell_smc' 192 (by omega) (by omega),
                          htail_sum_smc', ← hRdec]
                      exact hgas_sum
                    have hpost_R_le : memW post (globN smc' "ev" + 64) + memW post (globN smc' "ev" + 192) +
                        (((evmChain smc').tail.map fun ec => memW smc' (ec.1 + 64) + memW smc' (ec.1 + 192)).sum) ≤
                          OpDispatchSpec.evmR s0 := by
                      rw [hev_smc', hpost_cell_ne152 64 (by omega) (by omega),
                          hpost_cell_ne152 192 (by omega) (by omega),
                          hcell_smc' 64 (by omega) (by omega),
                          hcell_smc' 192 (by omega) (by omega),
                          htail_sum_smc', ← hRdec]
                      exact hBS.r_le
                    have hBS_post := fcBranchState_of_head_simple hBS_smc' hpost_G hpost_glob hpost_be
                      hpost_loc hpost_mem_out hpost_sp_le hpost_gas_le hpost_R_le
                    obtain ⟨_, _, hch_post, _, _, _, hR_post_dec⟩ :=
                      evmInvAt_of_head_simple hBS_smc'.arena hBS_smc'.inv hpost_G hpost_glob hpost_be
                        hpost_mem_out hpost_sp_le hpost_gas_le
                    have hev_post : globN post "ev" = globN st "ev" := by
                      have h1 : globN post "ev" = globN smc' "ev" := by unfold globN; rw [hpost_glob]
                      rw [h1, hev_smc']
                    have hR_post_eq : OpDispatchSpec.evmR post = OpDispatchSpec.evmR st := by
                      rw [hR_post_dec, hev_smc',
                          hpost_cell_ne152 64 (by omega) (by omega),
                          hpost_cell_ne152 192 (by omega) (by omega),
                          hcell_smc' 64 (by omega) (by omega),
                          hcell_smc' 192 (by omega) (by omega),
                          htail_sum_smc', ← hRdec]
                    refine ⟨hBS_post, hpost_loc, ?_,
                      hch_post.trans hch_smc', le_of_eq hR_post_eq, ?_, ?_, ?_⟩
                    · intro g _
                      have h1 : globN post g = globN smc' g := by unfold globN; rw [hpost_glob]
                      have h2 : globN smc' g = globN st g := by unfold globN; rw [hbre_st_smc'.globals]
                      rw [h1, h2]
                    · rw [hev_post, hpost_cell_ne152 16 (by omega) (by omega)]
                      exact hcell_smc' 16 (by omega) (by omega)
                    · rw [hev_post, hpost_cell_ne152 40 (by omega) (by omega)]
                      exact hcell_smc' 40 (by omega) (by omega)
                    · rw [hev_post, hpost_cell_ne152 232 (by omega) (by omega)]
                      exact hcell_smc' 232 (by omega) (by omega)
            · rw [if_neg hsh_vb] at hcall_eq; simp at hcall_eq

end InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk
