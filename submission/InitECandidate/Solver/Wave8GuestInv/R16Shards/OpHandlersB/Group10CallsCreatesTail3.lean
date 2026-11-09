import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.Group10CallsCreatesTail2

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.GuestGlobalKeep
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R11Shards
open InitECandidate.Solver.Wave8GuestInv.R11Shards.OpDispatchSpec
open InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA
open InitECandidate.Solver.Wave8GuestInv.R16Shards (evmInvAt_of_htab_step evaluate_be_eq)
open InitECandidate.Solver.Wave8GuestInv.R16Shards.StateRestoreEpilogue (noCatchableRaise evaluate_noCatchableRaise)
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers
open InitECandidate.Solver.Wave8Contracts.M23

/-! ## Milestone 5 (call family, part 2): `op_callcode` / `op_call` / `op_delegatecall`

The three remaining call-family opcodes reuse the `op_staticcall` machinery of
`Group10CallsCreatesTail2` with two additions forced by value transfer:

* `op_callcode` and `op_call` carry the popped `value` through `u256_is_zero`
  (stipend selection) and `calculate_message_call_gas` (stipend refund), and both
  have a failure path (`insufficient != 0`) that restores the regular-gas word
  `ev+64` by adding back `mcg.1` — a store that can RAISE the `evmR` sum.  The
  strict `evmR` decrease is banked earlier at `charge_gas(need)` (the need word
  is at least the stipend plus one) and carried as a credit invariant
  `evmR t + m0 + Sl + 1 ≤ evmR s0`, discharged at the restore store.
* `op_call` additionally charges state gas for a possible new account and refunds
  it on the failure path (`credit_state_gas_refund`), which touches only the
  state-gas word `ev+72` and leaves `evmR` untouched. -/

/-- Public copy of the `u256_is_zero` runtime-code lookup (the Helpers2 one is private). -/
theorem lookup_u256_is_zero_pub_g10 :
    originalRuntimeCode.lookup (ofString "u256_is_zero") =
      some ([(ofString "a", .comb [.one, .one, .one, .one])],
        sourceFnBody Guest.Software.guestFn_u256_is_zero, .one) :=
  lookup_of_guestAst_getElem 42 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_u256_is_zero) rfl

/-- A value of four-one shape is a record of four words. -/
theorem value_word4_of_shape_g10 {v : ValueHOL 64}
    (hsh : shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact v) = true) :
    ∃ q0 q1 q2 q3 : BitVec 64,
      v = .rStruct [.val (.word q0), .val (.word q1), .val (.word q2), .val (.word q3)] := by
  rcases v with _ | vs | _
  · exact absurd hsh (by simp [shapeOfHOLExact, shapeEqHOL])
  · rcases vs with _ | ⟨v0, _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | ⟨v4, _⟩⟩⟩⟩⟩
    · exact absurd hsh (by simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL])
    · exact absurd hsh (by simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL])
    · exact absurd hsh (by simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL])
    · exact absurd hsh (by simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL])
    · rcases v0 with ⟨⟨q0⟩⟩ | _ | _
      · rcases v1 with ⟨⟨q1⟩⟩ | _ | _
        · rcases v2 with ⟨⟨q2⟩⟩ | _ | _
          · rcases v3 with ⟨⟨q3⟩⟩ | _ | _
            · exact ⟨q0, q1, q2, q3, rfl⟩
            · exact absurd hsh (by simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL])
            · exact absurd hsh (by simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL])
          · exact absurd hsh (by simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL])
          · exact absurd hsh (by simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL])
        · exact absurd hsh (by simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL])
        · exact absurd hsh (by simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL])
      · exact absurd hsh (by simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL])
      · exact absurd hsh (by simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL])
    · exact absurd hsh (by simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL])
  · exact absurd hsh (by simp [shapeOfHOLExact, shapeEqHOL])

/-- Binding lemma for the two `u256_is_zero` call sites of this shard: the callee
frame maps `"a"` to the single argument (which the caller has pinned as a four-word
record). -/
theorem u256_is_zero_args_lookup_g10 {body' : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {ret' : ShapeHOL} {v0 : ValueHOL 64}
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "u256_is_zero") [v0] =
      some (body', callee, ret')) :
    ∃ q0 q1 q2 q3 : BitVec 64,
      v0 = .rStruct [.val (.word q0), .val (.word q1), .val (.word q2), .val (.word q3)] ∧
      callee.lookup (ofString "a") =
        some (.rStruct [.val (.word q0), .val (.word q1), .val (.word q2), .val (.word q3)]) := by
  have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
    originalRuntimeCode.lookup (ofString "u256_is_zero") [v0] body' callee ret' hl
  simp only [Flapjack.lookupCodeHOLExact, lookup_u256_is_zero_pub_g10] at hx
  split at hx
  · rename_i hcond
    have heq := Option.some.inj hx
    rcases Prod.mk.inj heq with ⟨rfl, hrest⟩
    rcases Prod.mk.inj hrest with ⟨hloc, rfl⟩
    have hsh : shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact v0) = true := by
      simpa using hcond.2.2
    obtain ⟨q0, q1, q2, q3, rfl⟩ := value_word4_of_shape_g10 hsh
    refine ⟨q0, q1, q2, q3, rfl, ?_⟩
    have hfn := congrFun hloc.symm (ofString "a")
    simpa [FUPDATE_LIST, FUPDATE] using hfn
  · cases hx

/-- Value of the `op_callcode`/`op_call` failure-path restore store: the new head
regular-gas word is the old one plus the call stipend word `m1`, hence at most
`old + m1.toNat` (word addition is modulo `2^64`). -/
theorem eval_store64_add_g10 {F : Type} {t : PanSemStateFiniteExact 64 F}
    {m0 m1 : BitVec 64} {v : ValueHOL 64}
    (hmcg : t.locals.lookup (ofString "mcg") =
      some (.rStruct [.val (.word m0), .val (.word m1)]))
    (hv : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
      (.op BinOp.add
        [.load ShapeHOL.one (.op BinOp.add [.var (.global) (ofString "ev"), .const 64#64]),
         .rfield 1 (.var (.local) (ofString "mcg"))]) = some v) :
    ∃ w : BitVec 64, v = .val (.word w) ∧
      w.toNat ≤ memW t (globN t "ev" + 64) + m1.toNat := by
  simp only [evalHOLExact, evalListHOLExact] at hv
  split at hv
  · rename_i vs hvs
    simp only [hmcg] at hvs
    rcases hg : t.globals.lookup (ofString "ev") with _ | gv
    · simp [hg, valueIsWord, valueWord, wordOpHOL, wordOp] at hvs
    · rcases gv with ⟨⟨ex⟩⟩ | _ | _
      · rcases Classical.em (t.memaddrs (ex + 64#64)) with hdom | hdom
        · rcases hm : t.memory (ex + 64#64) with ⟨ew⟩
          simp [hg, hdom, hm, valueIsWord, valueWord, wordOpHOL, wordOp, memLoadHOLExact] at hvs
          have hvs' : [.val (.word ew), .val (.word m1)] = vs := by
            simp [hvs]
          rw [← hvs'] at hv
          simp [valueIsWord, valueWord, wordOpHOL, wordOp] at hv
          have hv' : v = .val (.word (ew + m1)) := by simpa using hv.symm
          refine ⟨ew + m1, hv', ?_⟩
          have hgn : globN t "ev" = ex.toNat := by simp only [globN, hg]
          have hadd : BitVec.ofNat 64 (globN t "ev" + 64) = ex + 64#64 := by
            rw [hgn, BitVec.add_def]; simp
          have hmem : memW t (globN t "ev" + 64) = ew.toNat := by
            simp only [memW, hadd, hm]
          rw [BitVec.toNat_add, hmem]
          exact Nat.mod_le _ _
        · simp [hg, valueIsWord, valueWord, wordOpHOL, wordOp, memLoadHOLExact,
            isWfShapeExactHOL] at hvs
          rw [if_neg hdom] at hvs
          simp at hvs
      · simp [hg, valueIsWord, valueWord, wordOpHOL, wordOp] at hvs
      · simp [hg, valueIsWord, valueWord, wordOpHOL, wordOp] at hvs
  · simp at hv

/-- The failure-path head regular-gas store (`ev+64`) for op_callcode / op_call:
writes `w` with `w.toNat ≤ memW t (ev+64) + K` at the head frame's regular-gas word.
Preserves `EvmInv`, `HeadMemChainWF` and the chain, and the post `evmR` stays strictly
below `evmR s0` via the credit `evmR t + K + 1 ≤ evmR s0`. -/
theorem ev64_store_evmStep_g10 {F : Type} {s0 t : PanSemStateFiniteExact 64 F}
    {w : BitVec 64} {K : Nat}
    (hInv : EvmInv t) (hWF : Group10.HeadMemChainWF t)
    (hwK : w.toNat ≤ memW t (globN t "ev" + 64) + K)
    (hcredit : evmR t + K + 1 ≤ evmR s0)
    (hgastop : evmR s0 + 1 < 2 ^ 64) :
    EvmInv { t with memory := R14Shards.OpHandlersA.updW t.memory (BitVec.ofNat 64 (globN t "ev" + 64)) w } ∧
    Group10.HeadMemChainWF { t with memory := R14Shards.OpHandlersA.updW t.memory (BitVec.ofNat 64 (globN t "ev" + 64)) w } ∧
    evmChain { t with memory := R14Shards.OpHandlersA.updW t.memory (BitVec.ofNat 64 (globN t "ev" + 64)) w } = evmChain t ∧
    evmR { t with memory := R14Shards.OpHandlersA.updW t.memory (BitVec.ofNat 64 (globN t "ev" + 64)) w } < evmR s0 := by
  obtain ⟨hAR, S, hWT, hrest⟩ := hInv
  dsimp only at hrest
  obtain ⟨hch_ne, hch_len, hlast, hFWF, hFRoom, hRetW, hPair, hDisj, hTries, hMarks, hRoles, hGasSum⟩ := hrest
  set e0 := globN t "ev" with he0def
  set c0 := globN t "cur_cont" with hc0def
  set post := { t with memory := R14Shards.OpHandlersA.updW t.memory (BitVec.ofNat 64 (e0 + 64)) w } with hpostdef
  have hec0_mem : (e0, c0) ∈ evmChain t := by simp [evmChain, evmChainFrom, e0, c0]
  have hF0 := hFWF (e0, c0) hec0_mem
  have he0_blk := hF0.1 (e0, 280) (by simp)
  have he0_lt : e0 + 280 < 2 ^ 64 := by
    have hbb := he0_blk.1.2; rw [R11Shards.scratchEnd_val] at hbb; omega
  have hmem_out : ∀ a : BitVec 64, a ≠ BitVec.ofNat 64 (e0 + 64) → post.memory a = t.memory a := by
    intro a ha
    simp [hpostdef, R14Shards.OpHandlersA.updW, ha]
  obtain ⟨tl, hch_eq⟩ : ∃ tl, evmChain t = (e0, c0) :: tl := ⟨_, rfl⟩
  have hPcopy := hPair
  rw [hch_eq, List.map_cons, List.flatten_cons, List.pairwise_append] at hPcopy
  obtain ⟨hP0, _, hcross⟩ := hPcopy
  have hA : (e0, 280) ∈ frameObjects t (e0, c0) := by simp [frameObjects]
  have hBitVec_ne : ∀ n m : Nat, n < 2 ^ 64 → m < 2 ^ 64 → n ≠ m →
      BitVec.ofNat 64 n ≠ BitVec.ofNat 64 m := by
    intro n m hn hm hne h
    have hc := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at hc
    rw [Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hm] at hc
    omega
  have hhead64 : memW post (e0 + 64) = w.toNat := by
    simp only [memW, hpostdef]
    simp [R14Shards.OpHandlersA.updW]
  have hhead192 : memW post (e0 + 192) = memW t (e0 + 192) := by
    unfold memW
    rw [show post.memory (BitVec.ofNat 64 (e0 + 192)) = t.memory (BitVec.ofNat 64 (e0 + 192)) from
      hmem_out _ (hBitVec_ne _ _ (by omega) (by omega) (by omega))]
  have htail : ∀ ec ∈ tl, memW post (ec.1 + 64) = memW t (ec.1 + 64) ∧
      memW post (ec.1 + 192) = memW t (ec.1 + 192) := by
    intro ec hec
    have hFec := hFWF ec (by rw [hch_eq]; exact List.mem_cons_of_mem _ hec)
    have hec_blk := hFec.1 (ec.1, 280) (by simp)
    have hec_lt : ec.1 + 280 < 2 ^ 64 := by
      have hbb := hec_blk.1.2; rw [R11Shards.scratchEnd_val] at hbb; omega
    have hB : (ec.1, 280) ∈ (tl.map (frameObjects t)).flatten :=
      List.mem_flatten.2 ⟨frameObjects t ec, List.mem_map_of_mem hec, by simp [frameObjects]⟩
    have hd := hcross _ hA _ hB
    unfold Disj at hd; dsimp only at hd
    refine ⟨?_, ?_⟩
    · unfold memW
      rw [show post.memory (BitVec.ofNat 64 (ec.1 + 64)) = t.memory (BitVec.ofNat 64 (ec.1 + 64)) from
        hmem_out _ (hBitVec_ne _ _ (by omega) (by omega) (by omega))]
    · unfold memW
      rw [show post.memory (BitVec.ofNat 64 (ec.1 + 192)) = t.memory (BitVec.ofNat 64 (ec.1 + 192)) from
        hmem_out _ (hBitVec_ne _ _ (by omega) (by omega) (by omega))]
  have hsum : ((evmChain t).map fun ec => memW post (ec.1 + 64) + memW post (ec.1 + 192)).sum
      + memW t (e0 + 64) = evmR t + w.toNat := by
    have hRt : evmR t = ((evmChain t).map fun ec => memW t (ec.1 + 64) + memW t (ec.1 + 192)).sum := rfl
    simp only [hch_eq, List.map_cons, List.sum_cons, hhead64, hhead192, hRt]
    have hmap : ((tl.map fun ec => memW post (ec.1 + 64) + memW post (ec.1 + 192))).sum
        = ((tl.map fun ec => memW t (ec.1 + 64) + memW t (ec.1 + 192))).sum := by
      have hm : (tl.map fun ec => memW post (ec.1 + 64) + memW post (ec.1 + 192))
          = (tl.map fun ec => memW t (ec.1 + 64) + memW t (ec.1 + 192)) :=
        List.map_congr_left (fun ec hec => by rw [(htail ec hec).1, (htail ec hec).2])
      rw [hm]
    rw [hmap]
    ac_rfl
  have hgas : ((evmChain t).map fun ec => memW post (ec.1 + 64) + memW post (ec.1 + 192)).sum
      + 1 < 2 ^ 64 := by omega
  have hGp : GuestInv post := guestInv_updW_g10 hAR.1 (BitVec.ofNat 64 (e0 + 64)) w
  have hInvT : EvmInv t := ⟨hAR, S, hWT, hch_ne, hch_len, hlast, hFWF, hFRoom, hRetW, hPair,
    hDisj, hTries, hMarks, hRoles, hGasSum⟩
  have hmain := evmInv_of_head_gas_store_g10 (s := t) (post := post) hInvT hGp rfl rfl
    (fun x hx => hmem_out x hx) hgas
  have hAn : BitVec.toNat (BitVec.ofNat 64 (e0 + 64)) = e0 + 64 := by
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]
  have hWFp : Group10.HeadMemChainWF post :=
    headMemChainWF_store_headSafe hInvT hWF
      (x := BitVec.ofNat 64 (e0 + 64))
      (Or.inl ⟨64, by rw [hAn], by omega, by omega, by omega, by omega⟩)
      rfl hmain.2 (fun a ha => hmem_out a ha)
  refine ⟨hmain.1, hWFp, hmain.2, ?_⟩
  have hRp : evmR post = ((evmChain t).map fun ec => memW post (ec.1 + 64) + memW post (ec.1 + 192)).sum := by
    show ((evmChain post).map fun ec => memW post (ec.1 + 64) + memW post (ec.1 + 192)).sum = _
    rw [hmain.2]
  rw [hRp]
  omega

/-! ### Charged-accounting infrastructure for the call family -/

/-- Any `EvmPreservingSpecA` can expose its built-in `evmR`-monotonicity through the
post-condition, so continuation proofs can transport gas credits through the call. -/
theorem epsA_keepR_g10
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {Qret : ∀ {F : Type}, PanSemStateFiniteExact 64 F → ValueHOL 64 →
      PanSemStateFiniteExact 64 F → Prop}
    {nm : MlS} (h : EvmPreservingSpecA P Qret nm) :
    EvmPreservingSpecA P (fun s v post => Qret s v post ∧ evmR post ≤ evmR s) nm := by
  obtain ⟨params, body, rs, hlk, hspec⟩ := h
  refine ⟨params, body, rs, hlk, ?_⟩
  intro F s hcode hInv hWF hP hl hnt
  have hr := hspec s hcode hInv hWF hP hl hnt
  dsimp only at hr ⊢
  refine ⟨fun v hv => ?_, fun he => ?_⟩
  · obtain ⟨hIW, hch, hR, hQ⟩ := hr.1 v hv
    exact ⟨hIW, hch, hR, ⟨hQ, hR⟩⟩
  · exact hr.2 he

/-- `charge_gas` call whose continuation post-condition receives the exact accounting
fact `evmR cpost + amtw = evmR t` (plus the globals and chain pins), letting the
continuation establish gas credits; the charged flag flips to `true` like
`seq_charge_gas`, but the strict drop is discharged from `hpos` when flipping from
`charged = false`. -/
theorem HandlerRunA.seq_charge_gas_acc_g10 {F : Type}
    {s0 : PanSemStateFiniteExact 64 F}
    {P Q : PanSemStateFiniteExact 64 F → Prop} {charged : Bool}
    {amtExp : ExpHOL 64} {cont : ProgHOL 64}
    (hpos : ∀ t (w : BitVec 64),
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) amtExp =
        some (.val (.word w)) → EvmInv t → Group10.HeadMemChainWF t → P t →
        charged = true ∨ 0 < w.toNat)
    (hstep : ∀ t cpost (amtw : BitVec 64),
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) amtExp =
        some (.val (.word amtw)) →
      EvmInv t → Group10.HeadMemChainWF t → P t → evmR t ≤ evmR s0 →
      EvmInv cpost → Group10.HeadMemChainWF cpost →
      cpost.globals = t.globals →
      memW cpost (globN cpost "ev" + 32) = memW t (globN t "ev" + 32) →
      evmChain cpost = evmChain t →
      evmR cpost + amtw.toNat = evmR t →
      Q { cpost with locals := t.locals })
    (hcont : HandlerRunA s0 Q true cont) :
    HandlerRunA s0 P charged
      (.seq (.call (some (none, none)) (ofString "charge_gas") [amtExp]) cont) := by
  intro t hc hi hw hlen hR hp hn
  have hR_le := rboundA_to_le_g10 hR
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_call] at hn ⊢
  rcases hargs : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) [amtExp] with _ | values
  · exact opDispatchPostA_error s0 t
  · simp only [hargs] at hn ⊢
    rcases hl : lookupCodeHOLFinite t.code.lookup (ofString "charge_gas") values with _ | ⟨body', callee, ret'⟩
    · exact opDispatchPostA_error s0 t
    · simp only [hl] at hn ⊢
      by_cases hz : t.clock = 0
      · simp [hz] at hn
      · simp only [hz, ↓reduceIte] at hn ⊢
        have hv_list : ∃ v0, @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) amtExp = some v0 ∧ values = [v0] := by
          rw [evalListHOLFinite_eq_toExact] at hargs
          simp only [evalListHOLExact] at hargs
          rcases he : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) amtExp with _ | v0
          · simp [he] at hargs
          · simp only [he, Option.some.injEq] at hargs; exact ⟨v0, rfl, hargs.symm⟩
        obtain ⟨v0, hv0_ev, rfl⟩ := hv_list
        have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "charge_gas") [v0] =
            some (body', callee, ret') := by rwa [← hc]
        obtain ⟨rfl, rfl, amtw, rfl, hamt_cal⟩ :=
          R14Shards.OpHandlersA.one_word_arg_lookup M21.lookup_charge_gas hl_orig
        have hpos' := hpos t amtw hv0_ev hi hw hp
        have hi_ce : EvmInv (callEntryStateHOLFinite t callee) := localsFree_evmInv t callee (t.clock - 1) hi
        have hw_ce : Group10.HeadMemChainWF (callEntryStateHOLFinite t callee) :=
          Group10.headMemChainWF_locals t callee (t.clock - 1) hw
        have hch_ce : evmChain (callEntryStateHOLFinite t callee) = evmChain t :=
          OpDispatchSpec.evmChain_congr rfl rfl
        have hR_ce : OpDispatchSpec.evmR (callEntryStateHOLFinite t callee)
            = OpDispatchSpec.evmR t := by
          unfold OpDispatchSpec.evmR
          rw [hch_ce, OpDispatchSpec.memW_congr
            (show (callEntryStateHOLFinite t callee).memory = t.memory from rfl)]
        have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata
          (callEntryStateHOLFinite t callee) (sourceFnBody Guest.Software.guestFn_charge_gas)).1
        have hcg := charge_gas_body_exactA (callEntryStateHOLFinite t callee) hi_ce hw_ce hamt_cal
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite t callee)
            (sourceFnBody Guest.Software.guestFn_charge_gas) with ⟨res, cpost⟩
        simp only [hrun] at hn hmeta hcg ⊢
        change cpost.code = t.code at hmeta
        cases res with
        | none => exact opDispatchPostA_error s0 cpost
        | some r0' =>
          cases r0' with
          | timeOut => simp at hn
          | returned v =>
            by_cases hsh_ok : shapeEqHOL (shapeOfHOLExact v) .one = true
            · simp only [hsh_ok, ↓reduceIte] at hn ⊢
              obtain ⟨⟨hi_cp, hw_cp⟩, hglob_cp, hch_cp, hR_cp⟩ := hcg.1 v rfl
              rw [hR_ce] at hR_cp
              -- the ev+32 pin, from the keep32 spec applied at the call entry
              obtain ⟨p0, b0, r0, hl0, hspec0⟩ := epsA_charge_gas_exact_keep32_g10
              have hb_eq : sourceFnBody Guest.Software.guestFn_charge_gas = b0 :=
                lookupCodeHOLFinite_installed_body t.code.lookup
                  (ofString "charge_gas") p0 b0 (sourceFnBody Guest.Software.guestFn_charge_gas) r0
                  ShapeHOL.one [.val (.word amtw)] callee (by rwa [hc]) hl
              have hrs_eq : ShapeHOL.one = r0 := by
                have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
                  originalRuntimeCode.lookup (ofString "charge_gas") [.val (.word amtw)]
                  (sourceFnBody Guest.Software.guestFn_charge_gas) callee ShapeHOL.one hl_orig
                simp only [Flapjack.lookupCodeHOLExact, hl0] at hx
                split at hx
                · exact (congrArg (fun x => x.2.2) (Option.some.inj hx)).symm
                · cases hx
              have hlook_ce : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "charge_gas")
                  [.val (.word amtw)] = some (b0, callee, r0) := by
                rw [← hb_eq, ← hrs_eq]
                exact hl_orig
              have hnt_ce : (evaluateHOLFiniteState (callEntryStateHOLFinite t callee) b0).1
                  ≠ some .timeOut := by
                rw [← hb_eq, hrun]
                simp
              have hspec_ret := hspec0 (callEntryStateHOLFinite t callee) hc hi_ce hw_ce trivial
                ⟨[.val (.word amtw)], hlook_ce⟩ hnt_ce
              dsimp only at hspec_ret
              obtain ⟨_, _, _, _, hmem32_cp⟩ :=
                (hspec_ret.1 v (by rw [← hb_eq, hrun])).2.2.2
              have hmem32_t : memW cpost (globN cpost "ev" + 32) = memW t (globN t "ev" + 32) := by
                have hgev : globN cpost "ev" = globN t "ev" := globN_congr_g10 hglob_cp "ev"
                rw [hgev]
                rw [← hb_eq, hrun] at hmem32_cp
                exact hmem32_cp
              let resumed : PanSemStateFiniteExact 64 F := { cpost with locals := t.locals }
              have hi_res : EvmInv resumed := localsFree_evmInv cpost t.locals cpost.clock hi_cp
              have hw_res : Group10.HeadMemChainWF resumed :=
                Group10.headMemChainWF_locals cpost t.locals cpost.clock hw_cp
              have hch_res : evmChain resumed = evmChain cpost := OpDispatchSpec.evmChain_congr rfl rfl
              have hlen_res : (evmChain resumed).length = (evmChain s0).length := by
                rw [hch_res, hch_cp, hch_ce]; exact hlen
              have hR_lt : OpDispatchSpec.evmR resumed < OpDispatchSpec.evmR s0 := by
                have hR_res : OpDispatchSpec.evmR resumed = OpDispatchSpec.evmR cpost := by
                  unfold OpDispatchSpec.evmR
                  rw [hch_res, OpDispatchSpec.memW_congr
                    (show resumed.memory = cpost.memory from rfl)]
                rw [hR_res]
                rcases hpos' with he | hgt
                · rw [he] at hR; simp only [↓reduceIte] at hR; omega
                · omega
              exact hcont resumed (hmeta.trans hc) hi_res hw_res hlen_res (by simp [hR_lt])
                (hstep t cpost amtw hv0_ev hi hw hp hR_le hi_cp hw_cp hglob_cp hmem32_t
                  (hch_cp.trans (OpDispatchSpec.evmChain_congr rfl rfl)) hR_cp)
                (by simpa [resumed] using hn)
            · simp only [hsh_ok, Bool.false_eq_true, ↓reduceIte]
              exact opDispatchPostA_error s0 cpost
          | exception eid ev =>
            by_cases heid : eid = ofString "EvmErr"
            · subst heid
              obtain ⟨⟨hi_cp, hw_cp⟩, _, hch_cp, hR_cp⟩ := hcg.2 ⟨ev, rfl⟩
              have hi_el : EvmInv cpost.emptyLocalsHOLFinite := localsFree_evmInv cpost _ cpost.clock hi_cp
              have hw_el : Group10.HeadMemChainWF cpost.emptyLocalsHOLFinite :=
                Group10.headMemChainWF_locals cpost _ cpost.clock hw_cp
              have hch_el : evmChain cpost.emptyLocalsHOLFinite = evmChain cpost :=
                OpDispatchSpec.evmChain_congr rfl rfl
              have hR_el : OpDispatchSpec.evmR cpost.emptyLocalsHOLFinite
                  = OpDispatchSpec.evmR cpost := by
                unfold OpDispatchSpec.evmR
                rw [hch_el, OpDispatchSpec.memW_congr
                  (show cpost.emptyLocalsHOLFinite.memory = cpost.memory from rfl)]
              refine ⟨?_, fun _ => ⟨⟨hi_el, hw_el⟩, ?_, ?_⟩⟩
              · rintro ⟨_, h⟩; cases h
              · rw [hch_el, hch_cp, hch_ce]; exact hlen
              · rw [hR_el, hR_cp, hR_ce]; exact hR_le
            · refine opDispatchPostA_other (fun _ h => by cases h) ?_
              rintro ⟨_, h⟩; injection h with h'; injection h' with h1 _; exact heid h1
          | «break» => exact opDispatchPostA_error s0 cpost
          | «continue» => exact opDispatchPostA_error s0 cpost
          | finalFfi _ =>
              refine opDispatchPostA_other (fun _ h => by cases h) ?_
              rintro ⟨_, h⟩; cases h
          | error => exact opDispatchPostA_error s0 cpost.emptyLocalsHOLFinite

/-- Seeded variant of `opHandlerSpecA_of_run`: the run lemma may assume `EvmInv s0`
as its invariant post-condition, which the walk carries through every continuation
step (needed deep inside for the head-gas-sum bound `evmR s0 + 1 < 2^64`). -/
theorem opHandlerSpecA_of_run_seed_g10 (idx : Nat)
    (hidx : idx < Guest.Software.guestAst.length)
    (d : Decl (BitVec 64)) (hd : Guest.Software.guestAst[idx] = .function (extractFn d))
    (hrun : ∀ {F : Type} (s0 : PanSemStateFiniteExact 64 F),
      EvmInv s0 → Group10.HeadMemChainWF s0 → ¬ EvmDone s0 →
      HandlerRunA s0 (fun _ => EvmInv s0) false
        (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural (extractFn d).body)) :
    OpHandlerSpecA (ofString (extractFn d).name) := by
  refine ⟨_, _, _, lookup_of_guestAst_getElem idx hidx (extractFn d) hd, ?_⟩
  intro F s0 hcode ⟨hInv, hWF, hnd⟩ _ hnt
  exact hrun s0 hInv hWF hnd s0 hcode hInv hWF rfl (le_refl _) hInv hnt

/-! ### `op_callcode` prefix (Stage B) -/

/-- The `vz == 0` comparison evaluates against the pinned `vz` local. -/
theorem cmp_eq_vz_word_g10 {F : Type} {t : PanSemStateFiniteExact 64 F} {vz : BitVec 64}
    (hlk : t.locals.lookup (ofString "vz") = some (.val (.word vz))) :
    @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
      (.cmp .equal (.var .local (ofString "vz")) (.const 0#64)) =
      some (.val (.word (if vz = 0#64 then 1#64 else 0#64))) := by
  simp [evalHOLExact, hlk, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]

/-- Generic carry-through combinator for `decCall` nodes whose post-state
satisfies the same predicate as the pre-state. -/
theorem HandlerRunA.decCall_carry_g10 {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {P : PanSemStateFiniteExact 64 F → Prop} {charged : Bool}
    {nm : MlS} {sh : ShapeHOL} {fname : MlS} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    {Qc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hf : EvmPreservingSpecA (fun _ => True) Qc fname)
    (htr : ∀ (t : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
        (cpost : PanSemStateFiniteExact 64 F), P t →
      P (setVarHOLFinite nm v { cpost with locals := t.locals }))
    (hcont : HandlerRunA s0 P charged cont) :
    HandlerRunA s0 P charged (.decCall nm sh fname args cont) :=
  HandlerRunA.decCall hf (by intros; trivial)
    (fun t values body callee rs v cpost _ _ hp _ _ _ _ _ _ => htr t v cpost hp) hcont

/-- Generic carry-through combinator for `dec` nodes. -/
theorem HandlerRunA.dec_carry_g10 {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {P : PanSemStateFiniteExact 64 F → Prop} {charged : Bool}
    {nm : MlS} {sh : ShapeHOL} {init : ExpHOL 64} {body : ProgHOL 64}
    (htr : ∀ (t : PanSemStateFiniteExact 64 F) (v : ValueHOL 64), P t →
      P (setVarHOLFinite nm v t))
    (hbody : HandlerRunA s0 P charged body) :
    HandlerRunA s0 P charged (.dec nm sh init body) :=
  HandlerRunA.dec (Q := P) (hinit := fun t v _ _ hp => htr t v hp) hbody

/-- Post-`vz`-decCall bundle for the `op_callcode` prefix: the `value` local is
pinned as a four-word record, `vz` as a word in `{0, 1}`, and `vz = 1` forces all
four value limbs to be zero. -/
def CcVzQ_g10 {F : Type} (t : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ (q0 q1 q2 q3 vz : BitVec 64),
    t.locals.lookup (ofString "value") =
      some (.rStruct [.val (.word q0), .val (.word q1), .val (.word q2), .val (.word q3)]) ∧
    t.locals.lookup (ofString "vz") = some (.val (.word vz)) ∧
    (vz = 0#64 ∨ vz = 1#64) ∧
    (vz = 1#64 → (q0 ||| q1 ||| q2 ||| q3) = 0#64)

/-- Post-`transfer_cost`-ite bundle: the stipend correlation between `vz` and
`transfer_cost`. -/
def CcTcQ_g10 {F : Type} (t : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ (q0 q1 q2 q3 vz tcw : BitVec 64),
    t.locals.lookup (ofString "value") =
      some (.rStruct [.val (.word q0), .val (.word q1), .val (.word q2), .val (.word q3)]) ∧
    t.locals.lookup (ofString "vz") = some (.val (.word vz)) ∧
    t.locals.lookup (ofString "transfer_cost") = some (.val (.word tcw)) ∧
    ((vz = 0#64 ∧ tcw = 11300#64) ∨
      (vz = 1#64 ∧ tcw = 0#64 ∧ (q0 ||| q1 ||| q2 ||| q3) = 0#64))

/-- The `need` bundle: `need` covers the sum of the pinned access and transfer
costs. -/
def CcNdQ_g10 {F : Type} (t : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ (nw acw tcw : BitVec 64),
    t.locals.lookup (ofString "access_cost") = some (.val (.word acw)) ∧
    t.locals.lookup (ofString "transfer_cost") = some (.val (.word tcw)) ∧
    t.locals.lookup (ofString "need") = some (.val (.word nw)) ∧
    acw.toNat + tcw.toNat ≤ nw.toNat

/-- Post-need-charge bundle for `op_callcode`: the prefix's pins plus the
`Sl`-credit, where the stipend `Sl` is 2300 when a value transfer may occur
(`vz = 0`) and 0 otherwise. -/
def CcPQ_g10 {F : Type} (s0 t : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ (q0 q1 q2 q3 vz tcw acw cw ebw : BitVec 64) (Sl : Nat),
    t.locals.lookup (ofString "value") =
      some (.rStruct [.val (.word q0), .val (.word q1), .val (.word q2), .val (.word q3)]) ∧
    t.locals.lookup (ofString "vz") = some (.val (.word vz)) ∧
    t.locals.lookup (ofString "transfer_cost") = some (.val (.word tcw)) ∧
    t.locals.lookup (ofString "access_cost") = some (.val (.word acw)) ∧
    (acw = 100#64 ∨ acw = 3000#64) ∧
    t.locals.lookup (ofString "x") =
      some (.rStruct [.val (.word cw), .val (.word ebw)]) ∧
    (ebw = 0#64 ∨ (memW t (globN t "ev" + 32) + ebw.toNat < 2 ^ 37 ∧
      (memW t (globN t "ev" + 32) + ebw.toNat) % 32 = 0)) ∧
    ((vz = 0#64 ∧ tcw = 11300#64 ∧ Sl = 2300) ∨
      (vz = 1#64 ∧ tcw = 0#64 ∧ (q0 ||| q1 ||| q2 ||| q3) = 0#64 ∧ Sl = 0)) ∧
    evmR t + Sl + 1 ≤ evmR s0 ∧ EvmInv s0

/-- The `vz == 0` ite with the branch post-conditions carrying the `vz`
correlation: the yes-branch runs with `vz = 0` pinned, the no-branch with
`vz = 1`. -/
theorem HandlerRunA.seq_ite_vz_g10 {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {P : PanSemStateFiniteExact 64 F → Prop} {charged : Bool}
    {yes no cont : ProgHOL 64}
    (hpin : ∀ t, P t → ∃ vz : BitVec 64,
      t.locals.lookup (ofString "vz") = some (.val (.word vz)) ∧ (vz = 0#64 ∨ vz = 1#64))
    (hyes : HandlerRunA s0
      (fun t => P t ∧ ∃ vz : BitVec 64,
        t.locals.lookup (ofString "vz") = some (.val (.word vz)) ∧ vz = 0#64)
      charged (.seq yes cont))
    (hno : HandlerRunA s0
      (fun t => P t ∧ ∃ vz : BitVec 64,
        t.locals.lookup (ofString "vz") = some (.val (.word vz)) ∧ vz = 1#64)
      charged (.seq no cont)) :
    HandlerRunA s0 P charged
      (.seq (.ite (.cmp .equal (.var .local (ofString "vz")) (.const 0#64)) yes no) cont) := by
  intro t hc hi hw hlen hR hp hnt
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt ⊢
  revert hnt
  split
  · rename_i w hcond
    obtain ⟨vz, hlk, h01⟩ := hpin t hp
    have hcmp := cmp_eq_vz_word_g10 (t := t) (vz := vz) hlk
    rw [hcmp] at hcond
    injection hcond with i1
    injection i1 with i2
    injection i2 with i3
    by_cases hw0 : w = 0
    · subst hw0
      have hvz1 : vz = 1#64 := by
        by_cases hz : vz = 0#64
        · rw [hz] at i3; simp at i3
        · rcases h01 with h0 | h1'
          · exact absurd h0 hz
          · exact h1'
      simp only [↓reduceIte]
      rw [← evaluateHOLFiniteState_seq_line780]
      intro hnt
      exact hno t hc hi hw hlen hR ⟨hp, vz, hlk, hvz1⟩ hnt
    · have hvz0 : vz = 0#64 := by
        by_cases hz : vz = 0#64
        · exact hz
        · rw [if_neg hz] at i3; exact absurd i3.symm hw0
      simp only [hw0, ↓reduceIte]
      rw [← evaluateHOLFiniteState_seq_line780]
      intro hnt
      exact hyes t hc hi hw hlen hR ⟨hp, vz, hlk, hvz0⟩ hnt
  · intro _; dsimp only; exact opDispatchPostA_error s0 t

/-- The `op_callcode` pops (nodes 1-11): seven `decCall`s, two `dec`s, and the
`x` `decCall`, threading the seeded `EvmInv s0`. -/
theorem op_callcode_pops_g10 {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {charged : Bool} {cont : ProgHOL 64}
    (hcont : HandlerRunA s0 (fun t => scXQ t ∧ EvmInv s0) charged cont) :
    HandlerRunA s0 (fun _ => EvmInv s0) charged
      (.decCall (ofString "gasv") (.comb [.one, .one, .one, .one]) (ofString "stack_pop") []
        (.decCall (ofString "cav") (.comb [.one, .one, .one, .one]) (ofString "stack_pop") []
          (.decCall (ofString "code_address0") .one (ofString "to_address_masked")
            [.var .local (ofString "cav")]
            (.decCall (ofString "value") (.comb [.one, .one, .one, .one]) (ofString "stack_pop") []
              (.decCall (ofString "in_start") (.comb [.one, .one, .one, .one]) (ofString "stack_pop") []
                (.decCall (ofString "in_size") (.comb [.one, .one, .one, .one]) (ofString "stack_pop") []
                  (.decCall (ofString "out_start") (.comb [.one, .one, .one, .one]) (ofString "stack_pop") []
                    (.decCall (ofString "out_size") (.comb [.one, .one, .one, .one]) (ofString "stack_pop") []
                      (.dec (ofString "msg") .one
                        (.load .one (.op .add [.var .global (ofString "ev"),
                          .const (BitVec.ofNat 64 112)]))
                        (.dec (ofString "to") .one
                          (.load .one (.op .add [.var .local (ofString "msg"),
                            .const (BitVec.ofNat 64 32)]))
                          (.decCall (ofString "x") (.comb [.one, .one]) (ofString "extend_memory_cost2")
                            [.var .local (ofString "in_start"), .var .local (ofString "in_size"),
                             .var .local (ofString "out_start"), .var .local (ofString "out_size")]
                            cont))))))))))) := by
  refine HandlerRunA.decCall_carry_g10 (P := fun _ => EvmInv s0) epsA_stack_pop_le_g10 (fun _ _ _ hp => hp) ?_
  refine HandlerRunA.decCall_carry_g10 (P := fun _ => EvmInv s0) epsA_stack_pop_le_g10 (fun _ _ _ hp => hp) ?_
  refine HandlerRunA.decCall_carry_g10 (P := fun _ => EvmInv s0) epsA_to_address_masked (fun _ _ _ hp => hp) ?_
  refine HandlerRunA.decCall_carry_g10 (P := fun _ => EvmInv s0) epsA_stack_pop_le_g10 (fun _ _ _ hp => hp) ?_
  refine HandlerRunA.decCall_carry_g10 (P := fun _ => EvmInv s0) epsA_stack_pop_le_g10 (fun _ _ _ hp => hp) ?_
  refine HandlerRunA.decCall_carry_g10 (P := fun _ => EvmInv s0) epsA_stack_pop_le_g10 (fun _ _ _ hp => hp) ?_
  refine HandlerRunA.decCall_carry_g10 (P := fun _ => EvmInv s0) epsA_stack_pop_le_g10 (fun _ _ _ hp => hp) ?_
  refine HandlerRunA.decCall_carry_g10 (P := fun _ => EvmInv s0) epsA_stack_pop_le_g10 (fun _ _ _ hp => hp) ?_
  refine HandlerRunA.dec_carry_g10 (P := fun _ => EvmInv s0) (fun _ _ hp => hp) ?_
  refine HandlerRunA.dec_carry_g10 (P := fun _ => EvmInv s0) (fun _ _ hp => hp) ?_
  refine HandlerRunA.decCall (Q := fun t => scXQ t ∧ EvmInv s0) epsA_extend_memory_cost2
    (hentry := fun t values body' callee ret' _ _ _ _ _ _ => trivial) ?_ hcont
  · intro t values body callee rs v cpost _ _ hp _ _ _ _ _ hQc
    obtain ⟨hlf, cw, ebw, hv, hbd⟩ := hQc
    refine ⟨⟨cw, ebw, ?_, ?_⟩, hp⟩
    · dsimp only [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      first | rw [if_pos rfl, hv] | simp [hv]
    · rw [hlf]
      exact hbd

/-- The `vz` `decCall` (node 16). -/
theorem op_callcode_vzChain_g10 {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {charged : Bool} {cont : ProgHOL 64}
    (hcont : HandlerRunA s0
      (fun s => scXQ s ∧ EvmInv s0 ∧ AcQ_g10 s ∧ CcVzQ_g10 s) charged cont) :
    HandlerRunA s0 (fun s => scXQ s ∧ EvmInv s0 ∧ AcQ_g10 s) charged
      (.decCall (ofString "vz") .one (ofString "u256_is_zero")
        [.var .local (ofString "value")] cont) := by
  apply HandlerRunA.decCall
    (Q := fun s => scXQ s ∧ EvmInv s0 ∧ AcQ_g10 s ∧ CcVzQ_g10 s)
    Group10.epsA_u256_is_zero_sem_g10
    (hentry := fun t values body' callee ret' _ _ _ _ _ _ => trivial)
  · intro t values body callee rs v cpost _ _ hp hargs hlk _ _ _ hQc
    obtain ⟨hlf, z, hvz, hz01, hor⟩ := hQc
    obtain ⟨v0, hv0_ev, hvals⟩ : ∃ v0,
        @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
          (.var .local (ofString "value")) = some v0 ∧ values = [v0] := by
      rw [evalListHOLFinite_eq_toExact] at hargs
      simp only [evalListHOLExact] at hargs
      rcases he : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
          (.var .local (ofString "value")) with _ | v0
      · simp [he] at hargs
      · simp only [he, Option.some.injEq] at hargs; exact ⟨v0, rfl, hargs.symm⟩
    subst hvals
    obtain ⟨q0, q1, q2, q3, hv0_struct, ha_pin⟩ := u256_is_zero_args_lookup_g10 hlk
    have hval_pin : t.locals.lookup (ofString "value") =
        some (.rStruct [.val (.word q0), .val (.word q1), .val (.word q2), .val (.word q3)]) := by
      rw [← hv0_struct]
      exact hv0_ev
    refine ⟨scXQ_setvar_g10 (by decide) (scXQ_of_locFrame_call_g10 hp.1 hlf), hp.2.1, hp.2.2, ?_⟩
    refine ⟨q0, q1, q2, q3, z, hval_pin, ?_, hz01, hor q0 q1 q2 q3 ha_pin⟩
    dsimp only [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    first | rw [if_pos rfl, hvz] | simp [hvz]
  · exact hcont

/-- The `transfer_cost` `dec` and the `vz == 0` ite (nodes 17). -/
theorem op_callcode_tcChain_g10 {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {charged : Bool} {cont : ProgHOL 64}
    (hcont : HandlerRunA s0
      (fun s => scXQ s ∧ EvmInv s0 ∧ AcQ_g10 s ∧ CcTcQ_g10 s) charged cont) :
    HandlerRunA s0
      (fun s => scXQ s ∧ EvmInv s0 ∧ AcQ_g10 s ∧ CcVzQ_g10 s) charged
      (.dec (ofString "transfer_cost") .one (.const (BitVec.ofNat 64 0))
        (.seq (.ite (.cmp .equal (.var .local (ofString "vz")) (.const (BitVec.ofNat 64 0)))
            (.assign .local (ofString "transfer_cost") (.const (BitVec.ofNat 64 11300))) .skip)
          cont)) := by
  apply HandlerRunA.dec (Q := fun s => scXQ s ∧ EvmInv s0 ∧ AcQ_g10 s ∧ CcVzQ_g10 s ∧
      ∃ tcw : BitVec 64, s.locals.lookup (ofString "transfer_cost") = some (.val (.word tcw)) ∧
        tcw = 0#64)
    (hinit := fun t v hv _ hp => by
      have hvw : v = .val (.word (BitVec.ofNat 64 0)) := eval_const_word_g10 _ v hv
      subst hvw
      obtain ⟨hsc, hinv, hac, hccvz⟩ := hp
      obtain ⟨acw', hla', hacd⟩ := hac
      obtain ⟨q0, q1, q2, q3, vz, hvp, hvzp, h01, hor⟩ := hccvz
      have hvps : (setVarHOLFinite (ofString "transfer_cost") (.val (.word 0#64)) t).locals.lookup
          (ofString "value") =
          some (.rStruct [.val (.word q0), .val (.word q1), .val (.word q2),
            .val (.word q3)]) := by
        simp only [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        rw [if_neg (by decide)]
        exact hvp
      have hvzps : (setVarHOLFinite (ofString "transfer_cost") (.val (.word 0#64)) t).locals.lookup
          (ofString "vz") = some (.val (.word vz)) := by
        simp only [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        rw [if_neg (by decide)]
        exact hvzp
      have htps : (setVarHOLFinite (ofString "transfer_cost") (.val (.word 0#64)) t).locals.lookup
          (ofString "transfer_cost") = some (.val (.word 0#64)) := by
        simp only [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        first | rw [if_pos (by simp)] | simp
      refine ⟨scXQ_setvar_g10 (by decide) hsc, hinv, ⟨acw', ?_, hacd⟩,
        ⟨q0, q1, q2, q3, vz, hvps, hvzps, h01, hor⟩, ⟨0#64, htps, rfl⟩⟩
      simp only [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      rw [if_neg (by decide)]
      exact hla')
  apply HandlerRunA.seq_ite_vz_g10
    (P := fun s => scXQ s ∧ EvmInv s0 ∧ AcQ_g10 s ∧ CcVzQ_g10 s ∧
      ∃ tcw : BitVec 64, s.locals.lookup (ofString "transfer_cost") = some (.val (.word tcw)) ∧
        tcw = 0#64)
    (hpin := fun t hp => by
      obtain ⟨_, _, _, hccvz, _⟩ := hp
      obtain ⟨_, _, _, _, vz, _, hvzp, h01, _⟩ := hccvz
      exact ⟨vz, hvzp, h01⟩)
  · exact HandlerRunA.seq_assign_local
      (Q := fun s => scXQ s ∧ EvmInv s0 ∧ AcQ_g10 s ∧ CcTcQ_g10 s) hcont
      (hasgn := fun t v hv _ hp => by
        have hvw : v = .val (.word (BitVec.ofNat 64 11300)) := eval_const_word_g10 _ v hv
        subst hvw
        obtain ⟨⟨hsc, hinv, hac, hccvz, _⟩, vz, hvzp, hvz0⟩ := hp
        obtain ⟨q0, q1, q2, q3, _, hvp, _, h01, hor⟩ := hccvz
        obtain ⟨acw', hla', hacd⟩ := hac
        have hvps : (setKvarHOLFinite .local (ofString "transfer_cost")
            (.val (.word 11300#64)) t).locals.lookup (ofString "value") =
            some (.rStruct [.val (.word q0), .val (.word q1), .val (.word q2),
              .val (.word q3)]) := by
          simp only [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          rw [if_neg (by decide)]
          exact hvp
        have hvzps : (setKvarHOLFinite .local (ofString "transfer_cost")
            (.val (.word 11300#64)) t).locals.lookup (ofString "vz") = some (.val (.word vz)) := by
          simp only [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          rw [if_neg (by decide)]
          exact hvzp
        have htcps : (setKvarHOLFinite .local (ofString "transfer_cost")
            (.val (.word 11300#64)) t).locals.lookup (ofString "transfer_cost") =
            some (.val (.word 11300#64)) := by
          simp only [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          first | rw [if_pos (by simp)] | simp
        refine ⟨scXQ_setvar_g10 (by decide) hsc, hinv, ⟨acw', ?_, hacd⟩,
          ⟨q0, q1, q2, q3, vz, 11300#64, hvps, hvzps, htcps, Or.inl ⟨hvz0, rfl⟩⟩⟩
        simp only [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        rw [if_neg (by decide)]
        exact hla')
  · have himp : ∀ t : PanSemStateFiniteExact 64 F, EvmInv t →
      ((scXQ t ∧ EvmInv s0 ∧ AcQ_g10 t ∧ CcVzQ_g10 t ∧
        ∃ tcw, t.locals.lookup (ofString "transfer_cost") = some (.val (.word tcw)) ∧
          tcw = 0#64) ∧
        ∃ vz, t.locals.lookup (ofString "vz") = some (.val (.word vz)) ∧ vz = 1#64) →
      (scXQ t ∧ EvmInv s0 ∧ AcQ_g10 t ∧ CcTcQ_g10 t) := by
      intro t _ hp
      obtain ⟨tcw0, htcp0, htc0v⟩ := hp.1.2.2.2.2
      obtain ⟨⟨hsc, hinv, hac, hccvz, _⟩, vz, hvzp, hvz1⟩ := hp
      obtain ⟨q0, q1, q2, q3, vz0, hvp, hvzp0, h01, hor⟩ := hccvz
      have hvz01 : vz0 = 1#64 := by
        have he := hvzp.symm.trans hvzp0
        injection he with c1
        injection c1 with c2
        injection c2 with c3
        exact c3 ▸ hvz1
      exact ⟨hsc, hinv, hac, ⟨q0, q1, q2, q3, vz0, tcw0, hvp, hvzp0, htcp0,
        Or.inr ⟨hvz01, htc0v, hor hvz01⟩⟩⟩
    exact HandlerRunA.seq_skip (HandlerRunA.weaken himp hcont)

/-- The `need` `decCall` and the `charge_gas` call (nodes 18-19). -/
theorem op_callcode_needChain_g10 {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {cont : ProgHOL 64}
    (hcont : HandlerRunA s0 (fun t => CcPQ_g10 s0 t) true cont) :
    HandlerRunA s0
      (fun s => scXQ s ∧ EvmInv s0 ∧ AcQ_g10 s ∧ CcTcQ_g10 s) false
      (.decCall (ofString "need") .one (ofString "add_sat")
        [.op .add [.var .local (ofString "access_cost"),
          .var .local (ofString "transfer_cost")],
         .rfield 0 (.var .local (ofString "x"))]
        (.seq (.call (some (none, none)) (ofString "charge_gas") [.var .local (ofString "need")])
          cont)) := by
  apply HandlerRunA.decCall
    (Q := fun s => scXQ s ∧ EvmInv s0 ∧ AcQ_g10 s ∧ CcTcQ_g10 s ∧ CcNdQ_g10 s)
    epsA_add_sat_ge_g10
    (hentry := fun t values body' callee ret' _ _ _ _ _ _ => trivial)
  · intro t values body callee rs v cpost _ _ hp hargs hlk _ _ _ hQc
    obtain ⟨hlf, aw, rww, hvw, hle⟩ := hQc
    obtain ⟨hsc, hinv, hac, htc⟩ := hp
    obtain ⟨acw, hl_ac, hacd⟩ := hac
    obtain ⟨q0, q1, q2, q3, vz, tcw, hvp, hvzp, htcp, hcorr⟩ := htc
    obtain ⟨v0, v1, hv0_ev, hv1_ev, hvals⟩ : ∃ v0 v1,
        @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
          (.op .add [.var .local (ofString "access_cost"),
            .var .local (ofString "transfer_cost")]) = some v0 ∧
        @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
          (.rfield 0 (.var .local (ofString "x"))) = some v1 ∧
        values = [v0, v1] := by
      rw [evalListHOLFinite_eq_toExact] at hargs
      simp only [evalListHOLExact] at hargs
      rcases he0 : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
          (.op .add [.var .local (ofString "access_cost"),
            .var .local (ofString "transfer_cost")]) with _ | v0
      · simp [he0] at hargs
      rcases he1 : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
          (.rfield 0 (.var .local (ofString "x"))) with _ | v1
      · simp [he0, he1] at hargs
      simp only [he0, he1, Option.some.injEq] at hargs
      exact ⟨v0, v1, rfl, rfl, hargs.symm⟩
    subst hvals
    obtain ⟨w0, w1, hv0w, hv1w, hla0, _⟩ := add_sat_args_lookup_g10 hlk
    have h3 : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
        (.op .add [.var .local (ofString "access_cost"),
          .var .local (ofString "transfer_cost")]) =
        some (.val (.word (acw + tcw))) := by
      simp [evalHOLExact, evalListHOLExact, hl_ac, htcp, wordOpHOL, wordOp, valueIsWord, valueWord]
    rw [h3] at hv0_ev
    have hsum : acw + tcw = w0 := by
      have he : (.val (.word (acw + tcw)) : ValueHOL 64) = .val (.word w0) :=
        (Option.some.inj hv0_ev).trans hv0w
      injection he with i1
      injection i1 with i2
    have hla' : callee.lookup (ofString "a") = some (.val (.word aw)) := hvw
    have haw : aw = w0 := by
      have he := hla'.symm.trans hla0
      injection he with j1
      injection j1 with j2
      injection j2 with j3
    have hle_nat : (acw + tcw).toNat ≤ rww.toNat := by
      have h4 : aw.toNat ≤ rww.toNat := hle.2
      rw [haw, ← hsum] at h4
      exact h4
    have hac100 : 100 ≤ acw.toNat := by rcases hacd with rfl | rfl <;> simp
    have hac3000 : acw.toNat ≤ 3000 := by rcases hacd with rfl | rfl <;> simp
    have htc_bound : tcw.toNat = 11300 ∨ tcw.toNat = 0 := by
      rcases hcorr with ⟨hvz0, htc11300⟩ | ⟨hvz1, htc0, hor0⟩
      · exact Or.inl (by rw [htc11300]; rfl)
      · exact Or.inr (by rw [htc0]; rfl)
    have hmod : (acw + tcw).toNat = acw.toNat + tcw.toNat := by
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
    have hbound : acw.toNat + tcw.toNat ≤ rww.toNat := by rw [← hmod]; exact hle_nat
    refine ⟨scXQ_setvar_g10 (by decide) (scXQ_of_locFrame_call_g10 hsc hlf), hinv,
      ⟨acw, ?_, hacd⟩, ?_, ?_⟩
    · simp only [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      rw [if_neg (by decide)]
      exact hl_ac
    · refine ⟨q0, q1, q2, q3, vz, tcw, ?_, ?_, ?_, hcorr⟩
      · simp only [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        rw [if_neg (by decide)]
        exact hvp
      · simp only [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        rw [if_neg (by decide)]
        exact hvzp
      · simp only [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        rw [if_neg (by decide)]
        exact htcp
    · refine ⟨rww, acw, tcw, ?_, ?_, ?_, hbound⟩
      · simp only [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        rw [if_neg (by decide)]
        exact hl_ac
      · simp only [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        rw [if_neg (by decide)]
        exact htcp
      · dsimp only [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        first | rw [if_pos rfl, hle.1] | simp [hle.1]
  apply HandlerRunA.seq_charge_gas_acc_g10 (Q := fun t => CcPQ_g10 s0 t)
    (hpos := fun t w hv _ _ hp => by
      obtain ⟨nw, acw, tcw, hla, hlt, hln, hbound⟩ := hp.2.2.2.2
      obtain ⟨acw', hla', hacd⟩ := hp.2.2.1
      have hacweq : acw = acw' := by
        have he := hla'.symm.trans hla
        injection he with c1
        injection c1 with c2
        injection c2 with c3
        exact c3.symm
      subst hacweq
      have hac100 : 100 ≤ acw.toNat := by rcases hacd with rfl | rfl <;> simp
      have hev : t.locals.lookup (ofString "need") = some (.val (.word w)) := hv
      rw [hln] at hev
      injection hev with k1
      injection k1 with k2
      injection k2 with k3
      subst k3
      exact Or.inr (by omega))
    (hstep := fun t cpost amtw hv0_ev hi hw hp hR_le hi_cp hw_cp hglob_cp hm32_cp hch_cp hR_cp => by
      obtain ⟨hsc, hinv, hac, htc, hnd⟩ := hp
      obtain ⟨acw', hla', hacd⟩ := hac
      obtain ⟨nw, acw, tcw, hla, hlt, hln, hbound⟩ := hnd
      have hacweq : acw = acw' := by
        have he := hla'.symm.trans hla
        injection he with c1
        injection c1 with c2
        injection c2 with c3
        exact c3.symm
      subst hacweq
      obtain ⟨q0, q1, q2, q3, vz, tcw0, hvp, hvzp, htcp0, hcorr⟩ := htc
      have htcweq : tcw = tcw0 := by
        have he := hlt.symm.trans htcp0
        injection he with u1
        injection u1 with u2
        injection u2 with u3
      subst htcweq
      obtain ⟨cw, ebw, hxl, hbd⟩ := hsc
      have hamtw : amtw = nw := by
        have hev : t.locals.lookup (ofString "need") = some (.val (.word amtw)) := hv0_ev
        rw [hln] at hev
        injection hev with k1
        injection k1 with k2
        injection k2 with k3
        exact k3.symm
      have hamtwN : amtw.toNat = nw.toNat := by rw [hamtw]
      have hscu : scXQ { cpost with locals := t.locals } :=
        scXQ_of_pins_g10 ⟨cw, ebw, hxl, hbd⟩ hm32_cp
      obtain ⟨cw', ebw', hxlu, hbdu⟩ := hscu
      have hRu : evmR { cpost with locals := t.locals } = evmR cpost :=
        (evm_congr (s := cpost) (t := { cpost with locals := t.locals }) rfl rfl).2.1
      have hac100 : 100 ≤ acw.toNat := by rcases hacd with rfl | rfl <;> simp
      rcases hcorr with ⟨hvz0, htc11300⟩ | ⟨hvz1, htc0, hor0⟩
      · have htcN : tcw.toNat = 11300 := by rw [htc11300]; rfl
        have hcred' : evmR cpost + 2300 + 1 ≤ evmR s0 := by omega
        have hcredu : evmR { cpost with locals := t.locals } + 2300 + 1 ≤ evmR s0 := by
          rw [hRu]; exact hcred'
        exact ⟨q0, q1, q2, q3, vz, tcw, acw, cw', ebw', 2300, hvp, hvzp, htcp0, hla, hacd, hxlu,
          hbdu, Or.inl ⟨hvz0, htc11300, rfl⟩, hcredu, hinv⟩
      · have hcred' : evmR cpost + 0 + 1 ≤ evmR s0 := by omega
        have hcredu : evmR { cpost with locals := t.locals } + 0 + 1 ≤ evmR s0 := by
          rw [hRu]; exact hcred'
        exact ⟨q0, q1, q2, q3, vz, tcw, acw, cw', ebw', 0, hvp, hvzp, htcp0, hla, hacd, hxlu,
          hbdu, Or.inr ⟨hvz1, htc0, hor0, rfl⟩, hcredu, hinv⟩)
    (hcont := hcont)

/-- The `op_callcode` cost chain (nodes 12-19). -/
theorem op_callcode_costChain_g10 {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {cont : ProgHOL 64}
    (hcont : HandlerRunA s0 (fun t => CcPQ_g10 s0 t) true cont) :
    HandlerRunA s0 (fun t => scXQ t ∧ EvmInv s0) false
      (.decCall (ofString "warm") .one (ofString "is_warm_address")
        [.var .local (ofString "code_address0")]
        (.dec (ofString "access_cost") .one (.const (BitVec.ofNat 64 100))
          (.seq (.ite (.cmp .equal (.var .local (ofString "warm")) (.const (BitVec.ofNat 64 0)))
              (.assign .local (ofString "access_cost") (.const (BitVec.ofNat 64 3000))) .skip)
            (.decCall (ofString "vz") .one (ofString "u256_is_zero")
              [.var .local (ofString "value")]
              (.dec (ofString "transfer_cost") .one (.const (BitVec.ofNat 64 0))
                (.seq (.ite (.cmp .equal (.var .local (ofString "vz")) (.const (BitVec.ofNat 64 0)))
                    (.assign .local (ofString "transfer_cost") (.const (BitVec.ofNat 64 11300)))
                    .skip)
                  (.decCall (ofString "need") .one (ofString "add_sat")
                    [.op .add [.var .local (ofString "access_cost"),
                      .var .local (ofString "transfer_cost")],
                     .rfield 0 (.var .local (ofString "x"))]
                    (.seq (.call (some (none, none)) (ofString "charge_gas")
                      [.var .local (ofString "need")]) cont)))))))) := by
  apply HandlerRunA.decCall (Q := fun t => scXQ t ∧ EvmInv s0) epsA_is_warm_address
    (hentry := fun t values body' callee ret' _ _ _ _ _ _ => trivial)
  · intro t values body callee rs v cpost _ _ hp _ _ _ _ _ hQc
    exact ⟨scXQ_setvar_g10 (by decide) (scXQ_of_locFrame_call_g10 hp.1 hQc), hp.2⟩
  apply HandlerRunA.dec (Q := fun s => scXQ s ∧ EvmInv s0 ∧ AcQ_g10 s)
    (hinit := fun t v hv _ hp => by
      have hvw : v = .val (.word (BitVec.ofNat 64 100)) := eval_const_word_g10 _ v hv
      subst hvw
      refine ⟨scXQ_setvar_g10 (by decide) hp.1, hp.2, (BitVec.ofNat 64 100), ?_, Or.inl rfl⟩
      dsimp only [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      first | rw [if_pos rfl] | simp)
  apply HandlerRunA.seq_ite_unit
  · intro t w _ _
    apply HandlerRunA.seq_assign_local (Q := fun s => scXQ s ∧ EvmInv s0 ∧ AcQ_g10 s)
      (hasgn := fun t v hv _ hp => by
        have hvw : v = .val (.word (BitVec.ofNat 64 3000)) := eval_const_word_g10 _ v hv
        subst hvw
        refine ⟨scXQ_setvar_g10 (by decide) hp.1, hp.2.1, (BitVec.ofNat 64 3000), ?_, Or.inr rfl⟩
        dsimp only [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        first | rw [if_pos rfl] | simp)
    exact op_callcode_vzChain_g10
      (op_callcode_tcChain_g10 (op_callcode_needChain_g10 hcont))
  · intro t _
    exact HandlerRunA.seq_skip
      (op_callcode_vzChain_g10 (op_callcode_tcChain_g10 (op_callcode_needChain_g10 hcont)))

/-- The `op_callcode` prefix (nodes 1-19). -/
theorem op_callcode_prefix_g10 {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {cont : ProgHOL 64}
    (hcont : HandlerRunA s0 (fun t => CcPQ_g10 s0 t) true cont) :
    HandlerRunA s0 (fun _ => EvmInv s0) false
      (.decCall (ofString "gasv") (.comb [.one, .one, .one, .one]) (ofString "stack_pop") []
        (.decCall (ofString "cav") (.comb [.one, .one, .one, .one]) (ofString "stack_pop") []
          (.decCall (ofString "code_address0") .one (ofString "to_address_masked")
            [.var .local (ofString "cav")]
            (.decCall (ofString "value") (.comb [.one, .one, .one, .one]) (ofString "stack_pop") []
              (.decCall (ofString "in_start") (.comb [.one, .one, .one, .one]) (ofString "stack_pop") []
                (.decCall (ofString "in_size") (.comb [.one, .one, .one, .one]) (ofString "stack_pop") []
                  (.decCall (ofString "out_start") (.comb [.one, .one, .one, .one]) (ofString "stack_pop") []
                    (.decCall (ofString "out_size") (.comb [.one, .one, .one, .one]) (ofString "stack_pop") []
                      (.dec (ofString "msg") .one
                        (.load .one (.op .add [.var .global (ofString "ev"),
                          .const (BitVec.ofNat 64 112)]))
                        (.dec (ofString "to") .one
                          (.load .one (.op .add [.var .local (ofString "msg"),
                            .const (BitVec.ofNat 64 32)]))
                          (.decCall (ofString "x") (.comb [.one, .one]) (ofString "extend_memory_cost2")
                            [.var .local (ofString "in_start"), .var .local (ofString "in_size"),
                             .var .local (ofString "out_start"), .var .local (ofString "out_size")]
                            (.decCall (ofString "warm") .one (ofString "is_warm_address")
                              [.var .local (ofString "code_address0")]
                              (.dec (ofString "access_cost") .one (.const (BitVec.ofNat 64 100))
                                (.seq (.ite (.cmp .equal (.var .local (ofString "warm"))
                                    (.const (BitVec.ofNat 64 0)))
                                    (.assign .local (ofString "access_cost")
                                      (.const (BitVec.ofNat 64 3000))) .skip)
                                  (.decCall (ofString "vz") .one (ofString "u256_is_zero")
                                    [.var .local (ofString "value")]
                                    (.dec (ofString "transfer_cost") .one (.const (BitVec.ofNat 64 0))
                                      (.seq (.ite (.cmp .equal (.var .local (ofString "vz"))
                                          (.const (BitVec.ofNat 64 0)))
                                          (.assign .local (ofString "transfer_cost")
                                            (.const (BitVec.ofNat 64 11300))) .skip)
                                        (.decCall (ofString "need") .one (ofString "add_sat")
                                          [.op .add [.var .local (ofString "access_cost"),
                                            .var .local (ofString "transfer_cost")],
                                           .rfield 0 (.var .local (ofString "x"))]
                                          (.seq (.call (some (none, none)) (ofString "charge_gas")
                                            [.var .local (ofString "need")]) cont))))))))))))))))))) := by
  exact op_callcode_pops_g10 (op_callcode_costChain_g10 hcont)

/-! ## Stage C: the `op_callcode` insufficient-gas tail

The `insufficient != 0` branch consumes the gas credit: the YES branch
restores the regular-gas word `ev+64` (a store that can RAISE `evmR`), and the
NO branch runs `generic_call`.  Both branches are gated by
`HandlerRunA.seq_ite_branch` at a credit predicate, so the shared continuation
(the `started` test and the final `return`) runs at the weak predicate
`fun _ => EvmInv s0`.  Feeding that continuation through the branch-local
`dec`/`decCall` scopes requires two evaluation-level swap lemmas, whose
continuation-safety is discharged by a no-read property of the shared
continuation. -/

/-! ### Same-but-locals state agreement -/

/-- Two states agreeing on every field except `locals` (clock included). -/
def SameButLocalsClock_g10 {F : Type} (s1 s2 : PanSemStateFiniteExact 64 F) : Prop :=
  s1.globals = s2.globals ∧ s1.structs = s2.structs ∧ s1.code = s2.code ∧
    s1.eshapes = s2.eshapes ∧ s1.memory = s2.memory ∧ s1.memaddrs = s2.memaddrs ∧
    s1.shMemaddrs = s2.shMemaddrs ∧ s1.clock = s2.clock ∧ s1.be = s2.be ∧
    s1.ffi = s2.ffi ∧ s1.baseAddr = s2.baseAddr ∧ s1.topAddr = s2.topAddr

theorem SameButLocalsClock_g10_refl {F : Type} (s : PanSemStateFiniteExact 64 F) :
    SameButLocalsClock_g10 s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem sameButLocalsClock_update_g10 {F : Type} {s1 s2 : PanSemStateFiniteExact 64 F}
    (h : SameButLocalsClock_g10 s1 s2) (L1 L2 : HolFiniteMapExact MlS (ValueHOL 64)) :
    SameButLocalsClock_g10 {s1 with locals := L1} {s2 with locals := L2} := by
  obtain ⟨hg, hst, hcd, hesh, hmem, hma, hsma, hck, hbe, hffi, hba, hta⟩ := h
  exact ⟨hg, hst, hcd, hesh, hmem, hma, hsma, hck, hbe, hffi, hba, hta⟩

/-- The record-equality shape consumed by `opDispatchPostA_congr_lc`. -/
theorem state_eq_lc_of_same_g10 {F : Type} {u v : PanSemStateFiniteExact 64 F}
    (h : SameButLocalsClock_g10 u v) :
    u = { v with locals := u.locals, clock := u.clock } := by
  obtain ⟨hg, hst, hcd, hesh, hmem, hma, hsma, hck, hbe, hffi, hba, hta⟩ := h
  cases u; cases v; simp_all

theorem callEntry_eq_of_sameButLocals_g10 {F : Type}
    {s1 s2 : PanSemStateFiniteExact 64 F}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} (h : SameButLocalsClock_g10 s1 s2) :
    callEntryStateHOLFinite s1 callee = callEntryStateHOLFinite s2 callee := by
  obtain ⟨hg, hst, hcd, hesh, hmem, hma, hsma, hck, hbe, hffi, hba, hta⟩ := h
  unfold callEntryStateHOLFinite
  cases s1; cases s2; simp_all

/-! ### Continuation no-read -/

/-- A continuation whose evaluation is insensitive to one local slot: the two
evaluations agree in result and in every state field except `locals`. -/
def ContNoread_g10 {F : Type} (nm : MlS) (cont : ProgHOL 64) : Prop :=
  ∀ (s1 s2 : PanSemStateFiniteExact 64 F),
    SameButLocalsClock_g10 s1 s2 →
    (∀ k, k ≠ nm → s1.locals.lookup k = s2.locals.lookup k) →
    (evaluateHOLFiniteState s1 cont).1 = (evaluateHOLFiniteState s2 cont).1 ∧
    SameButLocalsClock_g10 (evaluateHOLFiniteState s1 cont).2
      (evaluateHOLFiniteState s2 cont).2

/-- Constant-argument lists evaluate state-independently. -/
theorem evalListHOLFinite_const_g10 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (c : BitVec 64) :
    evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [.const c] =
      some [.val (.word c)] := by
  simp [evalListHOLFinite, evalListHOLExact, evalHOLExact]

/-- A plain call (no assignment, no handler) is insensitive to the caller's
locals: results agree and output states agree off `locals`. -/
theorem eval_call_congr_g10 {F : Type} {fnm : MlS} {args : List (ExpHOL 64)}
    {s1 s2 : PanSemStateFiniteExact 64 F}
    (hsame : SameButLocalsClock_g10 s1 s2)
    (hargs : evalListHOLFinite s1 (h := fun a => Classical.propDecidable (s1.memaddrs a)) args =
      evalListHOLFinite s2 (h := fun a => Classical.propDecidable (s2.memaddrs a)) args) :
    (evaluateHOLFiniteState s1 (.call (some (none, none)) fnm args)).1 =
      (evaluateHOLFiniteState s2 (.call (some (none, none)) fnm args)).1 ∧
    SameButLocalsClock_g10 (evaluateHOLFiniteState s1 (.call (some (none, none)) fnm args)).2
      (evaluateHOLFiniteState s2 (.call (some (none, none)) fnm args)).2 := by
  classical
  obtain ⟨hg, hst, hcd, hesh, hmem, hma, hsma, hck, hbe, hffi, hba, hta⟩ := id hsame
  rw [evaluateHOLFiniteState_call s1 (some (none, none)) fnm args,
    evaluateHOLFiniteState_call s2 (some (none, none)) fnm args]
  rw [← hargs]
  rcases he1 : evalListHOLFinite s1 (h := fun a => Classical.propDecidable (s1.memaddrs a)) args
    with _ | values
  · simp only [he1]
    exact ⟨trivial, hsame⟩
  · simp only [he1] at hargs ⊢
    rw [hcd]
    rcases hl : lookupCodeHOLFinite s2.code.lookup fnm values with _ | ⟨body, callee, rs⟩
    · simp only [hl]
      exact ⟨trivial, hsame⟩
    · simp only [hl] at hargs ⊢
      rw [hck]
      by_cases hz : s2.clock = 0
      · simp only [if_pos hz]
        exact ⟨trivial, sameButLocalsClock_update_g10 hsame _ _⟩
      · simp only [hz, ↓reduceIte] at hargs ⊢
        rw [callEntry_eq_of_sameButLocals_g10 hsame]
        rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s2 callee) body
          with ⟨rB, stB⟩
        cases rB with
        | none => exact ⟨rfl, SameButLocalsClock_g10_refl _⟩
        | some r =>
          cases r with
          | «break» => exact ⟨by simp, SameButLocalsClock_g10_refl _⟩
          | «continue» => exact ⟨by simp, SameButLocalsClock_g10_refl _⟩
          | returned v =>
            by_cases hsh : shapeEqHOL (shapeOfHOLExact v) rs = true
            · simp only [hsh, ↓reduceIte]
              exact ⟨trivial, sameButLocalsClock_update_g10 (SameButLocalsClock_g10_refl _) _ _⟩
            · simp only [hsh, ↓reduceIte]
              exact ⟨rfl, SameButLocalsClock_g10_refl _⟩
          | exception id v =>
            simp only
            exact ⟨by simp, sameButLocalsClock_update_g10 (SameButLocalsClock_g10_refl _) _ _⟩
          | error =>
            simp only
            exact ⟨by simp, sameButLocalsClock_update_g10 (SameButLocalsClock_g10_refl _) _ _⟩
          | timeOut =>
            simp only
            exact ⟨by simp, sameButLocalsClock_update_g10 (SameButLocalsClock_g10_refl _) _ _⟩
          | finalFfi ev =>
            simp only
            exact ⟨by simp, sameButLocalsClock_update_g10 (SameButLocalsClock_g10_refl _) _ _⟩

/-! ### Stage C, chunk 2: the `op_callcode` terminal continuation -/

/-- Restoring one local slot leaves every other slot untouched. -/
theorem resVarEq_lookup_ne_g10 {m : HolFiniteMapExact MlS (ValueHOL 64)}
    {nm : MlS} {old : Option (ValueHOL 64)} {k : MlS} (hk : k ≠ nm) :
    (HolFiniteMapExact.resVarEq m (nm, old)).lookup k = m.lookup k := by
  cases old with
  | none =>
    have h := congrFun (lookup_resVarEq_toExact m (nm, none)) k
    simp only [h, resVarHOLExact]
    exact if_neg hk
  | some v =>
    have h := congrFun (lookup_resVarEq_toExact m (nm, some v)) k
    simp only [h, resVarHOLExact]
    exact if_neg hk

/-- Returning a constant is insensitive to everything except `locals`. -/
theorem eval_return_const_congr_g10 {F : Type} (c : BitVec 64)
    {s1 s2 : PanSemStateFiniteExact 64 F} (hsame : SameButLocalsClock_g10 s1 s2) :
    (evaluateHOLFiniteState s1 (.return (.const c))).1 =
      (evaluateHOLFiniteState s2 (.return (.const c))).1 ∧
    SameButLocalsClock_g10 (evaluateHOLFiniteState s1 (.return (.const c))).2
      (evaluateHOLFiniteState s2 (.return (.const c))).2 := by
  classical
  obtain ⟨hg, hst, hcd, hesh, hmem, hma, hsma, hck, hbe, hffi, hba, hta⟩ := id hsame
  have hc1 : @evalHOLExact 64 F _ s1.toExact
      (fun a => Classical.propDecidable (s1.memaddrs a)) (.const c) = some (.val (.word c)) := by
    simp [evalHOLExact]
  have hc2 : @evalHOLExact 64 F _ s2.toExact
      (fun a => Classical.propDecidable (s2.memaddrs a)) (.const c) = some (.val (.word c)) := by
    simp [evalHOLExact]
  rw [evaluateHOLFiniteState_return s1 (.const c),
      evaluateHOLFiniteState_return s2 (.const c)]
  simp only [hc1, hc2, hst]
  by_cases hsz : sizeOfShapeWithContextHOL s2.structs (shapeOfHOLExact (.val (.word c))) ≤ 32
  · simp only [if_pos hsz]
    exact ⟨trivial, sameButLocalsClock_update_g10 hsame _ _⟩
  · simp only [if_neg hsz]
    exact ⟨trivial, hsame⟩

/-- The terminal continuation of `op_callcode`'s tail: the `started` re-check,
`pc_add` when the call already started, then `return 0`. -/
def callcodeContProg_g10 : ProgHOL 64 :=
  .seq
    (.ite (.cmp .equal (.var .local (ofString "started")) (.const (BitVec.ofNat 64 0)))
      (.call (some (none, none)) (ofString "pc_add") [.const (BitVec.ofNat 64 1)])
      .skip)
    (.return (.const (BitVec.ofNat 64 0)))

/-- The terminal continuation reads only the `started` local (in its guard); it
is insensitive to any other local slot. -/
theorem callcodeCont_noread_g10 {F : Type} {nm : MlS}
    (hnm : (ofString "started") ≠ nm) :
    ContNoread_g10 (F := F) nm callcodeContProg_g10 := by
  intro s1 s2 hsame hloc
  classical
  have hstart : s1.locals.lookup (ofString "started") =
      s2.locals.lookup (ofString "started") := hloc (ofString "started") hnm
  have hcond : @evalHOLExact 64 F _ s1.toExact
      (fun a => Classical.propDecidable (s1.memaddrs a))
      (.cmp .equal (.var .local (ofString "started")) (.const (BitVec.ofNat 64 0))) =
    @evalHOLExact 64 F _ s2.toExact
      (fun a => Classical.propDecidable (s2.memaddrs a))
      (.cmp .equal (.var .local (ofString "started")) (.const (BitVec.ofNat 64 0))) := by
    simp only [evalHOLExact, hstart]
  simp only [callcodeContProg_g10]
  rw [evaluateHOLFiniteState_seq_line780 (state := s1),
      evaluateHOLFiniteState_seq_line780 (state := s2)]
  rw [evaluateHOLFiniteState_ite (state := s1),
      evaluateHOLFiniteState_ite (state := s2)]
  rw [hcond]
  rcases hc2 : @evalHOLExact 64 F _ s2.toExact
      (fun a => Classical.propDecidable (s2.memaddrs a))
      (.cmp .equal (.var .local (ofString "started")) (.const (BitVec.ofNat 64 0))) with
    _ | v
  · simp only [hc2]
    exact ⟨trivial, hsame⟩
  · cases v with
    | val hw =>
      cases hw with
      | word w =>
        simp only [hc2, evaluateHOLFiniteState_skip]
        by_cases hw0 : w = 0
        · subst hw0
          simp only [↓reduceIte]
          exact eval_return_const_congr_g10 (BitVec.ofNat 64 0) hsame
        · simp only [hw0, ↓reduceIte]
          have hcc := eval_call_congr_g10 (fnm := ofString "pc_add")
            (args := [.const (BitVec.ofNat 64 1)]) hsame
            (by rw [evalListHOLFinite_const_g10 s1 (BitVec.ofNat 64 1),
              evalListHOLFinite_const_g10 s2 (BitVec.ofNat 64 1)])
          rcases hcp1 : evaluateHOLFiniteState s1
              (.call (some (none, none)) (ofString "pc_add")
                [.const (BitVec.ofNat 64 1)]) with ⟨rC, u1⟩
          rcases hcp2 : evaluateHOLFiniteState s2
              (.call (some (none, none)) (ofString "pc_add")
                [.const (BitVec.ofNat 64 1)]) with ⟨rC', u2⟩
          simp only [hcp1, hcp2] at hcc ⊢
          have hrC : rC = rC' := hcc.1
          subst hrC
          cases rC with
          | none => exact eval_return_const_congr_g10 (BitVec.ofNat 64 0) hcc.2
          | some r => exact ⟨rfl, hcc.2⟩
    | rStruct _ =>
      simp only [hc2]
      exact ⟨trivial, hsame⟩
    | nStruct _ _ =>
      simp only [hc2]
      exact ⟨trivial, hsame⟩

/-! ### Stage C, chunk 3: seq/dec and seq/decCall swaps -/

/-- Swapping a `dec` out of a `seq`: evaluating `.seq (.dec nm sh init body) cont`
agrees with evaluating `.dec nm sh init (.seq body cont)` whenever the
continuation does not read `nm`. -/
theorem seq_dec_swap_g10 {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {P : PanSemStateFiniteExact 64 F → Prop} {charged : Bool}
    {nm : MlS} {sh : ShapeHOL} {init : ExpHOL 64} {body cont : ProgHOL 64}
    (hnoread : ContNoread_g10 (F := F) nm cont)
    (h : HandlerRunA s0 P charged (.dec nm sh init (.seq body cont))) :
    HandlerRunA s0 P charged (.seq (.dec nm sh init body) cont) := by
  intro t hc hi hw hlen hR hp hnt
  classical
  have hkey : (evaluateHOLFiniteState t (.seq (.dec nm sh init body) cont)).1 =
      (evaluateHOLFiniteState t (.dec nm sh init (.seq body cont))).1 ∧
    (evaluateHOLFiniteState t (.seq (.dec nm sh init body) cont)).2 =
      { (evaluateHOLFiniteState t (.dec nm sh init (.seq body cont))).2 with
        locals := (evaluateHOLFiniteState t (.seq (.dec nm sh init body) cont)).2.locals,
        clock := (evaluateHOLFiniteState t (.seq (.dec nm sh init body) cont)).2.clock } := by
    simp only [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_dec_total]
    rcases hinit : @evalHOLExact 64 F _ t.toExact
        (fun a => Classical.propDecidable (t.memaddrs a)) init with _ | v
    · simp only [hinit]
      exact ⟨trivial, trivial⟩
    · simp only [hinit]
      by_cases hshape : shapeEqHOL sh (shapeOfHOLExact v) = true
      · simp only [hshape, ↓reduceIte]
        rcases hB : evaluateHOLFiniteState (setVarHOLFinite nm v t) body with ⟨rB, sB⟩
        simp only [hB]
        cases rB with
        | some _ => exact ⟨rfl, rfl⟩
        | none =>
          have hn := hnoread {sB with locals :=
              HolFiniteMapExact.resVarEq sB.locals (nm, t.locals.lookup nm)} sB
            (sameButLocalsClock_update_g10 (SameButLocalsClock_g10_refl sB) _ sB.locals)
            (fun k hk =>
              resVarEq_lookup_ne_g10 (m := sB.locals) (old := t.locals.lookup nm) hk)
          exact ⟨hn.1, state_eq_lc_of_same_g10 hn.2⟩
      · simp only [hshape, ↓reduceIte]
        exact ⟨rfl, rfl⟩
  have hsrc := h t hc hi hw hlen hR hp (by rw [← hkey.1]; exact hnt)
  rw [← hkey.1] at hsrc
  exact opDispatchPostA_congr_lc hkey.2 hsrc

/-- Swapping a `decCall` out of a `seq`: evaluating
`.seq (.decCall nm sh fnm args body) cont` agrees with evaluating
`.decCall nm sh fnm args (.seq body cont)` whenever the continuation does not
read `nm`. -/
theorem seq_decCall_swap_g10 {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {P : PanSemStateFiniteExact 64 F → Prop} {charged : Bool}
    {nm : MlS} {sh : ShapeHOL} {fnm : MlS} {args : List (ExpHOL 64)}
    {body cont : ProgHOL 64}
    (hnoread : ContNoread_g10 (F := F) nm cont)
    (h : HandlerRunA s0 P charged (.decCall nm sh fnm args (.seq body cont))) :
    HandlerRunA s0 P charged (.seq (.decCall nm sh fnm args body) cont) := by
  intro t hc hi hw hlen hR hp hnt
  classical
  have hkey : (evaluateHOLFiniteState t (.seq (.decCall nm sh fnm args body) cont)).1 =
      (evaluateHOLFiniteState t (.decCall nm sh fnm args (.seq body cont))).1 ∧
    (evaluateHOLFiniteState t (.seq (.decCall nm sh fnm args body) cont)).2 =
      { (evaluateHOLFiniteState t (.decCall nm sh fnm args (.seq body cont))).2 with
        locals := (evaluateHOLFiniteState t (.seq (.decCall nm sh fnm args body) cont)).2.locals,
        clock := (evaluateHOLFiniteState t (.seq (.decCall nm sh fnm args body) cont)).2.clock } := by
    simp only [evaluateHOLFiniteState_seq_line780,
      evaluateHOLFiniteState_decCall_fixClockRewrite]
    rcases hargs : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) args
      with _ | values
    · simp only [hargs]
      exact ⟨trivial, trivial⟩
    · simp only [hargs]
      rcases hl : lookupCodeHOLFinite t.code.lookup fnm values with _ | ⟨bodys, callee, rs⟩
      · simp only [hl]
        exact ⟨trivial, trivial⟩
      · simp only [hl]
        by_cases hz : t.clock = 0
        · simp only [if_pos hz]
          exact ⟨trivial, trivial⟩
        · simp only [hz, ↓reduceIte]
          rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite t callee) bodys
            with ⟨rB, sB⟩
          simp only [hb]
          cases rB with
          | none => exact ⟨rfl, rfl⟩
          | some r =>
            cases r with
            | «break» => exact ⟨rfl, rfl⟩
            | «continue» => exact ⟨rfl, rfl⟩
            | returned v =>
              by_cases hsh :
                (shapeEqHOL (shapeOfHOLExact v) sh && shapeEqHOL (shapeOfHOLExact v) rs) = true
              · simp only [hsh, ↓reduceIte]
                rcases hB2 : evaluateHOLFiniteState
                    (setVarHOLFinite nm v {sB with locals := t.locals}) body with ⟨rB', sB'⟩
                simp only [hB2]
                cases rB' with
                | some _ => exact ⟨rfl, rfl⟩
                | none =>
                  have hn := hnoread {sB' with locals :=
                      HolFiniteMapExact.resVarEq sB'.locals (nm, t.locals.lookup nm)} sB'
                    (sameButLocalsClock_update_g10 (SameButLocalsClock_g10_refl sB') _ sB'.locals)
                    (fun k hk =>
                      resVarEq_lookup_ne_g10 (m := sB'.locals) (old := t.locals.lookup nm) hk)
                  exact ⟨hn.1, state_eq_lc_of_same_g10 hn.2⟩
              · simp only [hsh, ↓reduceIte]
                exact ⟨rfl, rfl⟩
            | exception _ _ => exact ⟨rfl, rfl⟩
            | error => exact ⟨rfl, rfl⟩
            | timeOut => exact ⟨rfl, rfl⟩
            | finalFfi _ => exact ⟨rfl, rfl⟩
  have hsrc := h t hc hi hw hlen hR hp (by rw [← hkey.1]; exact hnt)
  rw [← hkey.1] at hsrc
  exact opDispatchPostA_congr_lc hkey.2 hsrc

/-! ### Chunk 4: the `op_callcode` tail after `charge_gas [need]` -/

/-- The op_callcode tail: everything after the prefix's `charge_gas [need]` call —
the `warm`-ite, the delegation-cost chain, the message-call-gas charge with the
spill/restore ledger, and the insufficient-funds branch. -/
def callcodeTailProg_g10 : ProgHOL 64 :=
  .seq
    (.ite (.cmp .equal (.var .local (ofString "warm")) (.const (BitVec.ofNat 64 0)))
      (.call (some (none, none)) (ofString "warm_address")
        [.var .local (ofString "code_address0")])
      .skip)
    (.decCall (ofString "dl") (.comb [.one, .one, .one]) (ofString "calculate_delegation_cost")
      [.var .local (ofString "code_address0")]
      (.dec (ofString "code_address") .one (.rfield 1 (.var .local (ofString "dl")))
        (.seq
          (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "dl")))
              (.const (BitVec.ofNat 64 0)))
            (.seq (.call (some (none, none)) (ofString "charge_gas")
                [.rfield 2 (.var .local (ofString "dl"))])
              (.call (some (none, none)) (ofString "warm_address")
                [.var .local (ofString "code_address")]))
            .skip)
          (.decCall (ofString "code") (.comb [.one, .one]) (ofString "ext_code_of")
            [.var .local (ofString "code_address")]
            (.decCall (ofString "gw") .one (ofString "sat_word")
              [.var .local (ofString "gasv")]
              (.decCall (ofString "mcg") (.comb [.one, .one])
                  (ofString "calculate_message_call_gas")
                [.var .local (ofString "value"),
                 .var .local (ofString "gw"),
                 .load .one
                   (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 64)]),
                 .const (BitVec.ofNat 64 0),
                 .const (BitVec.ofNat 64 0)]
                (.seq
                  (.call (some (none, none)) (ofString "charge_gas")
                    [.rfield 0 (.var .local (ofString "mcg"))])
                  (.seq
                    (.store (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 184)])
                      (.op .sub
                        [.load .one
                           (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 184)]),
                         .rfield 1 (.var .local (ofString "mcg"))]))
                    (.seq
                      (.call (some (none, none)) (ofString "extend_memory")
                        [.rfield 1 (.var .local (ofString "x"))])
                      (.dec (ofString "reservoir") .one
                        (.load .one
                          (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 72)]))
                        (.seq
                          (.store (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 72)])
                            (.const (BitVec.ofNat 64 0)))
                          (.decCall (ofString "sender") .one (ofString "get_account")
                            [.var .local (ofString "to")]
                            (.decCall (ofString "insufficient") .one (ofString "u256_lt")
                              [.load (.comb [.one, .one, .one, .one])
                                 (.op .add [.var .local (ofString "sender"),
                                   .const (BitVec.ofNat 64 8)]),
                               .var .local (ofString "value")]
                              (.dec (ofString "started") .one (.const (BitVec.ofNat 64 0))
                                (.seq
                                  (.ite (.cmp .notEqual (.var .local (ofString "insufficient"))
                                      (.const (BitVec.ofNat 64 0)))
                                    (.seq (.call (some (none, none)) (ofString "stack_push")
                                        [.rstruct [.const (0#64), .const (0#64), .const (0#64), .const (0#64)]])
                                      (.dec (ofString "empty") .one
                                        (.var .global (ofString "evm_empty"))
                                        (.seq (.call (some (none, none)) (ofString "set_retdata")
                                            [.var .local (ofString "empty"),
                                             .const (BitVec.ofNat 64 0)])
                                          (.seq
                                            (.store (.op .add [.var .global (ofString "ev"),
                                                .const (BitVec.ofNat 64 64)])
                                              (.op .add
                                                [.load .one (.op .add [.var .global (ofString "ev"),
                                                   .const (BitVec.ofNat 64 64)]),
                                                 .rfield 1 (.var .local (ofString "mcg"))]))
                                            (.store (.op .add [.var .global (ofString "ev"),
                                                .const (BitVec.ofNat 64 72)])
                                              (.op .add
                                                [.load .one (.op .add [.var .global (ofString "ev"),
                                                   .const (BitVec.ofNat 64 72)]),
                                                 .var .local (ofString "reservoir")]))))))
                                    (.decCall (ofString "is") .one (ofString "sat_word")
                                      [.var .local (ofString "in_start")]
                                      (.decCall (ofString "isz") .one (ofString "sat_word")
                                        [.var .local (ofString "in_size")]
                                        (.decCall (ofString "os") .one (ofString "sat_word")
                                          [.var .local (ofString "out_start")]
                                          (.decCall (ofString "osz") .one (ofString "sat_word")
                                            [.var .local (ofString "out_size")]
                                            (.call (some (some (.local, ofString "started"), none))
                                              (ofString "generic_call")
                                              [.rfield 1 (.var .local (ofString "mcg")),
                                               .var .local (ofString "reservoir"),
                                               .var .local (ofString "value"),
                                               .var .local (ofString "to"),
                                               .var .local (ofString "to"),
                                               .var .local (ofString "code_address"),
                                               .const (BitVec.ofNat 64 1),
                                               .const (BitVec.ofNat 64 0),
                                               .var .local (ofString "is"),
                                               .var .local (ofString "isz"),
                                               .var .local (ofString "os"),
                                               .var .local (ofString "osz"),
                                               .rfield 0 (.var .local (ofString "code")),
                                               .rfield 1 (.var .local (ofString "code")),
                                               .rfield 0 (.var .local (ofString "dl")),
                                               .const (BitVec.ofNat 64 0)]))))))
                                  callcodeContProg_g10)))))))))))))))

/-- Post-`dl`-decCall bundle: the `CcPQ` pins plus the `dl` local as a three-word
record with the cost/shape correlations from `calculate_delegation_cost`. -/
def CcDLQ_g10 {F : Type} (s0 t : PanSemStateFiniteExact 64 F) : Prop :=
  CcPQ_g10 s0 t ∧
  ∃ (d0 d1 d2 : BitVec 64),
    t.locals.lookup (ofString "dl") =
      some (.rStruct [.val (.word d0), .val (.word d1), .val (.word d2)]) ∧
    (d0 = 0#64 → d2 = 0#64) ∧
    (d0 ≠ 0#64 → 0 < d2.toNat)

/-- Post-`mcg`-decCall bundle: the `CcDLQ` pins plus the `mcg` local as a two-word
record with the stipend classification. -/
def CcMGQ_g10 {F : Type} (s0 t : PanSemStateFiniteExact 64 F) : Prop :=
  CcDLQ_g10 s0 t ∧
  ∃ (w0 w1 st : BitVec 64),
    t.locals.lookup (ofString "mcg") =
      some (.rStruct [.val (.word w0), .val (.word w1)]) ∧
    w1.toNat ≤ w0.toNat + st.toNat ∧
    (st = 0#64 ∨ (st = 2300#64 ∧ ∀ q0 q1 q2 q3 : BitVec 64,
      t.locals.lookup (ofString "value") =
        some (.rStruct [.val (.word q0), .val (.word q1),
          .val (.word q2), .val (.word q3)]) →
      (q0 ||| q1 ||| q2 ||| q3) ≠ 0#64))

/-- Post-`charge_gas [mcg.0]` bundle: the full `x`-pin (needed for the coming
`extend_memory`), the `mcg` pin (needed by the failure-path `ev+64` restore), and
the upgraded credit `evmR t + mcg.1 ≤ evmR s0` (the charged `w0` pays for the
restorable `w1 = w0 + stipend`). -/
def CcRQ_g10 {F : Type} (s0 t : PanSemStateFiniteExact 64 F) : Prop :=
  MemoryExpansionLocal_g10 t ∧
  ∃ (w0 w1 : BitVec 64),
    t.locals.lookup (ofString "mcg") =
      some (.rStruct [.val (.word w0), .val (.word w1)]) ∧
    evmR t + w1.toNat + 1 ≤ evmR s0 ∧ EvmInv s0

/-- Post-`extend_memory` bundle: the `x` size-word condition has been consumed by
the `extend_memory` entry obligation; the `mcg` pin and credit survive. -/
def CcR2Q_g10 {F : Type} (s0 t : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ (w0 w1 : BitVec 64),
    t.locals.lookup (ofString "mcg") =
      some (.rStruct [.val (.word w0), .val (.word w1)]) ∧
    evmR t + w1.toNat + 1 ≤ evmR s0 ∧ EvmInv s0

/-- The `calculate_message_call_gas` callee's argument locals are the call values:
`value` the four-word record, `gas`/`gas_left`/`memory_cost`/`extra_gas` words.
The zero-ness of the last two comes from the call site's `const 0` arguments, not
from the lookup, and is established at the use site. -/
theorem cmc_args_lookup_g10 {body' : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {ret' : ShapeHOL}
    {v0 v1 v2 v3 v4 : ValueHOL 64}
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "calculate_message_call_gas")
        [v0, v1, v2, v3, v4] = some (body', callee, ret')) :
    ∃ (q0 q1 q2 q3 gw gl m3 m4 : BitVec 64),
      v0 = .rStruct [.val (.word q0), .val (.word q1), .val (.word q2), .val (.word q3)] ∧
      v1 = .val (.word gw) ∧ v2 = .val (.word gl) ∧
      v3 = .val (.word m3) ∧ v4 = .val (.word m4) ∧
      callee.lookup (ofString "value") = v0 ∧
      callee.lookup (ofString "gas") = v1 ∧
      callee.lookup (ofString "gas_left") = v2 ∧
      callee.lookup (ofString "memory_cost") = v3 ∧
      callee.lookup (ofString "extra_gas") = v4 := by
  have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
    originalRuntimeCode.lookup (ofString "calculate_message_call_gas") [v0, v1, v2, v3, v4]
    body' callee ret' hl
  simp only [Flapjack.lookupCodeHOLExact, lookup_calculate_message_call_gas] at hx
  split at hx
  · rename_i hcond
    have heq := Option.some.inj hx
    rcases Prod.mk.inj heq with ⟨rfl, hrest⟩
    rcases Prod.mk.inj hrest with ⟨hloc, rfl⟩
    have hall := hcond.2.2
    have hshv : shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact v0) = true ∧
        shapeEqHOL .one (shapeOfHOLExact v1) = true ∧
        shapeEqHOL .one (shapeOfHOLExact v2) = true ∧
        shapeEqHOL .one (shapeOfHOLExact v3) = true ∧
        shapeEqHOL .one (shapeOfHOLExact v4) = true := by
      simpa using hall
    obtain ⟨hsh0, hsh1, hsh2, hsh3, hsh4⟩ := hshv
    obtain ⟨q0, q1, q2, q3, rfl⟩ := value_word4_of_shape_g10 hsh0
    rcases v1 with ⟨⟨gw⟩⟩ | v1' | v1'
    · rcases v2 with ⟨⟨gl⟩⟩ | v2' | v2'
      · rcases v3 with ⟨⟨m3⟩⟩ | v3' | v3'
        · rcases v4 with ⟨⟨m4⟩⟩ | v4' | v4'
          · have hvg : ofString "value" ≠ ofString "gas" := by decide
            have hvgl : ofString "value" ≠ ofString "gas_left" := by decide
            have hvmc : ofString "value" ≠ ofString "memory_cost" := by decide
            have hvea : ofString "value" ≠ ofString "extra_gas" := by decide
            have hggl : ofString "gas" ≠ ofString "gas_left" := by decide
            have hgmc : ofString "gas" ≠ ofString "memory_cost" := by decide
            have hgea : ofString "gas" ≠ ofString "extra_gas" := by decide
            have hglmc : ofString "gas_left" ≠ ofString "memory_cost" := by decide
            have hglea : ofString "gas_left" ≠ ofString "extra_gas" := by decide
            have hmcea : ofString "memory_cost" ≠ ofString "extra_gas" := by decide
            refine ⟨q0, q1, q2, q3, gw, gl, m3, m4, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
            · have hfn := congrFun hloc.symm (ofString "value")
              simpa [FUPDATE_LIST, FUPDATE,
                hvg, Ne.symm hvg, hvgl, Ne.symm hvgl, hvmc, Ne.symm hvmc,
                hvea, Ne.symm hvea] using hfn
            · have hfn := congrFun hloc.symm (ofString "gas")
              simpa [FUPDATE_LIST, FUPDATE,
                hvg, Ne.symm hvg, hggl, Ne.symm hggl, hgmc, Ne.symm hgmc,
                hgea, Ne.symm hgea] using hfn
            · have hfn := congrFun hloc.symm (ofString "gas_left")
              simpa [FUPDATE_LIST, FUPDATE,
                hvgl, Ne.symm hvgl, hggl, Ne.symm hggl, hglmc, Ne.symm hglmc,
                hglea, Ne.symm hglea] using hfn
            · have hfn := congrFun hloc.symm (ofString "memory_cost")
              simpa [FUPDATE_LIST, FUPDATE,
                hvmc, Ne.symm hvmc, hgmc, Ne.symm hgmc, hglmc, Ne.symm hglmc,
                hmcea, Ne.symm hmcea] using hfn
            · have hfn := congrFun hloc.symm (ofString "extra_gas")
              simpa [FUPDATE_LIST, FUPDATE] using hfn
          · exact absurd hsh4 (by simp [shapeOfHOLExact, shapeEqHOL])
          · exact absurd hsh4 (by simp [shapeOfHOLExact, shapeEqHOL])
        · exact absurd hsh3 (by simp [shapeOfHOLExact, shapeEqHOL])
        · exact absurd hsh3 (by simp [shapeOfHOLExact, shapeEqHOL])
      · exact absurd hsh2 (by simp [shapeOfHOLExact, shapeEqHOL])
      · exact absurd hsh2 (by simp [shapeOfHOLExact, shapeEqHOL])
    · exact absurd hsh1 (by simp [shapeOfHOLExact, shapeEqHOL])
    · exact absurd hsh1 (by simp [shapeOfHOLExact, shapeEqHOL])
  · cases hx


/-! ### Batch B: state-plumbing transport helpers -/

/-- `EvmInv`'s only regular-gas conjunct is exactly the `evmR` ceiling. -/
theorem evmInv_gas_top_g10 {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : EvmInv s) : evmR s + 1 < 2 ^ 64 := by
  obtain ⟨_, _, _, hrest⟩ := h
  dsimp only at hrest
  exact hrest.2.2.2.2.2.2.2.2.2.2.2

/-- A local slot other than the assigned one is untouched by `setVarHOLFinite`. -/
private theorem setVar_lookup_ne_g10 {F : Type} (t : PanSemStateFiniteExact 64 F)
    (nm nm' : MlS) (v : ValueHOL 64) (hne : nm ≠ nm') :
    (setVarHOLFinite nm v t).locals.lookup nm' = t.locals.lookup nm' := by
  simp only [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  rw [if_neg (by simp [hne])]

/-- A local slot other than the assigned one is untouched by a call-return resume
that also restores the caller's locals. -/
private theorem setVarRes_lookup_ne_g10 {F : Type} (t cpost : PanSemStateFiniteExact 64 F)
    (nm nm' : MlS) (v : ValueHOL 64) (hne : nm ≠ nm') :
    (setVarHOLFinite nm v { cpost with locals := t.locals }).locals.lookup nm' =
      t.locals.lookup nm' := by
  simp only [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  rw [if_neg (by simp [hne])]

/-- Transport `CcPQ` to a state whose pinned locals, `ev` global, `ev+32` word and
`evmR` agree with the old one. -/
private theorem CcPQ_lu_g10 {F : Type} {s0 t r : PanSemStateFiniteExact 64 F}
    (hlu : ∀ nm' ∈ (["value", "vz", "transfer_cost", "access_cost", "x", "dl"] : List String),
      r.locals.lookup (ofString nm') = t.locals.lookup (ofString nm'))
    (heR : evmR r ≤ evmR t) (hgm : globN r "ev" = globN t "ev")
    (hxm : memW r (globN t "ev" + 32) = memW t (globN t "ev" + 32))
    (h : CcPQ_g10 s0 t) : CcPQ_g10 s0 r := by
  obtain ⟨q0, q1, q2, q3, vz, tcw, acw, cw, ebw, Sl,
    hvalue, hvz, htc, hac, hacw, hx, hxebw, hvzcase, hcredit, hInvS⟩ := h
  refine ⟨q0, q1, q2, q3, vz, tcw, acw, cw, ebw, Sl,
    (hlu "value" (by decide)).trans hvalue, (hlu "vz" (by decide)).trans hvz,
    (hlu "transfer_cost" (by decide)).trans htc,
    (hlu "access_cost" (by decide)).trans hac, hacw,
    (hlu "x" (by decide)).trans hx, ?_, hvzcase, ?_, hInvS⟩
  · rcases hxebw with hz | hb
    · exact Or.inl hz
    · rw [hgm]
      exact Or.inr ⟨by rw [hxm]; exact hb.1, by rw [hxm]; exact hb.2⟩
  · omega

/-- Transport `CcDLQ` to a state whose pinned locals (including `dl`), `ev`
global, `ev+32` word and `evmR` agree with the old one. -/
theorem CcDLQ_lu_g10 {F : Type} {s0 t r : PanSemStateFiniteExact 64 F}
    (hlu : ∀ nm' ∈ (["value", "vz", "transfer_cost", "access_cost", "x", "dl"] : List String),
      r.locals.lookup (ofString nm') = t.locals.lookup (ofString nm'))
    (heR : evmR r ≤ evmR t) (hgm : globN r "ev" = globN t "ev")
    (hxm : memW r (globN t "ev" + 32) = memW t (globN t "ev" + 32))
    (h : CcDLQ_g10 s0 t) : CcDLQ_g10 s0 r := by
  obtain ⟨hpq, d0, d1, d2, hdl, hc1, hc2⟩ := h
  exact ⟨CcPQ_lu_g10 hlu heR hgm hxm hpq,
    d0, d1, d2, (hlu "dl" (by decide)).trans hdl, hc1, hc2⟩

/-- Transport `CcR2Q` over a plain `dec` local assignment outside `mcg`. -/
theorem CcR2Q_setVar_g10 {F : Type} {s0 t : PanSemStateFiniteExact 64 F}
    {nm : MlS} {v : ValueHOL 64} (hne : nm ≠ ofString "mcg")
    (h : CcR2Q_g10 s0 t) : CcR2Q_g10 s0 (setVarHOLFinite nm v t) := by
  obtain ⟨w0, w1, hmcg, hcredit, hInvS⟩ := h
  have hc : evmR (setVarHOLFinite nm v t) = evmR t :=
    (evm_congr (s := t) (t := setVarHOLFinite nm v t) rfl rfl).2.1
  refine ⟨w0, w1, ?_, ?_, hInvS⟩
  · rw [setVar_lookup_ne_g10 t nm (ofString "mcg") v hne]
    exact hmcg
  · rw [hc]
    exact hcredit

/-- Transport `CcR2Q` over a call-return resume assigning a local outside `mcg`. -/
theorem CcR2Q_setVarRes_g10 {F : Type} {s0 t cpost : PanSemStateFiniteExact 64 F}
    {nm : MlS} {v : ValueHOL 64} (hne : nm ≠ ofString "mcg")
    (heR : evmR cpost ≤ evmR t) (h : CcR2Q_g10 s0 t) :
    CcR2Q_g10 s0 (setVarHOLFinite nm v { cpost with locals := t.locals }) := by
  obtain ⟨w0, w1, hmcg, hcredit, hInvS⟩ := h
  have hc : evmR (setVarHOLFinite nm v { cpost with locals := t.locals }) = evmR cpost :=
    (evm_congr (s := cpost)
      (t := setVarHOLFinite nm v { cpost with locals := t.locals }) rfl rfl).2.1
  refine ⟨w0, w1, ?_, ?_, hInvS⟩
  · rw [setVarRes_lookup_ne_g10 t cpost nm (ofString "mcg") v hne]
    exact hmcg
  · omega

/-! ### Stage C, chunk 4 batch B2a: helper lemmas for the `op_callcode` tail walk -/

/-- The first word of the `mcg` record, read as a standalone expression. -/
private theorem eval_rfield0_mcg_word_g10 {F : Type} {t : PanSemStateFiniteExact 64 F}
    {w0 w1 amtw : BitVec 64}
    (hmcg : t.locals.lookup (ofString "mcg") =
      some (.rStruct [.val (.word w0), .val (.word w1)]))
    (hv : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
      (.rfield 0 (.var .local (ofString "mcg"))) = some (.val (.word amtw))) :
    amtw = w0 := by
  simp [evalHOLExact, hmcg] at hv
  exact hv.symm

/-- The third word of the `dl` record, read as a standalone expression. -/
private theorem eval_rfield2_dl_word_g10 {F : Type} {t : PanSemStateFiniteExact 64 F}
    {d0 d1 d2 amtw : BitVec 64}
    (hdl : t.locals.lookup (ofString "dl") =
      some (.rStruct [.val (.word d0), .val (.word d1), .val (.word d2)]))
    (hv : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
      (.rfield 2 (.var .local (ofString "dl"))) = some (.val (.word amtw))) :
    amtw = d2 := by
  simp [evalHOLExact, hdl] at hv
  exact hv.symm

/-- Strict head-frame bound on the `ev` global. -/
private theorem ev280_lt_g10 {F : Type} {t : PanSemStateFiniteExact 64 F} (hInv : EvmInv t) :
    globN t "ev" + 280 < 2 ^ 64 := by
  obtain ⟨hAR, S, hWT, hrest⟩ := hInv
  dsimp only at hrest
  obtain ⟨hch_ne, hch_len, hlast, hFWF, hFRoom, hRetW, hPair, hDisj, hTries, hMarks, hRoles, hGasSum⟩ := hrest
  have hhead : (globN t "ev", globN t "cur_cont") ∈ evmChain t := by
    simp [evmChain, evmChainFrom]
  have hF0 := hFWF _ hhead
  have hbb := (hF0.1 (globN t "ev", 280) (by simp)).1.2
  rw [R11Shards.scratchEnd_val] at hbb
  omega

/-- An off-store at `ev+k` (k = 184 or 72) preserves the head stack-size word at
`ev+32`. -/
private theorem memW_updW_ev32_g10 {F : Type} {t : PanSemStateFiniteExact 64 F}
    {k : Nat} (hlt : globN t "ev" + 280 < 2 ^ 64) (w : BitVec 64) (hk : k = 184 ∨ k = 72)
    (hk32 : k ≠ 32) :
    memW ({ t with memory := R14Shards.OpHandlersA.updW t.memory (BitVec.ofNat 64 (globN t "ev" + k)) w })
        (globN t "ev" + 32) = memW t (globN t "ev" + 32) := by
  have hbvne : BitVec.ofNat 64 (globN t "ev" + k) ≠ BitVec.ofNat 64 (globN t "ev" + 32) := by
    intro h
    have hc := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at hc
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hc
    omega
  simp [memW, R14Shards.OpHandlersA.updW, Ne.symm hbvne]

/-- The call entry state has the same `evmR` as the caller. -/
theorem evmR_entry_eq_g10 {F : Type} {t : PanSemStateFiniteExact 64 F}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} :
    evmR (callEntryStateHOLFinite t callee) = evmR t :=
  (evm_congr (s := t) (t := callEntryStateHOLFinite t callee) rfl rfl).2.1

/-- A five-argument call list decomposes into its component evaluations. -/
private theorem evalList5_decomp_g10 {F : Type} {t : PanSemStateFiniteExact 64 F}
    {e0 e1 e2 e3 e4 : ExpHOL 64} {values : List (ValueHOL 64)}
    (hargs : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
      [e0, e1, e2, e3, e4] = some values) :
    ∃ v0 v1 v2 v3 v4 : ValueHOL 64,
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) e0 = some v0 ∧
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) e1 = some v1 ∧
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) e2 = some v2 ∧
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) e3 = some v3 ∧
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) e4 = some v4 ∧
      values = [v0, v1, v2, v3, v4] := by
  rw [evalListHOLFinite_eq_toExact] at hargs
  simp only [evalListHOLExact] at hargs
  rcases he0 : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) e0 with _ | v0
  · simp [he0] at hargs
  rcases he1 : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) e1 with _ | v1
  · simp [he0, he1] at hargs
  rcases he2 : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) e2 with _ | v2
  · simp [he0, he1, he2] at hargs
  rcases he3 : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) e3 with _ | v3
  · simp [he0, he1, he2, he3] at hargs
  rcases he4 : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) e4 with _ | v4
  · simp [he0, he1, he2, he3, he4] at hargs
  simp only [he0, he1, he2, he3, he4, Option.some.injEq] at hargs
  exact ⟨v0, v1, v2, v3, v4, rfl, rfl, rfl, rfl, rfl, hargs.symm⟩

/-- Six pinned locals are untouched by a `dec` that assigns outside them. -/
private theorem lu6_setVar_ne_g10 {F : Type} (t : PanSemStateFiniteExact 64 F)
    (nm : MlS) (v : ValueHOL 64)
    (hne : nm ≠ ofString "value" ∧ nm ≠ ofString "vz" ∧ nm ≠ ofString "transfer_cost" ∧
      nm ≠ ofString "access_cost" ∧ nm ≠ ofString "x" ∧ nm ≠ ofString "dl") :
    ∀ nm' ∈ (["value", "vz", "transfer_cost", "access_cost", "x", "dl"] : List String),
      (setVarHOLFinite nm v t).locals.lookup (ofString nm') = t.locals.lookup (ofString nm') := by
  intro nm' hmem
  simp only [List.mem_cons, List.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | hbad
  · exact setVar_lookup_ne_g10 t nm (ofString "value") v hne.1
  · exact setVar_lookup_ne_g10 t nm (ofString "vz") v hne.2.1
  · exact setVar_lookup_ne_g10 t nm (ofString "transfer_cost") v hne.2.2.1
  · exact setVar_lookup_ne_g10 t nm (ofString "access_cost") v hne.2.2.2.1
  · exact setVar_lookup_ne_g10 t nm (ofString "x") v hne.2.2.2.2.1
  · exact setVar_lookup_ne_g10 t nm (ofString "dl") v hne.2.2.2.2.2
  · cases hbad

/-- Six pinned locals are untouched by a call-return resume assigning outside them. -/
theorem lu6_setVarRes_ne_g10 {F : Type} (t cpost : PanSemStateFiniteExact 64 F)
    (nm : MlS) (v : ValueHOL 64)
    (hne : nm ≠ ofString "value" ∧ nm ≠ ofString "vz" ∧ nm ≠ ofString "transfer_cost" ∧
      nm ≠ ofString "access_cost" ∧ nm ≠ ofString "x" ∧ nm ≠ ofString "dl") :
    ∀ nm' ∈ (["value", "vz", "transfer_cost", "access_cost", "x", "dl"] : List String),
      (setVarHOLFinite nm v { cpost with locals := t.locals }).locals.lookup (ofString nm')
        = t.locals.lookup (ofString nm') := by
  intro nm' hmem
  simp only [List.mem_cons, List.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | hbad
  · exact setVarRes_lookup_ne_g10 t cpost nm (ofString "value") v hne.1
  · exact setVarRes_lookup_ne_g10 t cpost nm (ofString "vz") v hne.2.1
  · exact setVarRes_lookup_ne_g10 t cpost nm (ofString "transfer_cost") v hne.2.2.1
  · exact setVarRes_lookup_ne_g10 t cpost nm (ofString "access_cost") v hne.2.2.2.1
  · exact setVarRes_lookup_ne_g10 t cpost nm (ofString "x") v hne.2.2.2.2.1
  · exact setVarRes_lookup_ne_g10 t cpost nm (ofString "dl") v hne.2.2.2.2.2
  · cases hbad

/-- Transport `CcPQ` over a state whose pinned locals (five names), `ev` global,
`ev+32` word and `evmR` agree with the old one. -/
theorem CcPQ_lu5_g10 {F : Type} {s0 t r : PanSemStateFiniteExact 64 F}
    (hlu : ∀ nm' ∈ (["value", "vz", "transfer_cost", "access_cost", "x"] : List String),
      r.locals.lookup (ofString nm') = t.locals.lookup (ofString nm'))
    (heR : evmR r ≤ evmR t) (hgm : globN r "ev" = globN t "ev")
    (hxm : memW r (globN t "ev" + 32) = memW t (globN t "ev" + 32))
    (h : CcPQ_g10 s0 t) : CcPQ_g10 s0 r := by
  obtain ⟨q0, q1, q2, q3, vz, tcw, acw, cw, ebw, Sl,
    hvalue, hvz, htc, hac, hacw, hx, hxebw, hvzcase, hcredit, hInvS⟩ := h
  refine ⟨q0, q1, q2, q3, vz, tcw, acw, cw, ebw, Sl,
    (hlu "value" (by decide)).trans hvalue, (hlu "vz" (by decide)).trans hvz,
    (hlu "transfer_cost" (by decide)).trans htc,
    (hlu "access_cost" (by decide)).trans hac, hacw,
    (hlu "x" (by decide)).trans hx, ?_, hvzcase, ?_, hInvS⟩
  · rcases hxebw with hz | hb
    · exact Or.inl hz
    · rw [hgm]
      exact Or.inr ⟨by rw [hxm]; exact hb.1, by rw [hxm]; exact hb.2⟩
  · omega

/-- Transport `CcR2Q` over a plain call-return resume with `evmR cpost ≤ evmR t`. -/
theorem CcR2Q_res_g10 {F : Type} {s0 t cpost : PanSemStateFiniteExact 64 F}
    (heR : evmR cpost ≤ evmR t) (h : CcR2Q_g10 s0 t) :
    CcR2Q_g10 s0 { cpost with locals := t.locals } := by
  obtain ⟨w0, w1, hmcg, hcredit, hInvS⟩ := h
  have h1 : evmR { cpost with locals := t.locals } = evmR cpost :=
    (evm_congr (s := cpost) (t := { cpost with locals := t.locals }) rfl rfl).2.1
  exact ⟨w0, w1, hmcg, by rw [h1]; omega, hInvS⟩

/-! ### Batch B2b: the `op_callcode` tail walk (chunk 5)

The tail after the prefix's `charge_gas [need]`: the warm-ite, the delegation-cost
chain, the message-call-gas charge with the spill/restore ledger, and the
insufficient-funds branch, down to the terminal `started`-test continuation. -/

/-- Five pinned locals are untouched by a call-return resume assigning outside them. -/
theorem lu5_setVarRes_ne_g10 {F : Type} (t cpost : PanSemStateFiniteExact 64 F)
    (nm : MlS) (v : ValueHOL 64)
    (hne : nm ≠ ofString "value" ∧ nm ≠ ofString "vz" ∧ nm ≠ ofString "transfer_cost" ∧
      nm ≠ ofString "access_cost" ∧ nm ≠ ofString "x") :
    ∀ nm' ∈ (["value", "vz", "transfer_cost", "access_cost", "x"] : List String),
      (setVarHOLFinite nm v { cpost with locals := t.locals }).locals.lookup (ofString nm')
        = t.locals.lookup (ofString nm') := by
  intro nm' hmem
  simp only [List.mem_cons, List.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | hbad
  · exact setVarRes_lookup_ne_g10 t cpost nm (ofString "value") v hne.1
  · exact setVarRes_lookup_ne_g10 t cpost nm (ofString "vz") v hne.2.1
  · exact setVarRes_lookup_ne_g10 t cpost nm (ofString "transfer_cost") v hne.2.2.1
  · exact setVarRes_lookup_ne_g10 t cpost nm (ofString "access_cost") v hne.2.2.2.1
  · exact setVarRes_lookup_ne_g10 t cpost nm (ofString "x") v hne.2.2.2.2
  · cases hbad

/-- Transport `CcDLQ` over a plain `dec` local assignment outside the six pinned names. -/
theorem CcDLQ_setVar_g10 {F : Type} {s0 t : PanSemStateFiniteExact 64 F}
    {nm : MlS} {v : ValueHOL 64}
    (hne : nm ≠ ofString "value" ∧ nm ≠ ofString "vz" ∧ nm ≠ ofString "transfer_cost" ∧
      nm ≠ ofString "access_cost" ∧ nm ≠ ofString "x" ∧ nm ≠ ofString "dl")
    (h : CcDLQ_g10 s0 t) : CcDLQ_g10 s0 (setVarHOLFinite nm v t) := by
  have hc : evmR (setVarHOLFinite nm v t) = evmR t :=
    (evm_congr (s := t) (t := setVarHOLFinite nm v t) rfl rfl).2.1
  exact CcDLQ_lu_g10 (lu6_setVar_ne_g10 t nm v hne) (by rw [hc]) rfl rfl h

/-- The terminal continuation of the `op_callcode` tail at the trivial predicate. -/
theorem callcodeCont_run_g10 {F : Type} {s0 : PanSemStateFiniteExact 64 F} :
    HandlerRunA s0 (fun _ => True) true callcodeContProg_g10 := by
  simp only [callcodeContProg_g10]
  refine HandlerRunA.seq_ite_unit (fun t w heval hw0 => ?_) (fun t heval => ?_)
  · exact HandlerRunA.seq_call_simple epsA_pc_add
      (HandlerRunA.ret (.const (BitVec.ofNat 64 0)))
  · exact HandlerRunA.seq_skip (HandlerRunA.ret (.const (BitVec.ofNat 64 0)))

/-- The `generic_call` of the sufficient-funds branch, with the `started` result
assigned to a local and the terminal continuation attached. -/
theorem callcodeGenericCall_g10 {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    (hgc : EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "generic_call")) :
    HandlerRunA s0 (fun t => CcR2Q_g10 s0 t) true
      (.seq
        (.call (some (some (.local, ofString "started"), none)) (ofString "generic_call")
          [.rfield 1 (.var .local (ofString "mcg")),
           .var .local (ofString "reservoir"),
           .var .local (ofString "value"),
           .var .local (ofString "to"),
           .var .local (ofString "to"),
           .var .local (ofString "code_address"),
            .const (BitVec.ofNat 64 1),
            .const (BitVec.ofNat 64 0),
            .var .local (ofString "is"),
            .var .local (ofString "isz"),
            .var .local (ofString "os"),
            .var .local (ofString "osz"),
            .rfield 0 (.var .local (ofString "code")),
           .rfield 1 (.var .local (ofString "code")),
           .rfield 0 (.var .local (ofString "dl")),
           .const (BitVec.ofNat 64 0)])
        callcodeContProg_g10) :=
  HandlerRunA.seq_call_assign_local hgc
    (fun t values body' callee ret' hc hi hw hp hargs hl => trivial)
    (fun t values body callee retShape v cpost hi hw hp hargs hl hshp hi_cp hw_cp hch_cp hQc =>
      CcR2Q_setVarRes_g10 (by decide)
        (le_of_eq ((evmR_congr_full_g10 hQc).trans evmR_entry_eq_g10)) hp)
    (HandlerRunA.weaken (fun t ht hp => trivial) callcodeCont_run_g10)

/-- The `insufficient != 0` branch: the YES side restores the regular-gas word
`ev+64` by adding back `mcg.1` (a store that can raise `evmR`, so the strict
drop is banked at the `charge_gas [mcg.0]` step), clears the reservoir word, and
returns 0; the NO side runs `generic_call` and the terminal continuation. -/
theorem callcodeInsfTail_g10 {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    (hgc : EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "generic_call")) :
    HandlerRunA s0 (fun t => CcR2Q_g10 s0 t) true
      (.seq
        (.ite (.cmp .notEqual (.var .local (ofString "insufficient"))
            (.const (BitVec.ofNat 64 0)))
          (.seq (.call (some (none, none)) (ofString "stack_push")
              [.rstruct [.const (0#64), .const (0#64), .const (0#64), .const (0#64)]])
            (.dec (ofString "empty") .one (.var .global (ofString "evm_empty"))
              (.seq (.call (some (none, none)) (ofString "set_retdata")
                  [.var .local (ofString "empty"), .const (BitVec.ofNat 64 0)])
                (.seq (.store (.op .add [.var .global (ofString "ev"),
                      .const (BitVec.ofNat 64 64)])
                    (.op .add
                      [.load .one (.op .add [.var .global (ofString "ev"),
                         .const (BitVec.ofNat 64 64)]),
                       .rfield 1 (.var .local (ofString "mcg"))]))
                  (.store (.op .add [.var .global (ofString "ev"),
                      .const (BitVec.ofNat 64 72)])
                    (.op .add
                      [.load .one (.op .add [.var .global (ofString "ev"),
                         .const (BitVec.ofNat 64 72)]),
                       .var .local (ofString "reservoir")]))))))
          (.decCall (ofString "is") .one (ofString "sat_word")
            [.var .local (ofString "in_start")]
            (.decCall (ofString "isz") .one (ofString "sat_word")
              [.var .local (ofString "in_size")]
              (.decCall (ofString "os") .one (ofString "sat_word")
                [.var .local (ofString "out_start")]
                (.decCall (ofString "osz") .one (ofString "sat_word")
                  [.var .local (ofString "out_size")]
                  (.call (some (some (.local, ofString "started"), none))
                    (ofString "generic_call")
                    [.rfield 1 (.var .local (ofString "mcg")),
                     .var .local (ofString "reservoir"),
                     .var .local (ofString "value"),
                     .var .local (ofString "to"),
                     .var .local (ofString "to"),
                     .var .local (ofString "code_address"),
                     .const (BitVec.ofNat 64 1),
                     .const (BitVec.ofNat 64 0),
                     .var .local (ofString "is"),
                     .var .local (ofString "isz"),
                     .var .local (ofString "os"),
                     .var .local (ofString "osz"),
                     .rfield 0 (.var .local (ofString "code")),
                     .rfield 1 (.var .local (ofString "code")),
                     .rfield 0 (.var .local (ofString "dl")),
                     .const (BitVec.ofNat 64 0)]))))))
        callcodeContProg_g10) := by
  refine HandlerRunA.seq_ite_unit (fun t w heval hw0 => ?_) (fun t heval => ?_)
  · refine HandlerRunA.seq_assoc ?_
    refine HandlerRunA.seq_call (epsA_keepR_g10 epsA_stack_push)
      (Q := fun t => CcR2Q_g10 s0 t) ?_ ?_ ?_
    · intro t values body' callee ret' hc hi hw hp hargs hl
      exact trivial
    · intro t values body callee retShape v cpost hi hw hp hargs hl hi_cp hw_cp hch_cp hQc
      obtain ⟨hgpins, hR_cp⟩ := hQc
      rw [evmR_entry_eq_g10] at hR_cp
      exact CcR2Q_res_g10 hR_cp hp
    · refine seq_dec_swap_g10 (callcodeCont_noread_g10 (by decide)) ?_
      refine HandlerRunA.dec_carry_g10 (fun t v hp => CcR2Q_setVar_g10 (by decide) hp) ?_
      refine HandlerRunA.seq_assoc ?_
      refine HandlerRunA.seq_set_retdata_empty (P := fun t => CcR2Q_g10 s0 t)
        (Q := fun t => CcR2Q_g10 s0 t) ?_ ?_
      · intro t cpost hi hw hp hi_cp hw_cp hch_cp hglob_cp hevR_cp hbe hmem
        exact CcR2Q_res_g10 (le_of_eq hevR_cp) hp
      · refine HandlerRunA.seq_assoc ?_
        refine HandlerRunA.seq_store_ev64_charged_g10 (P := fun t => CcR2Q_g10 s0 t)
          (Q := fun _ => True) ?_ ?_ ?_
        · intro t v hp hv
          obtain ⟨w0, w1, hmcg, hcredit, hInvS⟩ := hp
          obtain ⟨w', hwv, hwK⟩ := eval_store64_add_g10 hmcg hv
          exact ⟨w', hwv⟩
        · intro t w heval hi hw hp hR_lt
          obtain ⟨w0, w1, hmcg, hcredit, hInvS⟩ := hp
          obtain ⟨w', hwv, hwK⟩ := eval_store64_add_g10 hmcg heval
          injection hwv with hwv1
          injection hwv1 with hwv2
          subst hwv2
          obtain ⟨hInv1, hWF1, hch1, hR1⟩ :=
            ev64_store_evmStep_g10 (s0 := s0) (K := w1.toNat) hi hw hwK hcredit
              (evmInv_gas_top_g10 hInvS)
          exact ⟨hInv1, hWF1, hch1, trivial, hR1⟩
        · refine HandlerRunA.seq_store_ev_off_charged_g10 (off := 72)
            (P := fun _ => True) (Q := fun _ => True) (by omega) ?_ ?_ ?_
          · intro t v hp hv
            exact eval_op_word_g10 BinOp.add _ v hv
          · intro t w heval hi hw hp hR_lt
            obtain ⟨hInv1, hWF1, hch1, hRle⟩ :=
              evOff_store_evmStep_g10 (Q := fun _ => True) t w 72 (Or.inr rfl) hi hw
            exact ⟨hInv1, hWF1, hch1, trivial, lt_of_le_of_lt hRle hR_lt⟩
          · exact callcodeCont_run_g10
  · refine seq_decCall_swap_g10 (callcodeCont_noread_g10 (nm := ofString "is") (by decide)) ?_
    refine HandlerRunA.decCall epsA_sat_word (Q := fun t => CcR2Q_g10 s0 t) ?_ ?_ ?_
    · intro t values body' callee ret' hc hi hw hp hargs hl
      exact trivial
    · intro t values body callee retShape v cpost hi hw hp hargs hl hi_cp hw_cp hch_cp hQc
      exact CcR2Q_setVarRes_g10 (by decide)
        (le_of_eq ((evmR_congr_full_g10 hQc).trans evmR_entry_eq_g10)) hp
    · refine seq_decCall_swap_g10 (callcodeCont_noread_g10 (nm := ofString "isz") (by decide)) ?_
      refine HandlerRunA.decCall epsA_sat_word (Q := fun t => CcR2Q_g10 s0 t) ?_ ?_ ?_
      · intro t values body' callee ret' hc hi hw hp hargs hl
        exact trivial
      · intro t values body callee retShape v cpost hi hw hp hargs hl hi_cp hw_cp hch_cp hQc
        exact CcR2Q_setVarRes_g10 (by decide)
          (le_of_eq ((evmR_congr_full_g10 hQc).trans evmR_entry_eq_g10)) hp
      · refine seq_decCall_swap_g10 (callcodeCont_noread_g10 (nm := ofString "os") (by decide)) ?_
        refine HandlerRunA.decCall epsA_sat_word (Q := fun t => CcR2Q_g10 s0 t) ?_ ?_ ?_
        · intro t values body' callee ret' hc hi hw hp hargs hl
          exact trivial
        · intro t values body callee retShape v cpost hi hw hp hargs hl hi_cp hw_cp hch_cp hQc
          exact CcR2Q_setVarRes_g10 (by decide)
            (le_of_eq ((evmR_congr_full_g10 hQc).trans evmR_entry_eq_g10)) hp
        · refine seq_decCall_swap_g10 (callcodeCont_noread_g10 (nm := ofString "osz") (by decide)) ?_
          refine HandlerRunA.decCall epsA_sat_word (Q := fun t => CcR2Q_g10 s0 t) ?_ ?_ ?_
          · intro t values body' callee ret' hc hi hw hp hargs hl
            exact trivial
          · intro t values body callee retShape v cpost hi hw hp hargs hl hi_cp hw_cp hch_cp hQc
            exact CcR2Q_setVarRes_g10 (by decide)
              (le_of_eq ((evmR_congr_full_g10 hQc).trans evmR_entry_eq_g10)) hp
          · exact callcodeGenericCall_g10 hgc

/-- The `started` re-check `dec` before the insufficient-funds branch. -/
theorem callcodeStarted_g10 {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    (hgc : EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "generic_call")) {cont : ProgHOL 64}
    (hcont : HandlerRunA s0 (fun t => CcR2Q_g10 s0 t) true cont) :
    HandlerRunA s0 (fun t => CcR2Q_g10 s0 t) true
      (.dec (ofString "started") .one (.const (BitVec.ofNat 64 0)) cont) :=
  HandlerRunA.dec_carry_g10 (fun t v hp => CcR2Q_setVar_g10 (by decide) hp)
    hcont

/-- The `u256_lt` call deciding the insufficient-funds test. -/
theorem callcodeInsufficient_g10 {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    (hgc : EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "generic_call")) {cont : ProgHOL 64}
    (hcont : HandlerRunA s0 (fun t => CcR2Q_g10 s0 t) true cont) :
    HandlerRunA s0 (fun t => CcR2Q_g10 s0 t) true
      (.decCall (ofString "insufficient") .one (ofString "u256_lt")
        [.load (.comb [.one, .one, .one, .one])
           (.op .add [.var .local (ofString "sender"), .const (BitVec.ofNat 64 8)]),
         .var .local (ofString "value")]
        cont) := by
  refine HandlerRunA.decCall epsA_u256_lt (Q := fun t => CcR2Q_g10 s0 t) ?_ ?_ hcont
  · intro t values body' callee ret' hc hi hw hp hargs hl
    exact trivial
  · intro t values body callee retShape v cpost hi hw hp hargs hl hi_cp hw_cp hch_cp hQc
    exact CcR2Q_setVarRes_g10 (by decide)
      (le_of_eq ((evmR_congr_full_g10 hQc).trans evmR_entry_eq_g10)) hp

/-- The `get_account` call for the message recipient. -/
theorem callcodeSender_g10 {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    (hW : WorldAccountSpecsA)
    (hgc : EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "generic_call")) {cont : ProgHOL 64}
    (hcont : HandlerRunA s0 (fun t => CcR2Q_g10 s0 t) true cont) :
    HandlerRunA s0 (fun t => CcR2Q_g10 s0 t) true
      (.decCall (ofString "sender") .one (ofString "get_account")
        [.var .local (ofString "to")] cont) := by
  refine HandlerRunA.decCall hW.epsA_get_account (Q := fun t => CcR2Q_g10 s0 t) ?_ ?_ hcont
  · intro t values body' callee ret' hc hi hw hp hargs hl
    exact trivial
  · intro t values body callee retShape v cpost hi hw hp hargs hl hi_cp hw_cp hch_cp hQc
    obtain ⟨hgk, hRev⟩ := hQc
    exact CcR2Q_setVarRes_g10 (by decide) (le_of_eq (hRev.trans evmR_entry_eq_g10)) hp

/-- Clearing the reservoir word `ev+72` to zero. -/
theorem callcodeStore72z_g10 {F : Type} {s0 : PanSemStateFiniteExact 64 F} {cont : ProgHOL 64}
    (hcont : HandlerRunA s0 (fun t => CcR2Q_g10 s0 t) true cont) :
    HandlerRunA s0 (fun t => CcR2Q_g10 s0 t) true
      (.seq (.store (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 72)])
          (.const (BitVec.ofNat 64 0))) cont) := by
  refine HandlerRunA.seq_store_ev_off_charged_g10 (off := 72)
    (P := fun t => CcR2Q_g10 s0 t) (Q := fun t => CcR2Q_g10 s0 t) (by omega) ?_ ?_ hcont
  · intro t v hp hv
    exact ⟨BitVec.ofNat 64 0, eval_const_word_g10 _ v hv⟩
  · intro t w heval hi hw hp hR_lt
    obtain ⟨hInv1, hWF1, hch1, hRle⟩ :=
      evOff_store_evmStep_g10 (Q := fun _ => True) t w 72 (Or.inr rfl) hi hw
    obtain ⟨w0, w1, hmcg, hcredit, hInvS⟩ := hp
    exact ⟨hInv1, hWF1, hch1, ⟨w0, w1, hmcg, by omega, hInvS⟩, lt_of_le_of_lt hRle hR_lt⟩

/-- The `reservoir` `dec` reading the head reservoir word. -/
theorem callcodeReservoir_g10 {F : Type} {s0 : PanSemStateFiniteExact 64 F} {cont : ProgHOL 64}
    (hcont : HandlerRunA s0 (fun t => CcR2Q_g10 s0 t) true cont) :
    HandlerRunA s0 (fun t => CcR2Q_g10 s0 t) true
      (.dec (ofString "reservoir") .one
        (.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 72)]))
        cont) :=
  HandlerRunA.dec_carry_g10 (fun t v hp => CcR2Q_setVar_g10 (by decide) hp) hcont

/-- The `extend_memory` call consuming the `x` size-word condition. -/
theorem callcodeExtend_g10 {F : Type} {s0 : PanSemStateFiniteExact 64 F} {cont : ProgHOL 64}
    (hcont : HandlerRunA s0 (fun t => CcR2Q_g10 s0 t) true cont) :
    HandlerRunA s0 (fun t => CcRQ_g10 s0 t) true
      (.seq (.call (some (none, none)) (ofString "extend_memory")
          [.rfield 1 (.var .local (ofString "x"))]) cont) := by
  refine HandlerRunA.seq_call (epsA_keepR_g10 epsA_extend_memory)
    (Q := fun t => CcR2Q_g10 s0 t) ?_ ?_ hcont
  · intro t values body' callee ret' hc hi hw hp hargs hl
    exact memoryExpansionLocal_callee_pre_g10 t hc hw hp.1 hargs hl
  · intro t values body callee retShape v cpost hi hw hp hargs hl hi_cp hw_cp hch_cp hQc
    obtain ⟨hgpins, hR_cp⟩ := hQc
    rw [evmR_entry_eq_g10] at hR_cp
    obtain ⟨_, hc2⟩ := hp
    exact CcR2Q_res_g10 hR_cp hc2

/-- The stipend-word store `ev+184 -= mcg.1`. -/
theorem callcodeStore184_g10 {F : Type} {s0 : PanSemStateFiniteExact 64 F} {cont : ProgHOL 64}
    (hcont : HandlerRunA s0 (fun t => CcRQ_g10 s0 t) true cont) :
    HandlerRunA s0 (fun t => CcRQ_g10 s0 t) true
      (.seq (.store (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 184)])
          (.op .sub
            [.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 184)]),
             .rfield 1 (.var .local (ofString "mcg"))]))
        cont) := by
  refine HandlerRunA.seq_store_ev_off_charged_g10 (off := 184)
    (P := fun t => CcRQ_g10 s0 t) (Q := fun t => CcRQ_g10 s0 t) (by omega) ?_ ?_ hcont
  · intro t v hp hv
    exact eval_op_word_g10 BinOp.sub _ v hv
  · intro t w heval hi hw hp hR_lt
    obtain ⟨hInv1, hWF1, hch1, hRle⟩ :=
      evOff_store_evmStep_g10 (Q := fun _ => True) t w 184 (Or.inl rfl) hi hw
    obtain ⟨hmel, w0, w1, hmcg, hcredit, hInvS⟩ := hp
    refine ⟨hInv1, hWF1, hch1, ⟨?_, w0, w1, hmcg, ?_, hInvS⟩, ?_⟩
    · exact memoryExpansionLocal_transport_g10 hmel rfl rfl
        (memW_updW_ev32_g10 (ev280_lt_g10 hi) w (Or.inl rfl) (by omega))
    · omega
    · exact lt_of_le_of_lt hRle hR_lt

/-- The `charge_gas [mcg.0]` call with the exact accounting fact handed to the
continuation; the strict drop is banked here (the charged `w0` pays for the
restorable `w1 = w0 + stipend`). -/
theorem callcodeChargeMcg_g10 {F : Type} {s0 : PanSemStateFiniteExact 64 F} {cont : ProgHOL 64}
    (hcont : HandlerRunA s0 (fun t => CcRQ_g10 s0 t) true cont) :
    HandlerRunA s0 (fun t => CcMGQ_g10 s0 t) true
      (.seq (.call (some (none, none)) (ofString "charge_gas")
          [.rfield 0 (.var .local (ofString "mcg"))]) cont) := by
  refine HandlerRunA.seq_charge_gas_acc_g10 (P := fun t => CcMGQ_g10 s0 t)
    (Q := fun t => CcRQ_g10 s0 t) ?_ ?_ hcont
  · intro t w heval hi hw hp
    exact Or.inl rfl
  · intro t cpost amtw hv hi hw hp hR_le hi_cp hw_cp hglob_cp hmem32_cp hch_cp hR_cp
    obtain ⟨hpdl, w0, w1, st, hmcg, hw1le, hstc⟩ := hp
    obtain ⟨hpq, d0, d1, d2, hdl, hdc1, hdc2⟩ := hpdl
    obtain ⟨q0, q1, q2, q3, vz, tcw, acw, cw, ebw, Sl,
      hvalue, hvz, htc, hac, hacw, hx, hxebw, hvzcase, hcredit, hInvS⟩ := hpq
    have hamtw : amtw = w0 := eval_rfield0_mcg_word_g10 hmcg hv
    subst hamtw
    have hRr : evmR { cpost with locals := t.locals } = evmR cpost :=
      (evm_congr (s := cpost) (t := { cpost with locals := t.locals }) rfl rfl).2.1
    have hgm : globN { cpost with locals := t.locals } "ev"
        = globN t "ev" := globN_congr_g10 hglob_cp "ev"
    have hm32 : memW { cpost with locals := t.locals } (globN t "ev" + 32)
        = memW t (globN t "ev" + 32) := by
      have h := hmem32_cp
      rw [globN_congr_g10 hglob_cp "ev"] at h
      exact h
    refine ⟨memoryExpansionLocal_transport_g10 ⟨cw, ebw, hx, hxebw⟩ rfl hgm hm32,
      amtw, w1, hmcg, ?_, hInvS⟩
    rw [hRr]
    rcases hstc with hst0 | ⟨hst2300, hclass⟩
    · rw [hst0] at hw1le
      have hz : (0#64 : BitVec 64).toNat = 0 := by decide
      rcases hvzcase with ⟨_, _, hSl2300⟩ | ⟨_, _, _, hSl0⟩
      · rw [hSl2300] at hcredit; omega
      · rw [hSl0] at hcredit; omega
    · rw [hst2300] at hw1le
      rcases hvzcase with ⟨_, _, hSl2300⟩ | ⟨_, _, hlimbs, _⟩
      · rw [hSl2300] at hcredit
        have hz : (2300#64 : BitVec 64).toNat = 2300 := by decide
        omega
      · exact absurd hlimbs (hclass q0 q1 q2 q3 hvalue)

/-- The `calculate_message_call_gas` call (under `extra_gas = memory_cost = 0`,
which holds at this call site because both arguments are the literal `0`). -/
theorem callcodeMcg_g10 {F : Type} {s0 : PanSemStateFiniteExact 64 F} {cont : ProgHOL 64}
    (hcont : HandlerRunA s0 (fun t => CcMGQ_g10 s0 t) true cont) :
    HandlerRunA s0 (fun t => CcDLQ_g10 s0 t) true
      (.decCall (ofString "mcg") (.comb [.one, .one])
          (ofString "calculate_message_call_gas")
        [.var .local (ofString "value"),
         .var .local (ofString "gw"),
         .load .one
           (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 64)]),
         .const (BitVec.ofNat 64 0),
         .const (BitVec.ofNat 64 0)]
        cont) := by
  refine HandlerRunA.decCall Group10.epsA_cmc_g10 (Q := fun t => CcMGQ_g10 s0 t) ?_ ?_ hcont
  · intro t values body' callee ret' hc hi hw hp hargs hl
    obtain ⟨v0, v1, v2, v3, v4, hv0, hv1, hv2, hv3, hv4, hvals⟩ :=
      evalList5_decomp_g10 hargs
    subst hvals
    rw [hc] at hl
    obtain ⟨q0, q1, q2, q3, gw, gl, m3, m4, hv0v, hv1v, hv2v, hv3v, hv4v,
      hv0lk, hv1lk, hv2lk, hv3lk, hv4lk⟩ := cmc_args_lookup_g10 hl
    refine ⟨?_, ?_⟩
    · show callee.lookup (ofString "extra_gas") = some (.val (.word 0#64))
      exact hv4lk.trans (congrArg some (eval_const_word_g10 _ v4 hv4))
    · show callee.lookup (ofString "memory_cost") = some (.val (.word 0#64))
      exact hv3lk.trans (congrArg some (eval_const_word_g10 _ v3 hv3))
  · intro t values body callee retShape v cpost hi hw hp hargs hl hi_cp hw_cp hch_cp hQc
    obtain ⟨v0, v1, v2, v3, v4, hv0, hv1, hv2, hv3, hv4, hvals⟩ :=
      evalList5_decomp_g10 hargs
    subst hvals
    obtain ⟨q0, q1, q2, q3, gw, gl, m3, m4, hv0v, hv1v, hv2v, hv3v, hv4v,
      hv0lk, hv1lk, hv2lk, hv3lk, hv4lk⟩ := cmc_args_lookup_g10 hl
    obtain ⟨hlf, gl', w0, w1, st, hv, hgl, hw0gl, hw1le, hstc⟩ := hQc
    obtain ⟨hmem, hglob⟩ := locFrame_pins_g10 hlf
    have hge : cpost.globals = t.globals := hglob
    have hRr : evmR (setVarHOLFinite (ofString "mcg") v { cpost with locals := t.locals })
        = evmR cpost :=
      (evm_congr (s := cpost)
        (t := setVarHOLFinite (ofString "mcg") v { cpost with locals := t.locals }) rfl rfl).2.1
    have hRc : evmR cpost = evmR t := (evmR_congr_full_g10 hlf).trans evmR_entry_eq_g10
    have hgm : globN (setVarHOLFinite (ofString "mcg") v { cpost with locals := t.locals })
        "ev" = globN t "ev" := globN_congr_g10 hge "ev"
    have h32 : memW (setVarHOLFinite (ofString "mcg") v { cpost with locals := t.locals })
        (globN t "ev" + 32) = memW t (globN t "ev" + 32) := by
      have h := locFrame_mem32_g10 hlf
      rw [globN_congr_g10 hge "ev"] at h
      exact h
    refine ⟨CcDLQ_lu_g10 (lu6_setVarRes_ne_g10 t cpost (ofString "mcg") v (by decide))
      (by rw [hRr, hRc]) hgm h32 hp, w0, w1, st, ?_, hw1le, ?_⟩
    · dsimp only [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      first | rw [if_pos rfl, hv] | simp [hv]
    · rcases hstc with hst0 | ⟨hst2300, hclass⟩
      · exact Or.inl hst0
      · refine Or.inr ⟨hst2300, fun q0' q1' q2' q3' hvq => ?_⟩
        have hresv : (setVarHOLFinite (ofString "mcg") v { cpost with locals := t.locals }).locals.lookup (ofString "value") =
            t.locals.lookup (ofString "value") :=
          setVarRes_lookup_ne_g10 t cpost (ofString "mcg") (ofString "value") v (by decide)
        have hv0t : t.locals.lookup (ofString "value") = some v0 := hv0
        have hv0v' : v0 = .rStruct [.val (.word q0'), .val (.word q1'),
            .val (.word q2'), .val (.word q3')] :=
          (Option.some.inj ((hvq.symm.trans hresv).trans hv0t)).symm
        exact hclass q0' q1' q2' q3' (hv0lk.trans (congrArg some hv0v'))

/-- The `sat_word` call normalizing the gas value. -/
theorem callcodeGw_g10 {F : Type} {s0 : PanSemStateFiniteExact 64 F} {cont : ProgHOL 64}
    (hcont : HandlerRunA s0 (fun t => CcDLQ_g10 s0 t) true cont) :
    HandlerRunA s0 (fun t => CcDLQ_g10 s0 t) true
      (.decCall (ofString "gw") .one (ofString "sat_word")
        [.var .local (ofString "gasv")] cont) := by
  refine HandlerRunA.decCall epsA_sat_word (Q := fun t => CcDLQ_g10 s0 t) ?_ ?_ hcont
  · intro t values body' callee ret' hc hi hw hp hargs hl
    exact trivial
  · intro t values body callee retShape v cpost hi hw hp hargs hl hi_cp hw_cp hch_cp hQc
    obtain ⟨hmem, hglob⟩ := locFrame_pins_g10 hQc
    have hge : cpost.globals = t.globals := hglob
    have hRr : evmR (setVarHOLFinite (ofString "gw") v { cpost with locals := t.locals })
        = evmR cpost := (evm_congr (s := cpost)
          (t := setVarHOLFinite (ofString "gw") v { cpost with locals := t.locals }) rfl rfl).2.1
    refine CcDLQ_lu_g10 (lu6_setVarRes_ne_g10 t cpost (ofString "gw") v (by decide)) ?_ ?_ ?_ hp
    · exact le_of_eq (hRr.trans ((evmR_congr_full_g10 hQc).trans evmR_entry_eq_g10))
    · exact globN_congr_g10 hge "ev"
    · have h := locFrame_mem32_g10 hQc
      rw [globN_congr_g10 hge "ev"] at h
      exact h

/-- The `ext_code_of` call fetching the code size. -/
theorem callcodeCode_g10 {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    (hW : WorldAccountSpecsA)
    (hgc : EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "generic_call")) {cont : ProgHOL 64}
    (hcont : HandlerRunA s0 (fun t => CcDLQ_g10 s0 t) true cont) :
    HandlerRunA s0 (fun t => CcDLQ_g10 s0 t) true
      (.decCall (ofString "code") (.comb [.one, .one]) (ofString "ext_code_of")
        [.var .local (ofString "code_address")] cont) := by
  refine HandlerRunA.decCall hW.epsA_ext_code_of (Q := fun t => CcDLQ_g10 s0 t) ?_ ?_ hcont
  · intro t values body' callee ret' hc hi hw hp hargs hl
    exact trivial
  · intro t values body callee retShape v cpost hi hw hp hargs hl hi_cp hw_cp hch_cp hQc
    obtain ⟨hgk, hRev, hm32⟩ := hQc
    have hRr : evmR (setVarHOLFinite (ofString "code") v { cpost with locals := t.locals })
        = evmR cpost := (evm_congr (s := cpost)
          (t := setVarHOLFinite (ofString "code") v { cpost with locals := t.locals }) rfl rfl).2.1
    refine CcDLQ_lu_g10 (lu6_setVarRes_ne_g10 t cpost (ofString "code") v (by decide)) ?_ ?_ ?_ hp
    · exact le_of_eq (hRr.trans (hRev.trans evmR_entry_eq_g10))
    · exact (globN_of_lookup_eq_g10 "ev" (hgk (ofString "ev") (by decide)).symm)
    · exact hm32

/-- The `dl`-record warm-up ite: when the delegation is active, charge the
delegation cost and warm the (possibly different) effective code address. -/
theorem callcodeDlIte_g10 {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    (hW : WorldAccountSpecsA)
    (hgc : EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "generic_call")) {cont : ProgHOL 64}
    (hcont : HandlerRunA s0 (fun t => CcDLQ_g10 s0 t) true cont) :
    HandlerRunA s0 (fun t => CcDLQ_g10 s0 t) true
      (.seq
        (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "dl")))
            (.const (BitVec.ofNat 64 0)))
          (.seq (.call (some (none, none)) (ofString "charge_gas")
              [.rfield 2 (.var .local (ofString "dl"))])
            (.call (some (none, none)) (ofString "warm_address")
              [.var .local (ofString "code_address")]))
          .skip)
        cont) := by
  refine HandlerRunA.seq_ite_unit (fun t w heval hw0 => ?_) (fun t heval => ?_)
  · refine HandlerRunA.seq_assoc ?_
    refine HandlerRunA.seq_call (epsA_keepR_g10 epsA_charge_gas_keep32)
      (Q := fun t => CcDLQ_g10 s0 t) ?_ ?_ ?_
    · intro t values body' callee ret' hc hi hw hp hargs hl
      exact trivial
    · intro t values body callee retShape v cpost hi hw hp hargs hl hi_cp hw_cp hch_cp hQc
      obtain ⟨⟨hglob_cp, hmem32⟩, hR_cp⟩ := hQc
      have hRr : evmR { cpost with locals := t.locals } = evmR cpost :=
        (evm_congr (s := cpost) (t := { cpost with locals := t.locals }) rfl rfl).2.1
      rw [evmR_entry_eq_g10] at hR_cp
      refine CcDLQ_lu_g10 (t := t) (r := { cpost with locals := t.locals })
        (fun nm' _ => rfl) ?_ ?_ ?_ hp
      · rw [hRr]; exact hR_cp
      · exact globN_congr_g10 hglob_cp "ev"
      · exact hmem32
    · refine HandlerRunA.seq_call Group10.epsA_warm_address_keep32_g10
        (Q := fun t => CcDLQ_g10 s0 t) ?_ ?_ ?_
      · intro t values body' callee ret' hc hi hw hp hargs hl
        exact trivial
      · intro t values body callee retShape v cpost hi hw hp hargs hl hi_cp hw_cp hch_cp hQc
        obtain ⟨hgk, hRev, hm32⟩ := hQc
        have hRr : evmR { cpost with locals := t.locals } = evmR cpost :=
          (evm_congr (s := cpost) (t := { cpost with locals := t.locals }) rfl rfl).2.1
        refine CcDLQ_lu_g10 (t := t) (r := { cpost with locals := t.locals })
          (fun nm' _ => rfl) ?_ ?_ ?_ hp
        · exact le_of_eq (hRr.trans (hRev.trans evmR_entry_eq_g10))
        · exact (globN_of_lookup_eq_g10 "ev" (hgk (ofString "ev") (by decide)).symm)
        · exact hm32
      · exact hcont
  · exact HandlerRunA.seq_skip hcont

/-- The `code_address` `dec` selecting the effective-code second `dl` word. -/
theorem callcodeCodeAddr_g10 {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    (hW : WorldAccountSpecsA)
    (hgc : EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "generic_call")) {cont : ProgHOL 64}
    (hcont : HandlerRunA s0 (fun t => CcDLQ_g10 s0 t) true cont) :
    HandlerRunA s0 (fun t => CcDLQ_g10 s0 t) true
      (.dec (ofString "code_address") .one (.rfield 1 (.var .local (ofString "dl")))
        (.seq
          (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "dl")))
              (.const (BitVec.ofNat 64 0)))
            (.seq (.call (some (none, none)) (ofString "charge_gas")
                [.rfield 2 (.var .local (ofString "dl"))])
              (.call (some (none, none)) (ofString "warm_address")
                [.var .local (ofString "code_address")]))
            .skip)
          cont)) :=
  HandlerRunA.dec_carry_g10 (fun t v hp => CcDLQ_setVar_g10 (by decide) hp)
    (callcodeDlIte_g10 hW hgc hcont)

/-- The `calculate_delegation_cost` call. -/
theorem callcodeDl_g10 {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    (hW : WorldAccountSpecsA)
    (hgc : EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "generic_call")) {cont : ProgHOL 64}
    (hcont : HandlerRunA s0 (fun t => CcDLQ_g10 s0 t) true cont) :
    HandlerRunA s0 (fun t => CcPQ_g10 s0 t) true
      (.decCall (ofString "dl") (.comb [.one, .one, .one])
          (ofString "calculate_delegation_cost")
        [.var .local (ofString "code_address0")] cont) := by
  refine HandlerRunA.decCall (epsA_cdc_full_g10 hW) (Q := fun t => CcDLQ_g10 s0 t) ?_ ?_ hcont
  · intro t values body' callee ret' hc hi hw hp hargs hl
    exact trivial
  · intro t values body callee retShape v cpost hi hw hp hargs hl hi_cp hw_cp hch_cp hQc
    obtain ⟨hpins, hRev, d0, d1, d2, hv, hdc1, hdc2⟩ := hQc
    obtain ⟨hgev, hm32, _⟩ := hpins v rfl
    have hRr : evmR (setVarHOLFinite (ofString "dl") v { cpost with locals := t.locals })
        = evmR cpost := (evm_congr (s := cpost)
          (t := setVarHOLFinite (ofString "dl") v { cpost with locals := t.locals }) rfl rfl).2.1
    refine ⟨CcPQ_lu5_g10 (lu5_setVarRes_ne_g10 t cpost (ofString "dl") v (by decide))
      (by rw [hRr, hRev, evmR_entry_eq_g10]) hgev hm32 hp, d0, d1, d2, ?_, hdc1, hdc2⟩
    dsimp only [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    first | rw [if_pos rfl, hv] | simp [hv]

/-- The warm-ite on the pre-computed `warm` flag. -/
theorem callcodeWarmIte_g10 {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    (hW : WorldAccountSpecsA)
    (hgc : EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "generic_call")) {cont : ProgHOL 64}
    (hcont : HandlerRunA s0 (fun t => CcPQ_g10 s0 t) true cont) :
    HandlerRunA s0 (fun t => CcPQ_g10 s0 t) true
      (.seq
        (.ite (.cmp .equal (.var .local (ofString "warm")) (.const (BitVec.ofNat 64 0)))
          (.call (some (none, none)) (ofString "warm_address")
            [.var .local (ofString "code_address0")])
          .skip)
        cont) := by
  refine HandlerRunA.seq_ite_unit (fun t w heval hw0 => ?_) (fun t heval => ?_)
  · refine HandlerRunA.seq_call Group10.epsA_warm_address_keep32_g10
      (Q := fun t => CcPQ_g10 s0 t) ?_ ?_ ?_
    · intro t values body' callee ret' hc hi hw hp hargs hl
      exact trivial
    · intro t values body callee retShape v cpost hi hw hp hargs hl hi_cp hw_cp hch_cp hQc
      obtain ⟨hgk, hRev, hm32⟩ := hQc
      have hRr : evmR { cpost with locals := t.locals } = evmR cpost :=
        (evm_congr (s := cpost) (t := { cpost with locals := t.locals }) rfl rfl).2.1
      exact CcPQ_lu5_g10 (t := t) (r := { cpost with locals := t.locals })
        (fun nm' _ => rfl)
        (le_of_eq (hRr.trans (hRev.trans evmR_entry_eq_g10)))
        ((globN_of_lookup_eq_g10 "ev" (hgk (ofString "ev") (by decide)).symm)) hm32 hp
    · exact hcont
  · exact HandlerRunA.seq_skip hcont

/-- The `op_callcode` tail: everything after the prefix's `charge_gas [need]`. -/
theorem op_callcode_tail_g10 {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    (hW : WorldAccountSpecsA)
    (hgc : EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "generic_call")) :
    HandlerRunA s0 (fun t => CcPQ_g10 s0 t) true callcodeTailProg_g10 := by
  simp only [callcodeTailProg_g10]
  exact callcodeWarmIte_g10 hW hgc
    (callcodeDl_g10 hW hgc
      (callcodeCodeAddr_g10 hW hgc
        (callcodeCode_g10 hW hgc
          (callcodeGw_g10
            (callcodeMcg_g10
              (callcodeChargeMcg_g10
                (callcodeStore184_g10
                  (callcodeExtend_g10
                    (callcodeReservoir_g10
                      (callcodeStore72z_g10
                        (callcodeSender_g10 hW hgc
                          (callcodeInsufficient_g10 hgc
                            (callcodeStarted_g10 hgc
                              (callcodeInsfTail_g10 hgc))))))))))))))

/-- The full `op_callcode` run at the source body. -/
theorem op_callcode_run_full_g10 (hW : WorldAccountSpecsA)
    (hgc : EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "generic_call")) {F : Type} (s0 : PanSemStateFiniteExact 64 F) :
    HandlerRunA s0 (fun _ => EvmInv s0) false
      (sourceFnBody Guest.Software.guestFn_op_callcode) :=
  op_callcode_prefix_g10 (op_callcode_tail_g10 hW hgc)

/-- The `op_callcode` handler spec (guest AST index 604). -/
theorem op_callcode_specA_g10 (hW : WorldAccountSpecsA)
    (hgc : EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "generic_call")) :
    OpHandlerSpecA (ofString "op_callcode") := by
  refine opHandlerSpecA_of_run_seed_g10 604 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_op_callcode rfl ?_
  intro F s0 hInv0 hWF0 hnd0
  exact op_callcode_run_full_g10 hW hgc s0

end InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB
