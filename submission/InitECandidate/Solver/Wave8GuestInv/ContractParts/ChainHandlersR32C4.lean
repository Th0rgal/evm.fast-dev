import InitECandidate.Solver.Wave8GuestInv.ContractParts.ChainHandlersR32C1
import InitECandidate.Solver.Wave8GuestInv.ContractParts.ChainHandlersR32C2
import InitECandidate.Solver.Wave8GuestInv.ContractParts.ChainHandlersR32C3

/-! # Wave 8 R32 C4: the remaining chain-WF opcode walks

This shard carries the hard-tail opcode fields of `RemainingChainHandlersR32`
(the fields not closed by `ChainHandlersR32C2` (52 walks) and
`ChainHandlersR32C3` (`op_jump`/`op_jumpi`)):

* the memory family (`op_mload`, `op_mstore`, `op_mstore8`,
  `op_calldatacopy`, `op_codecopy`, `op_returndatacopy`, `op_extcodecopy`,
  `op_keccak`),
* the storage / transient family (`op_sload`, `op_sstore`, `op_tload`,
  `op_tstore`),
* the account family (`op_balance`, `op_selfbalance`, `op_extcodesize`,
  `op_extcodehash`),
* the environment family (`op_blockhash`),
* `op_calldataload`,
* and the bounded `op_push` (`nbytes ≤ 32`) / `op_log` (`ntopics ≤ 4`).

The stack-swap family (`op_swap`, `op_swapn`, `op_exchange`) is proved
unconditionally in this file (`op_swap_chainSpecR32`, `op_swapn_chainSpecR32`,
`op_exchange_chainSpecR32`), via an `EvmInvR32`-strength port of the R16
`eps_stack_swap_positions` walk (`epsA32_stack_swap_positions`): the swap
writes stay inside the head frame's stack region, which is a `frameObjects`
member disjoint from every chain frame's record cells, so the witness DB
(`witnessDbOK_of_scratchEff`) and the bridge chain-WF
(`Group09ChainWF.headMemChainWF_of_disj_bre`) are both preserved and the
globals never move.

`RemainingChainHandlersR32C4` bundles the still-open fields so the assembly
(`ChainHandlersR32C.remainingChainHandlersR32_of`) can merge them with the 57
proved fields (54 from C2/C3 plus the three swap walks here) into the full
77-field `RemainingChainHandlersR32`.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace InitECandidate.Solver.Wave8GuestInv.ContractParts.ChainHandlersR32C4

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R11Shards
open InitECandidate.Solver.Wave8GuestInv.R11Shards.OpDispatchSpec
open InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA
open InitECandidate.Solver.Wave8GuestInv.R16Shards
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.HeadMemBridge
open InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk
open InitECandidate.Solver.Wave8Contracts.M23
open InitECandidate.Solver.Wave8GuestInv.ContractParts.StrongBridges
open InitECandidate.Solver.Wave8GuestInv.ContractParts
open InitECandidate.Solver.Wave8GuestInv.ContractParts.ChainHandlersR32C1
open InitECandidate.Solver.Wave8GuestInv.ContractParts.ChainHandlersR32C2
open InitECandidate.Solver.Wave8GuestInv.ContractParts.ChainHandlersR32C3

/-! ## 1. Swap-family support -/

private def loadWordExp (base : ExpHOL 64) (off : BitVec 64) : ExpHOL 64 :=
  .load .one (.op .add [base, .const off])

private def struct4 : ShapeHOL := .comb [.one, .one, .one, .one]

/-- Symmetric-relation extraction from `List.Pairwise`: two distinct members
of a pairwise list are related (in either order). -/
private theorem pw_rel_of_mem {α : Type} {R : α → α → Prop} {L : List α}
    (hp : L.Pairwise R) {x y : α} (hx : x ∈ L) (hy : y ∈ L)
    (hsymm : ∀ a b : α, R a b → R b a) (hne : x ≠ y) : R x y := by
  induction L with
  | nil => cases hx
  | cons a t ih =>
    rcases List.mem_cons.1 hx with rfl | hx'
    · rcases List.mem_cons.1 hy with rfl | hy'
      · exact absurd rfl hne
      · exact (List.pairwise_cons.1 hp).1 _ hy'
    · rcases List.mem_cons.1 hy with rfl | hy'
      · exact hsymm _ _ ((List.pairwise_cons.1 hp).1 _ hx')
      · exact ih (List.pairwise_cons.1 hp).2 hx' hy'

private theorem stack_slot_in {F : Type} {s : PanSemStateFiniteExact 64 F} {S : List Nat}
    {stk sp item : BitVec 64}
    (_hA : ArenaOK s)
    (hFW : FrameWF s S (globN s "ev", globN s "cur_cont"))
    (hstk : stk.toNat = memW s (globN s "ev" + 8))
    (hsp : sp.toNat = memW s (globN s "ev" + 16))
    (hcap : memW s (globN s "ev" + 232) ≤ 1024)
    (hsp_le_cap : memW s (globN s "ev" + 16) ≤ memW s (globN s "ev" + 232))
    (hitem : item.toNat < sp.toNat) :
    let addr := stk + (sp - (1#64) - item) * (32#64)
    addr.toNat = stk.toNat + (sp.toNat - 1 - item.toNat) * 32 ∧
    stk.toNat ≤ addr.toNat ∧
    addr.toNat + 32 ≤ stk.toNat + 32 * memW s (globN s "ev" + 232) ∧
    addr.toNat + 32 ≤ 2 ^ 64 ∧
    addr.toNat % 8 = 0 := by
  intro addr
  have hstk_in := (hFW.1 (memW s (globN s "ev" + 8), 32 * memW s (globN s "ev" + 232)) (by simp)).1
  have hse : scratchEnd ≤ 2 ^ 64 := by rw [R11Shards.scratchEnd_val]; decide
  have hstk_bnd : memW s (globN s "ev" + 8) + 32 * memW s (globN s "ev" + 232) ≤ 2 ^ 64 :=
    le_trans hstk_in.2 hse
  have hstk8 : stk.toNat % 8 = 0 := by
    rw [hstk]
    exact (hFW.1 (memW s (globN s "ev" + 8), 32 * memW s (globN s "ev" + 232)) (by simp)).2.1
  have h1_lt : 1 ≤ sp.toNat := by omega
  have hsub1 : (sp - 1#64).toNat = sp.toNat - 1 := by
    rw [BitVec.toNat_sub_of_le]
    · rfl
    · rw [BitVec.le_def]; change 1 ≤ sp.toNat; omega
  have hsub2 : (sp - 1#64 - item).toNat = sp.toNat - 1 - item.toNat := by
    rw [BitVec.toNat_sub_of_le]
    · rw [hsub1]
    · rw [BitVec.le_def, hsub1]; omega
  have hmul : ((sp - 1#64 - item) * 32#64).toNat = (sp.toNat - 1 - item.toNat) * 32 := by
    have h32 : (32#64 : BitVec 64).toNat = 32 := rfl
    rw [BitVec.toNat_mul, hsub2, h32, Nat.mod_eq_of_lt (by omega)]
  have hadd : addr.toNat = stk.toNat + (sp.toNat - 1 - item.toNat) * 32 := by
    rw [BitVec.toNat_add, hmul, Nat.mod_eq_of_lt (by omega)]
  refine ⟨hadd, by omega, by omega, by omega, ?_⟩
  rw [hadd]
  omega

/-! ## 2. `epsA32_stack_swap_positions` -/

/-- `EvmInvR32`-strength port of `Group06Stack2.eps_stack_swap_positions`:
`stack_swap_positions` swaps two 32-byte slots inside the head frame's stack
region. The writes are confined to the stack `frameObjects` member (disjoint
from every chain frame's record cells by `EvmInvAt` pairwise disjointness), so
beyond the R16 `EvmInv` reconstruction the walk also preserves the witness DB
(`witnessDbOK_of_scratchEff` with `Rl = [oldStk]`) and the bridge chain-WF
(`Group09ChainWF.headMemChainWF_of_disj_bre`); the globals never move, so
`sysInside` transports. -/
theorem epsA32_stack_swap_positions :
    EvmPreservingSpecA32
      (fun s =>
        ∃ i j : BitVec 64,
          s.locals.lookup (ofString "i") = some (.val (.word i)) ∧
          s.locals.lookup (ofString "j") = some (.val (.word j)) ∧
          i.toNat < memW s (globN s "ev" + 16) ∧
          j.toNat < memW s (globN s "ev" + 16))
      (fun s _ post => post.globals = s.globals)
      (ofString "stack_swap_positions") := by
  refine ⟨_, _, _, lookup_stack_swap_positions, ?_⟩
  intro F s hcode hInv hWF hP _ hnt
  obtain ⟨iw, jw, hi_lk, hj_lk, hi_lt, hj_lt⟩ := hP
  have hno_ret_err {r0 : Option (PanSemResultExact 64)} {P1 P2 : Prop}
      (h1 : ∀ v, r0 ≠ some (.returned v)) (h2 : ¬ IsEvmErr r0) :
      (∀ v, r0 = some (.returned v) → P1) ∧ (IsEvmErr r0 → P2) :=
    ⟨fun v hv => (h1 v hv).elim, fun he => (h2 he).elim⟩
  have herr_triv {P1 P2 : Prop} :
      (∀ v, (some PanSemResultExact.error : Option (PanSemResultExact 64)) = some (.returned v) → P1) ∧
      (IsEvmErr (some PanSemResultExact.error) → P2) :=
    hno_ret_err (fun _ h => by cases h) (by rintro ⟨_, h⟩; cases h)
  have hbody : sourceFnBody Guest.Software.guestFn_stack_swap_positions =
      .dec (ofString "sp") .one (loadWordExp (.var .global (ofString "ev")) 16#64)
        (.dec (ofString "stk") .one (loadWordExp (.var .global (ofString "ev")) 8#64)
          (.dec (ofString "pa") .one
            (.op .add [.var .local (ofString "stk"),
              .panop .mul [.op .sub [.op .sub [.var .local (ofString "sp"), .const (1#64)],
                .var .local (ofString "i")], .const (32#64)]])
            (.dec (ofString "pb") .one
              (.op .add [.var .local (ofString "stk"),
                .panop .mul [.op .sub [.op .sub [.var .local (ofString "sp"), .const (1#64)],
                  .var .local (ofString "j")], .const (32#64)]])
              (.dec (ofString "a") struct4 (.load struct4 (.var .local (ofString "pa")))
                (.dec (ofString "b") struct4 (.load struct4 (.var .local (ofString "pb")))
                  (.seq (.store (.var .local (ofString "pa")) (.var .local (ofString "b")))
                    (.seq (.store (.var .local (ofString "pb")) (.var .local (ofString "a")))
                      (.return (.const (0#64)))))))))) := rfl
  dsimp only
  rw [hbody]
  have hhead_mem : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by
    simp [evmChain, evmChainFrom]
  have hFW0 := hInv.evmInv.2.choose_spec.2.2.2.2.1 _ hhead_mem
  have hb_ev := (frameWF_bounds hInv.evmInv.1.2 hFW0).1
  dsimp only at hb_ev
  have hsp_le_cap : memW s (globN s "ev" + 16) ≤ memW s (globN s "ev" + 232) := hFW0.2.2.2.2.1
  have hcap_ge1 : 1 ≤ memW s (globN s "ev" + 232) := hFW0.2.2.2.1
  have hcap_le1024 : memW s (globN s "ev" + 232) ≤ 1024 := hFW0.2.2.2.2.2.1
  -- Step 1: `dec "sp"`
  rw [evaluateHOLFiniteState_dec_total]; dsimp only
  rcases hload_sp : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (loadWordExp (.var .global (ofString "ev")) 16#64) with _ | vsp
  · simp only [hload_sp]; exact herr_triv
  · simp only [hload_sp]
    obtain ⟨spw, rfl, hspw_nat⟩ := evalAt_loadG_word s "ev" 16#64 vsp hload_sp
    have h16_n : (16#64 : BitVec 64).toNat = 16 := rfl
    rw [h16_n] at hspw_nat
    have hsh1_sp : shapeEqHOL .one (shapeOfHOLExact (.val (.word spw))) = true := by
      simp [shapeEqHOL, shapeOfHOLExact]
    rw [if_pos hsh1_sp]; dsimp only
    set s1 := setVarHOLFinite (ofString "sp") (.val (.word spw)) s with hs1
    -- Step 2: `dec "stk"`
    rw [evaluateHOLFiniteState_dec_total]; dsimp only
    rcases hload_stk : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
        (loadWordExp (.var .global (ofString "ev")) 8#64) with _ | vstk
    · simp only [hload_stk]; exact herr_triv
    · simp only [hload_stk]
      obtain ⟨stkw, rfl, hstkw_nat⟩ := evalAt_loadG_word s1 "ev" 8#64 vstk hload_stk
      have h8_n : (8#64 : BitVec 64).toNat = 8 := rfl
      have hs1_gm8 : memW s1 (globN s1 "ev" + 8) = memW s (globN s "ev" + 8) := rfl
      rw [h8_n, hs1_gm8] at hstkw_nat
      have hsh1_stk : shapeEqHOL .one (shapeOfHOLExact (.val (.word stkw))) = true := by
        simp [shapeEqHOL, shapeOfHOLExact]
      rw [if_pos hsh1_stk]; dsimp only
      set s2 := setVarHOLFinite (ofString "stk") (.val (.word stkw)) s1 with hs2
      -- Step 3: `dec "pa"`
      rw [evaluateHOLFiniteState_dec_total]; dsimp only
      have hs2_sp : s2.locals.lookup (ofString "sp") = some (.val (.word spw)) := by
        simp [hs2, hs1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "stk" ≠ ofString "sp" by decide]
      have hs2_stk : s2.locals.lookup (ofString "stk") = some (.val (.word stkw)) := by
        simp [hs2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hs2_i : s2.locals.lookup (ofString "i") = some (.val (.word iw)) := by
        simp [hs2, hs1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hi_lk,
          show ofString "stk" ≠ ofString "i" by decide, show ofString "sp" ≠ ofString "i" by decide]
      let pa_w : BitVec 64 := stkw + (spw - 1#64 - iw) * 32#64
      have hpa_eval : @evalHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a))
          (.op .add [.var .local (ofString "stk"),
            .panop .mul [.op .sub [.op .sub [.var .local (ofString "sp"), .const (1#64)],
              .var .local (ofString "i")], .const (32#64)]]) =
          some (.val (.word pa_w)) := by
        simp [evalHOLExact, evalListHOLExact, hs2_stk, hs2_sp, hs2_i,
          wordOpHOL, wordOp, panOpHOL, valueIsWord, valueWord, pa_w]
      rw [hpa_eval]; dsimp only
      have hsh1_pa : shapeEqHOL .one (shapeOfHOLExact (.val (.word pa_w))) = true := by
        simp [shapeEqHOL, shapeOfHOLExact]
      rw [if_pos hsh1_pa]; dsimp only
      set s3 := setVarHOLFinite (ofString "pa") (.val (.word pa_w)) s2 with hs3
      -- Step 4: `dec "pb"`
      rw [evaluateHOLFiniteState_dec_total]; dsimp only
      have hs3_sp : s3.locals.lookup (ofString "sp") = some (.val (.word spw)) := by
        simp [hs3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs2_sp,
          show ofString "pa" ≠ ofString "sp" by decide]
      have hs3_stk : s3.locals.lookup (ofString "stk") = some (.val (.word stkw)) := by
        simp [hs3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs2_stk,
          show ofString "pa" ≠ ofString "stk" by decide]
      have hs3_j : s3.locals.lookup (ofString "j") = some (.val (.word jw)) := by
        simp [hs3, hs2, hs1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hj_lk,
          show ofString "pa" ≠ ofString "j" by decide,
          show ofString "stk" ≠ ofString "j" by decide,
          show ofString "sp" ≠ ofString "j" by decide]
      let pb_w : BitVec 64 := stkw + (spw - 1#64 - jw) * 32#64
      have hpb_eval : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
          (.op .add [.var .local (ofString "stk"),
            .panop .mul [.op .sub [.op .sub [.var .local (ofString "sp"), .const (1#64)],
              .var .local (ofString "j")], .const (32#64)]]) =
          some (.val (.word pb_w)) := by
        simp [evalHOLExact, evalListHOLExact, hs3_stk, hs3_sp, hs3_j,
          wordOpHOL, wordOp, panOpHOL, valueIsWord, valueWord, pb_w]
      rw [hpb_eval]; dsimp only
      have hsh1_pb : shapeEqHOL .one (shapeOfHOLExact (.val (.word pb_w))) = true := by
        simp [shapeEqHOL, shapeOfHOLExact]
      rw [if_pos hsh1_pb]; dsimp only
      set s4 := setVarHOLFinite (ofString "pb") (.val (.word pb_w)) s3 with hs4
      -- Step 5: `dec "a"`
      rw [evaluateHOLFiniteState_dec_total]; dsimp only
      rcases hload_a : @evalHOLExact 64 F _ s4.toExact (fun a => Classical.propDecidable (s4.memaddrs a))
          (.load struct4 (.var .local (ofString "pa"))) with _ | va
      · simp only [hload_a]; exact herr_triv
      · simp only [hload_a]
        by_cases hsha : shapeEqHOL struct4 (shapeOfHOLExact va) = true
        · rw [if_pos hsha]; dsimp only
          have hva4 : ∃ w0 w1 w2 w3 : BitVec 64,
              va = .rStruct [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3)] := by
            have hsh := hsha
            rw [shapeEqHOL_eq_true] at hsh
            rcases va with _ | fs | _
            · simp [struct4, shapeOfHOLExact] at hsh
            · simp only [struct4, shapeOfHOLExact, ShapeHOL.comb.injEq] at hsh
              rcases fs with _ | ⟨f0, _ | ⟨f1, _ | ⟨f2, _ | ⟨f3, _ | _⟩⟩⟩⟩
              · simp at hsh
              · simp at hsh
              · simp at hsh
              · simp at hsh
              · simp only [List.map, List.cons.injEq] at hsh
                obtain ⟨h0, h1, h2, h3, _⟩ := hsh
                rcases f0 with ⟨⟨w0⟩⟩ | _ | _ <;> simp [shapeOfHOLExact] at h0
                rcases f1 with ⟨⟨w1⟩⟩ | _ | _ <;> simp [shapeOfHOLExact] at h1
                rcases f2 with ⟨⟨w2⟩⟩ | _ | _ <;> simp [shapeOfHOLExact] at h2
                rcases f3 with ⟨⟨w3⟩⟩ | _ | _ <;> simp [shapeOfHOLExact] at h3
                exact ⟨w0, w1, w2, w3, rfl⟩
              · simp at hsh
            · simp [struct4, shapeOfHOLExact] at hsh
          obtain ⟨aw0, aw1, aw2, aw3, rfl⟩ := hva4
          set s5 := setVarHOLFinite (ofString "a")
            (.rStruct [.val (.word aw0), .val (.word aw1), .val (.word aw2), .val (.word aw3)]) s4 with hs5
          -- Step 6: `dec "b"`
          rw [evaluateHOLFiniteState_dec_total]; dsimp only
          rcases hload_b : @evalHOLExact 64 F _ s5.toExact (fun a => Classical.propDecidable (s5.memaddrs a))
              (.load struct4 (.var .local (ofString "pb"))) with _ | vb
          · simp only [hload_b]; exact herr_triv
          · simp only [hload_b]
            by_cases hshb : shapeEqHOL struct4 (shapeOfHOLExact vb) = true
            · rw [if_pos hshb]; dsimp only
              have hvb4 : ∃ w0 w1 w2 w3 : BitVec 64,
                  vb = .rStruct [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3)] := by
                have hsh := hshb
                rw [shapeEqHOL_eq_true] at hsh
                rcases vb with _ | fs | _
                · simp [struct4, shapeOfHOLExact] at hsh
                · simp only [struct4, shapeOfHOLExact, ShapeHOL.comb.injEq] at hsh
                  rcases fs with _ | ⟨f0, _ | ⟨f1, _ | ⟨f2, _ | ⟨f3, _ | _⟩⟩⟩⟩
                  · simp at hsh
                  · simp at hsh
                  · simp at hsh
                  · simp at hsh
                  · simp only [List.map, List.cons.injEq] at hsh
                    obtain ⟨h0, h1, h2, h3, _⟩ := hsh
                    rcases f0 with ⟨⟨w0⟩⟩ | _ | _ <;> simp [shapeOfHOLExact] at h0
                    rcases f1 with ⟨⟨w1⟩⟩ | _ | _ <;> simp [shapeOfHOLExact] at h1
                    rcases f2 with ⟨⟨w2⟩⟩ | _ | _ <;> simp [shapeOfHOLExact] at h2
                    rcases f3 with ⟨⟨w3⟩⟩ | _ | _ <;> simp [shapeOfHOLExact] at h3
                    exact ⟨w0, w1, w2, w3, rfl⟩
                  · simp at hsh
                · simp [struct4, shapeOfHOLExact] at hsh
              obtain ⟨bw0, bw1, bw2, bw3, rfl⟩ := hvb4
              set s6 := setVarHOLFinite (ofString "b")
                (.rStruct [.val (.word bw0), .val (.word bw1), .val (.word bw2), .val (.word bw3)]) s5 with hs6
              -- Slot bounds for `pa_w` and `pb_w`
              have hslot_i := stack_slot_in (item := iw) hInv.evmInv.1.2 hFW0 hstkw_nat hspw_nat hcap_le1024 hsp_le_cap
                (by rw [hspw_nat]; exact hi_lt)
              have hslot_j := stack_slot_in (item := jw) hInv.evmInv.1.2 hFW0 hstkw_nat hspw_nat hcap_le1024 hsp_le_cap
                (by rw [hspw_nat]; exact hj_lt)
              have hs6_pa : s6.locals.lookup (ofString "pa") = some (.val (.word pa_w)) := by
                simp [hs6, hs5, hs4, hs3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                  show ofString "b" ≠ ofString "pa" by decide,
                  show ofString "a" ≠ ofString "pa" by decide,
                  show ofString "pb" ≠ ofString "pa" by decide]
              have hs6_pb : s6.locals.lookup (ofString "pb") = some (.val (.word pb_w)) := by
                simp [hs6, hs5, hs4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                  show ofString "b" ≠ ofString "pb" by decide,
                  show ofString "a" ≠ ofString "pb" by decide]
              have hs6_a : s6.locals.lookup (ofString "a") =
                  some (.rStruct [.val (.word aw0), .val (.word aw1), .val (.word aw2), .val (.word aw3)]) := by
                simp [hs6, hs5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                  show ofString "b" ≠ ofString "a" by decide]
              have hs6_b : s6.locals.lookup (ofString "b") =
                  some (.rStruct [.val (.word bw0), .val (.word bw1), .val (.word bw2), .val (.word bw3)]) := by
                simp [hs6, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
              -- Step 7: `store pa b`
              rw [evaluateHOLFiniteState_seq_line780]
              rcases hst1 : evaluateHOLFiniteState s6
                  (.store (.var .local (ofString "pa")) (.var .local (ofString "b"))) with ⟨r1, m1⟩
              simp only [hst1]
              cases r1 with
              | some res1 =>
                have herr := store_some_eq_error' hst1; subst herr; dsimp only; exact herr_triv
              | none =>
                dsimp only
                let oldStk : Ivl := (memW s (globN s "ev" + 8), 32 * memW s (globN s "ev" + 232))
                have hd1 := ScratchByteEff.of_store_struct4 (s := s6) (Rl := [oldStk])
                  hInv.evmInv.1.1.memaddrs hst1
                  (fun v hv => by
                    change s6.locals.lookup (ofString "b") = some v at hv
                    rw [hs6_b] at hv; injection hv with hv'
                    exact ⟨bw0, bw1, bw2, bw3, hv'.symm⟩)
                  (fun addr hdst => by
                    change s6.locals.lookup (ofString "pa") = some (.val (.word addr)) at hdst
                    rw [hs6_pa] at hdst; injection hdst with hd1'; injection hd1' with hd2'; injection hd2' with hd3'
                    subst hd3'
                    exact ⟨hslot_i.2.2.2.1, oldStk, List.mem_singleton.2 rfl,
                      by dsimp only [oldStk]; rw [← hstkw_nat]; exact hslot_i.2.1,
                      by dsimp only [oldStk]; rw [← hstkw_nat]; exact hslot_i.2.2.1⟩)
                obtain ⟨heff1, hm1_loc, hm1_glob⟩ := hd1
                -- Step 8: `store pb a`
                rw [evaluateHOLFiniteState_seq_line780]
                rcases hst2 : evaluateHOLFiniteState m1
                    (.store (.var .local (ofString "pb")) (.var .local (ofString "a"))) with ⟨r2, m2⟩
                simp only [hst2]
                cases r2 with
                | some res2 =>
                  have herr := store_some_eq_error' hst2; subst herr; dsimp only; exact herr_triv
                | none =>
                  dsimp only
                  have hd2 := ScratchByteEff.of_store_struct4 (Rl := [oldStk])
                    (heff1.memaddrs.trans hInv.evmInv.1.1.memaddrs) hst2
                    (fun v hv => by
                      change m1.locals.lookup (ofString "a") = some v at hv
                      rw [hm1_loc, hs6_a] at hv; injection hv with hv'
                      exact ⟨aw0, aw1, aw2, aw3, hv'.symm⟩)
                    (fun addr hdst => by
                      change m1.locals.lookup (ofString "pb") = some (.val (.word addr)) at hdst
                      rw [hm1_loc, hs6_pb] at hdst; injection hdst with hd1'; injection hd1' with hd2'; injection hd2' with hd3'
                      subst hd3'
                      exact ⟨hslot_j.2.2.2.1, oldStk, List.mem_singleton.2 rfl,
                        by dsimp only [oldStk]; rw [← hstkw_nat]; exact hslot_j.2.1,
                        by dsimp only [oldStk]; rw [← hstkw_nat]; exact hslot_j.2.2.1⟩)
                  obtain ⟨heff2, hm2_loc, hm2_glob⟩ := hd2
                  -- Step 9: `return 0`
                  rw [evaluateHOLFiniteState_return]
                  have hc0_m2 : @evalHOLExact 64 F _ m2.toExact
                      (fun a => Classical.propDecidable (m2.memaddrs a)) (.const 0#64) =
                      some (.val (.word 0#64)) := rfl
                  simp only [hc0_m2]
                  have hsz0 : sizeOfShapeWithContextHOL m2.structs
                      (shapeOfHOLExact (.val (.word 0#64))) ≤ 32 := by
                    simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
                  rw [if_pos hsz0]; dsimp only
                  let post := {
                      {
                        {
                          {
                            {
                              { m2.emptyLocalsHOLFinite with
                              locals := m2.emptyLocalsHOLFinite.locals.resVarEq
                                (ofString "b", s5.locals.lookup (ofString "b")) } with
                            locals := (m2.emptyLocalsHOLFinite.locals.resVarEq
                              (ofString "b", s5.locals.lookup (ofString "b"))).resVarEq
                              (ofString "a", s4.locals.lookup (ofString "a")) } with
                          locals := ((m2.emptyLocalsHOLFinite.locals.resVarEq
                            (ofString "b", s5.locals.lookup (ofString "b"))).resVarEq
                              (ofString "a", s4.locals.lookup (ofString "a"))).resVarEq
                              (ofString "pb", s3.locals.lookup (ofString "pb")) } with
                        locals := (((m2.emptyLocalsHOLFinite.locals.resVarEq
                          (ofString "b", s5.locals.lookup (ofString "b"))).resVarEq
                            (ofString "a", s4.locals.lookup (ofString "a"))).resVarEq
                              (ofString "pb", s3.locals.lookup (ofString "pb"))).resVarEq
                              (ofString "pa", s2.locals.lookup (ofString "pa")) } with
                      locals := ((((m2.emptyLocalsHOLFinite.locals.resVarEq
                        (ofString "b", s5.locals.lookup (ofString "b"))).resVarEq
                          (ofString "a", s4.locals.lookup (ofString "a"))).resVarEq
                            (ofString "pb", s3.locals.lookup (ofString "pb"))).resVarEq
                            (ofString "pa", s2.locals.lookup (ofString "pa"))).resVarEq
                            (ofString "stk", s1.locals.lookup (ofString "stk")) } with
                    locals := (((((m2.emptyLocalsHOLFinite.locals.resVarEq
                      (ofString "b", s5.locals.lookup (ofString "b"))).resVarEq
                        (ofString "a", s4.locals.lookup (ofString "a"))).resVarEq
                          (ofString "pb", s3.locals.lookup (ofString "pb"))).resVarEq
                          (ofString "pa", s2.locals.lookup (ofString "pa"))).resVarEq
                          (ofString "stk", s1.locals.lookup (ofString "stk"))).resVarEq
                          (ofString "sp", s.locals.lookup (ofString "sp")) }
                  have hpost_glob : post.globals = s.globals := by
                    change m2.globals = s.globals
                    rw [hm2_glob, hm1_glob]; rfl
                  have hs_s6 : ScratchByteEff s s6 [oldStk] :=
                    ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩
                  have heff_old : ScratchByteEff s post [oldStk] :=
                    ((hs_s6.trans heff1).trans heff2).with_locals_clock post.locals m2.clock
                  have heff_full : ScratchByteEff s post [(0, 0), (globN s "ev", 280), oldStk] :=
                    heff_old.mono (fun x hx => by
                      simp only [List.mem_singleton] at hx; subst hx
                      exact ⟨oldStk, by simp, le_refl _, le_refl _⟩)
                  have hApost : ArenaReady post :=
                    ⟨guestInv_congr (s := s) heff_full.code heff_full.memaddrs
                      heff_full.shMemaddrs heff_full.baseAddr hInv.evmInv.1.1,
                     arenaOK_congr hpost_glob hInv.evmInv.1.2⟩
                  have hsc_le : globN post "scratch_ptr" ≤ globN s "scratch_ptr" := by
                    unfold globN; rw [hpost_glob]
                  have he0_eq : ∀ off, off + 8 ≤ 280 → off % 8 = 0 →
                      memW post (globN s "ev" + off) = memW s (globN s "ev" + off) := by
                    intro off hoff hoff8
                    unfold memW
                    rw [heff_old.cell_frame (BitVec.ofNat 64 (globN s "ev" + off))]
                    intro x hx
                    simp only [List.mem_singleton] at hx; subst hx
                    have htn : (BitVec.ofNat 64 (globN s "ev" + off)).toNat = globN s "ev" + off :=
                      Nat.mod_eq_of_lt (by omega)
                    rw [htn]
                    have he0_8 : (globN s "ev") % 8 = 0 := (hFW0.1 (globN s "ev", 280) (by simp)).2.1
                    have ha8 : (globN s "ev" + off) % 8 = 0 := by omega
                    have hold_8 : (memW s (globN s "ev" + 8)) % 8 = 0 :=
                      (hFW0.1 oldStk (by simp [oldStk])).2.1
                    have hpw_fo := hInv.evmInv.2.choose_spec.2.2.2.2.2.2.2.1
                    have hch_s : ∃ tl, evmChain s = (globN s "ev", globN s "cur_cont") :: tl := ⟨_, rfl⟩
                    obtain ⟨tl_s, hch_s_eq⟩ := hch_s
                    rw [hch_s_eq, List.map_cons, List.flatten_cons, List.pairwise_append] at hpw_fo
                    have hd_stk : Disj (globN s "ev", 280) oldStk := by
                      have hp0 := hpw_fo.1; unfold frameObjects at hp0
                      exact (List.pairwise_cons.1 hp0).1 _ (by simp [oldStk])
                    exact not_cellHits_of_disj_aligned (i := (globN s "ev", 280)) ha8 hold_8
                      (Nat.le_add_right _ off) (Nat.add_le_add_left hoff _) hd_stk
                  have hnew_stk :
                      ((0, 0).2 = 0 ∧ memW post (globN s "ev" + 8) = memW s (globN s "ev" + 8) ∧
                        memW post (globN s "ev" + 232) = memW s (globN s "ev" + 232)) ∨
                      ((0, 0).2 ≠ 0 ∧ (memW post (globN s "ev" + 8), 32 * memW post (globN s "ev" + 232)) = (0, 0)) :=
                    Or.inl ⟨rfl,
                      he0_eq 8 (by omega) (by omega),
                      he0_eq 232 (by omega) (by omega)⟩
                  have hcap_post :
                      1 ≤ memW post (globN s "ev" + 232) ∧
                      memW post (globN s "ev" + 16) ≤ memW post (globN s "ev" + 232) ∧
                      memW post (globN s "ev" + 232) ≤ 1024 := by
                    rw [he0_eq 16 (by omega) (by omega), he0_eq 232 (by omega) (by omega)]
                    exact ⟨hcap_ge1, hsp_le_cap, hcap_le1024⟩
                  obtain ⟨hInv_p, hch_p, hR_p⟩ := evmInv_of_head_stack_push hInv.evmInv hApost hsc_le
                    heff_full (Or.inl rfl)
                    (fun off hoff hoff8 _ _ _ => he0_eq off hoff hoff8)
                    hnew_stk hcap_post
                  -- R32 payload: witness DB, sysInside, bridge chain-WF
                  have holdStk_8 : oldStk.1 % 8 = 0 := (hFW0.1 oldStk (by simp [oldStk])).2.1
                  have hRl8 : ∀ x ∈ ([oldStk] : List Ivl), x.1 % 8 = 0 := by
                    intro x hx
                    simp only [List.mem_singleton] at hx; subst hx; exact holdStk_8
                  have hstk_fo : oldStk ∈ frameObjects s (globN s "ev", globN s "cur_cont") := by
                    show (memW s (globN s "ev" + 8), 32 * memW s (globN s "ev" + 232)) ∈
                      frameObjects s (globN s "ev", globN s "cur_cont")
                    simp [frameObjects]
                  have hRl_avoid : ∀ x ∈ ([oldStk] : List Ivl), x.2 = 0 ∨
                      ((x ∈ frameObjects s (globN s "ev", globN s "cur_cont") ∧
                        Inside x (globN s "scratch_ptr") scratchEnd) ∨
                      Inside x (globN post "scratch_ptr") (globN s "scratch_ptr")) := by
                    intro x hx
                    simp only [List.mem_singleton] at hx; subst hx
                    exact Or.inr (Or.inl ⟨hstk_fo, (hFW0.1 oldStk (by simp [oldStk])).1⟩)
                  have hdb_p : StorageCreateFinish.WitnessDbOK post :=
                    witnessDbOK_of_scratchEff hInv.evmInv hInv.witnessDbOK hApost heff_old hsc_le
                      hRl8 hRl_avoid
                  have hsys_p := sysInside_congr_globals hpost_glob hInv.sysInside
                  have hflat_pw : ((evmChain s).map (frameObjects s)).flatten.Pairwise Disj :=
                    hInv.evmInv.2.choose_spec.2.2.2.2.2.2.2.1
                  have hstk_flat : oldStk ∈ ((evmChain s).map (frameObjects s)).flatten :=
                    List.mem_flatten.2 ⟨frameObjects s (globN s "ev", globN s "cur_cont"),
                      List.mem_map.2 ⟨(globN s "ev", globN s "cur_cont"), hhead_mem, rfl⟩, hstk_fo⟩
                  have hdj : ∀ ec ∈ evmChain s, ∀ i ∈ ([oldStk] : List Ivl),
                      (i.2 = 0 ∨ Disj (ec.1, 280) i) ∧ (i.2 = 0 ∨ Disj (ec.2, 104) i) := by
                    intro ec hec i hi
                    simp only [List.mem_singleton] at hi; subst hi
                    have h280_flat : (ec.1, 280) ∈ ((evmChain s).map (frameObjects s)).flatten :=
                      List.mem_flatten.2 ⟨frameObjects s ec,
                        List.mem_map.2 ⟨ec, hec, rfl⟩, by simp [frameObjects]⟩
                    have h104_flat : (ec.2, 104) ∈ ((evmChain s).map (frameObjects s)).flatten :=
                      List.mem_flatten.2 ⟨frameObjects s ec,
                        List.mem_map.2 ⟨ec, hec, rfl⟩, by simp [frameObjects]⟩
                    have hne280 : ¬ (oldStk = (ec.1, 280)) := by
                      intro h
                      have h2 : (32 * memW s (globN s "ev" + 232) : Nat) = 280 :=
                        congrArg Prod.snd h
                      omega
                    have hne104 : ¬ (oldStk = (ec.2, 104)) := by
                      intro h
                      have h2 : (32 * memW s (globN s "ev" + 232) : Nat) = 104 :=
                        congrArg Prod.snd h
                      omega
                    exact ⟨Or.inr (pw_rel_of_mem hflat_pw h280_flat hstk_flat
                        (fun a b h => R11Shards.Disj.symm h) (fun h => hne280 h.symm)),
                      Or.inr (pw_rel_of_mem hflat_pw h104_flat hstk_flat
                        (fun a b h => R11Shards.Disj.symm h) (fun h => hne104 h.symm))⟩
                  have hwf_p : HeadMemBridge.HeadMemChainWF post :=
                    (headMemChainWF_g09_iff_bridge post).mp
                      (Group09ChainWF.headMemChainWF_of_disj_bre hInv.evmInv
                        ((headMemChainWF_g09_iff_bridge s).mpr hWF) hch_p
                        (congrFun (globN_congr hpost_glob) "ev")
                        (congrFun (globN_congr hpost_glob) "frame_mem_ptr")
                        hRl8 heff_old.cell_frame hdj)
                  exact ⟨fun _ _ => ⟨⟨⟨hInv_p, hdb_p, hsys_p⟩, hwf_p⟩, hch_p, le_of_eq hR_p, hpost_glob⟩,
                    by rintro ⟨_, h⟩; cases h⟩
            · rw [if_neg hshb]; dsimp only; exact herr_triv
        · rw [if_neg hsha]; dsimp only; exact herr_triv

/-! ## 3. `HandlerRunA32` wiring for the swap callee -/

/-- `EvmInvR32`-strength analogue of `Group06Stack3.seq_call_stack_swap`:
call `stack_swap_positions` with two word arguments that index the head stack
(strictly below `sp`), then continue. -/
private theorem seq_callA32_stack_swap {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {P : PanSemStateFiniteExact 64 F → Prop} {charged : Bool}
    {arg1 arg2 : ExpHOL 64} {cont : ProgHOL 64}
    (hargs_ok : ∀ t (w1 w2 : BitVec 64),
      EvmInvR32 t → P t →
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) arg1 =
        some (.val (.word w1)) →
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) arg2 =
        some (.val (.word w2)) →
      w1.toNat < memW t (globN t "ev" + 16) ∧ w2.toNat < memW t (globN t "ev" + 16))
    (hcont : HandlerRunA32 s0 (fun _ => True) charged cont) :
    HandlerRunA32 s0 P charged
      (.seq (.call (some (none, none)) (ofString "stack_swap_positions") [arg1, arg2]) cont) := by
  refine HandlerRunA32.seq_call epsA32_stack_swap_positions ?_ (by intros; trivial) hcont
  intro t values body' callee ret' hc hi hwf hP hargs hl
  have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "stack_swap_positions") values =
      some (body', callee, ret') := by rwa [← hc]
  obtain ⟨_, _, w1, w2, rfl, hw1_cal, hw2_cal⟩ :=
    two_word_arg_lookup (by decide) lookup_stack_swap_positions hl_orig
  rw [evalListHOLFinite_eq_toExact] at hargs
  simp only [evalListHOLExact] at hargs
  rcases he1 : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) arg1 with _ | u1
  · simp [he1] at hargs
  · rcases he2 : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) arg2 with _ | u2
    · simp [he1, he2] at hargs
    · simp only [he1, he2, Option.some.injEq, List.cons.injEq, and_true] at hargs
      rcases hargs with ⟨rfl, rfl⟩
      obtain ⟨h1_lt, h2_lt⟩ := hargs_ok t w1 w2 hi hP he1 he2
      exact ⟨w1, w2, hw1_cal, hw2_cal, h1_lt, h2_lt⟩

/-! ## 4. Ite-bound helpers (ports of `Group06Stack3` privates) -/

private theorem eval_cmp_eq {F : Type} (t : PanSemStateFiniteExact 64 F)
    (op : Cmp) (e1 e2 : ExpHOL 64) :
    @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) (.cmp op e1 e2) =
    match @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) e1,
          @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) e2 with
    | some (.val (.word lw)), some (.val (.word rw)) =>
      some (.val (.word (if Compiler.Encoders.Asm.wordCmpHOL op lw rw then 1#64 else 0#64)))
    | _, _ => none := by
  simp only [evalHOLExact]
  rcases @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) e1 with _ | ⟨⟨w1⟩ | _⟩ | _ | _ <;>
  rcases @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) e2 with _ | ⟨⟨w2⟩ | _⟩ | _ | _ <;>
  rfl

private theorem eval_notLower_var_loadG_eq_zero {F : Type}
    (t : PanSemStateFiniteExact 64 F) (nm : MlS) (g : String) (off : BitVec 64)
    (hw : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
      (.cmp .notLower (.var .local nm)
        (.load .one (.op .add [.var .global (ofString g), .const off]))) =
      some (.val (.word 0#64))) :
    ∃ xw : BitVec 64, t.locals.lookup nm = some (.val (.word xw)) ∧
      xw.toNat < memW t (globN t g + off.toNat) := by
  rw [eval_cmp_eq] at hw
  have hvar : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
      (.var .local nm) = t.locals.lookup nm := rfl
  rw [hvar] at hw
  rcases hr : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
      (.load .one (.op .add [.var .global (ofString g), .const off])) with _ | rv
  · rw [hr] at hw
    rcases hl : t.locals.lookup nm with _ | lv
    · rw [hl] at hw; cases hw
    · rw [hl] at hw
      rcases lv with ⟨⟨_⟩ | _⟩ | _ | _ <;> cases hw
  · obtain ⟨spw, rfl, hsp_nat⟩ := evalAt_loadG_word t g off rv hr
    rw [hr] at hw
    rcases hl : t.locals.lookup nm with _ | lv
    · rw [hl] at hw; cases hw
    · rw [hl] at hw
      rcases lv with ⟨⟨xw⟩⟩ | _ | _
      · dsimp only at hw
        simp only [Compiler.Encoders.Asm.wordCmpHOL] at hw
        by_cases hle : spw ≤ xw
        · simp [hle] at hw
        · rw [BitVec.le_def] at hle
          exact ⟨xw, rfl, by omega⟩
      · cases hw
      · cases hw

private theorem eval_lower_loadG_add1_eq_zero {F : Type}
    (t : PanSemStateFiniteExact 64 F) (g : String) (off : BitVec 64) (nm : MlS)
    {xw : BitVec 64} (hx : t.locals.lookup nm = some (.val (.word xw))) (hx_le : xw.toNat ≤ 255)
    (hw : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
      (.cmp .lower (.load .one (.op .add [.var .global (ofString g), .const off]))
        (.op .add [.var .local nm, .const 1#64])) =
      some (.val (.word 0#64))) :
    xw.toNat < memW t (globN t g + off.toNat) := by
  have hadd_ev : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
      (.op .add [.var .local nm, .const 1#64]) = some (.val (.word (xw + 1#64))) := by
    simp [evalHOLExact, evalListHOLExact, hx, valueIsWord, valueWord, wordOpHOL, wordOp]
  rw [eval_cmp_eq, hadd_ev] at hw
  rcases hld : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
      (.load .one (.op .add [.var .global (ofString g), .const off])) with _ | lv
  · rw [hld] at hw; cases hw
  · obtain ⟨spw, rfl, hsp_nat⟩ := evalAt_loadG_word t g off lv hld
    rw [hld] at hw; dsimp only at hw
    simp only [Compiler.Encoders.Asm.wordCmpHOL] at hw
    by_cases hlt : spw < xw + 1#64
    · simp [hlt] at hw
    · rw [BitVec.lt_def, BitVec.toNat_add] at hlt
      have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
      rw [h1, Nat.mod_eq_of_lt (by omega)] at hlt
      omega

/-! ## 5. Bounded `decode_single` at A32 strength -/

/-- Port of `Group06Stack3.eps_decode_single_bounded` at
`EvmPreservingSpecA32` strength: `decode_single` returns a word of at most
255. -/
theorem epsA32_decode_single_bounded :
    EvmPreservingSpecA32 (fun _ => True)
      (fun s v post => LocFrame s post ∧ ∃ nw : BitVec 64, v = .val (.word nw) ∧ nw.toNat ≤ 255)
      (ofString "decode_single") := by
  obtain ⟨params, body, retShape, hlk, hds⟩ := epsA32_decode_single
  have hlk_eq := ChainHandlersR32C2.lookup_decode_single.symm.trans hlk
  injection hlk_eq with hprod
  rcases Prod.mk.inj hprod with ⟨rfl, hprod2⟩
  rcases Prod.mk.inj hprod2 with ⟨hbody_eq, rfl⟩
  subst hbody_eq
  refine ⟨_, _, _, ChainHandlersR32C2.lookup_decode_single, ?_⟩
  intro F s hcode hInv hWF hP hlookup hnt
  have hs := hds s hcode hInv hWF hP hlookup hnt
  dsimp only at hs ⊢
  refine ⟨fun v hv => ?_, hs.2⟩
  obtain ⟨⟨h1a, h1b⟩, h2, h3, hlf⟩ := hs.1 v hv
  exact ⟨⟨h1a, h1b⟩, h2, h3, hlf, decode_single_body_bounded s v hv⟩

/-! ## 6. The swap-family walks -/

theorem op_swap_chainSpecR32 : OpHandlerChainSpecR32 (ofString "op_swap") := by
  refine opHandlerChainSpecR32_of_run 517 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_swap rfl ?_
  intro F s0 _ _ _
  dsimp only [Guest.Software.guestFn_op_swap, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine HandlerRunA32.seq_charge_gas_exact (Q := fun _ => True) ?_ ?_ ?_
  · intro t w hv _ _ _
    simp only [evalHOLExact] at hv
    injection hv with h1
    injection h1 with h2
    injection h2 with h3
    subst h3
    decide
  · intro t cpost amtw _ _ _ _ _ _ _ _ _ _
    trivial
  · refine HandlerRunA32.seq_ite_raise_skip
      (Q := fun t => ∃ itemw : BitVec 64,
        t.locals.lookup (ofString "item") = some (.val (.word itemw)) ∧
        itemw.toNat < memW t (globN t "ev" + 16))
      (fun t hw _ _ => by
        obtain ⟨itemw, hitem, hlt⟩ := eval_notLower_var_loadG_eq_zero t (ofString "item") "ev" 16#64 hw
        exact ⟨itemw, hitem, hlt⟩)
      ?_
    refine seq_callA32_stack_swap
      (fun t w1 w2 _ ⟨itemw, hitem, hlt⟩ he1 he2 => by
        simp only [evalHOLExact] at he1
        injection he1 with h1; injection h1 with h2; injection h2 with h3; subst h3
        change t.locals.lookup (ofString "item") = some (.val (.word w2)) at he2
        rw [hitem] at he2; injection he2 with h1; injection h1 with h2; injection h2 with h3; subst h3
        have h0 : (0#64 : BitVec 64).toNat = 0 := rfl
        exact ⟨by omega, hlt⟩)
      (HandlerRunA32.seq_call_simple epsA32_pc_add (HandlerRunA32.ret _))

theorem op_swapn_chainSpecR32 : OpHandlerChainSpecR32 (ofString "op_swapn") := by
  refine opHandlerChainSpecR32_of_run 521 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_swapn rfl ?_
  intro F s0 _ _ _
  dsimp only [Guest.Software.guestFn_op_swapn, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine HandlerRunA32.seq_charge_gas_exact (Q := fun _ => True) ?_ ?_ ?_
  · intro t w hv _ _ _
    simp only [evalHOLExact] at hv
    injection hv with h1
    injection h1 with h2
    injection h2 with h3
    subst h3
    decide
  · intro t cpost amtw _ _ _ _ _ _ _ _ _ _
    trivial
  · refine HandlerRunA32.decCall (Q := fun _ => True) epsA32_code_imm
      (by intros; trivial) (by intros; trivial) ?_
    refine HandlerRunA32.decCall
      (Q := fun t => ∃ nw : BitVec 64,
        t.locals.lookup (ofString "n") = some (.val (.word nw)) ∧ nw.toNat ≤ 255)
      epsA32_decode_single_bounded
      (by intros; trivial)
      (fun t values body callee retShape v cpost h1 h2 h3 h4 h5 h6 h7 h8 hqc => by
        obtain ⟨_, nw, hv, hnw_le⟩ := hqc
        subst hv
        exact ⟨nw, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE], hnw_le⟩)
      ?_
    refine HandlerRunA32.seq_ite_raise_skip
      (Q := fun t => ∃ nw : BitVec 64,
        t.locals.lookup (ofString "n") = some (.val (.word nw)) ∧
        nw.toNat < memW t (globN t "ev" + 16))
      (fun t hw _ ⟨nw, hnw, hnw_le⟩ =>
        ⟨nw, hnw, eval_lower_loadG_add1_eq_zero t "ev" 16#64 (ofString "n") hnw hnw_le hw⟩)
      ?_
    refine seq_callA32_stack_swap
      (fun t w1 w2 _ ⟨nw, hnw, hlt⟩ he1 he2 => by
        simp only [evalHOLExact] at he1
        injection he1 with h1; injection h1 with h2; injection h2 with h3; subst h3
        change t.locals.lookup (ofString "n") = some (.val (.word w2)) at he2
        rw [hnw] at he2; injection he2 with h1; injection h1 with h2; injection h2 with h3; subst h3
        have h0 : (0#64 : BitVec 64).toNat = 0 := rfl
        exact ⟨by omega, hlt⟩)
      (HandlerRunA32.seq_call_simple epsA32_pc_add (HandlerRunA32.ret _))

/-! ## 6b. `op_exchange` support: assign combinator, bounded eps lemmas -/

/-- `A32`-strength port of `HandlerRun.seq_assign_local`
(R14Shards/OpHandlersA/Common.lean): peeling a local `assign` node. -/
theorem HandlerRunA32.seq_assign_local {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {P Q : PanSemStateFiniteExact 64 F → Prop} {charged : Bool}
    {nm : MlS} {exp : ExpHOL 64} {cont : ProgHOL 64}
    (hasgn : ∀ t v,
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) exp = some v →
      EvmInvR32 t → HeadMemBridge.HeadMemChainWF t → P t → Q (setKvarHOLFinite .local nm v t))
    (hcont : HandlerRunA32 s0 Q charged cont) :
    HandlerRunA32 s0 P charged (.seq (.assign .local nm exp) cont) := by
  intro t hc hi hw hlen hR hP hnt
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign] at hnt ⊢
  revert hnt
  split
  · intro _; exact opDispatchChainPostR32_error s0 t
  · rename_i v hv
    split
    · dsimp only; intro hnt
      let t1 := setKvarHOLFinite .local nm v t
      have hi1 : EvmInvR32 t1 := localsFree_evmInvR32 t t1.locals t.clock hi
      have hw1 : HeadMemBridge.HeadMemChainWF t1 :=
        HeadMemBridge.headMemChainWF_locals t t1.locals t.clock hw
      have hc1 := evm_congr (s := t) (t := t1) rfl rfl
      have hR1 : if charged then evmR t1 < evmR s0 else evmR t1 ≤ evmR s0 := by
        rw [hc1.2.1]; exact hR
      exact opDispatchChainPostR32_congr_lcl rfl
        (hcont t1 hc hi1 hw1 (hc1.2.2.1.trans hlen) hR1 (hasgn t v hv hi hw hP) hnt)
    · intro _; exact opDispatchChainPostR32_error s0 t

private theorem eval_seq_seq {F : Type} (s : PanSemStateFiniteExact 64 F)
    (p1 p2 p3 : ProgHOL 64) :
    evaluateHOLFiniteState s (.seq (.seq p1 p2) p3) =
    evaluateHOLFiniteState s (.seq p1 (.seq p2 p3)) := by
  simp only [evaluateHOLFiniteState_seq_line780]
  rcases h1 : evaluateHOLFiniteState s p1 with ⟨r1, s1⟩
  cases r1 <;> rfl

/-- Port of `Group06Stack3.eps_code_imm_bounded` at `EvmPreservingSpecA32`
strength: `code_imm` returns a word of at most 255. -/
theorem epsA32_code_imm_bounded :
    EvmPreservingSpecA32 (fun _ => True)
      (fun s v post => LocFrame s post ∧ ∃ immw : BitVec 64, v = .val (.word immw) ∧ immw.toNat < 256)
      (ofString "code_imm") := by
  obtain ⟨params, body, retShape, hlk, hci⟩ := epsA32_code_imm
  have hlk_eq := lookup_code_imm.symm.trans hlk
  injection hlk_eq with hprod
  rcases Prod.mk.inj hprod with ⟨rfl, hprod2⟩
  rcases Prod.mk.inj hprod2 with ⟨hbody_eq, rfl⟩
  subst hbody_eq
  refine ⟨_, _, _, lookup_code_imm, ?_⟩
  intro F s hcode hInv hWF hP hlookup hnt
  have hs := hci s hcode hInv hWF hP hlookup hnt
  dsimp only at hs ⊢
  refine ⟨fun v hv => ?_, hs.2⟩
  obtain ⟨hInvWF, hch, hRe, hlf⟩ := hs.1 v hv
  exact ⟨hInvWF, hch, hRe, hlf, code_imm_body_bounded s v hv⟩

/-- `max` at `EvmPreservingSpecA32` strength with the argument-value refinement
of `Group06Stack2.eps_max`. -/
theorem epsA32_max_args :
    EvmPreservingSpecA32
      (fun s => ∃ aw bw : BitVec 64,
        s.locals.lookup (ofString "a") = some (.val (.word aw)) ∧
        s.locals.lookup (ofString "b") = some (.val (.word bw)))
      (fun s v post => LocFrame s post ∧
        ∀ aw bw : BitVec 64,
          s.locals.lookup (ofString "a") = some (.val (.word aw)) →
          s.locals.lookup (ofString "b") = some (.val (.word bw)) →
          ∃ rw : BitVec 64, v = .val (.word rw) ∧ rw.toNat = Nat.max aw.toNat bw.toNat)
      (ofString "max") := by
  obtain ⟨params, body, retShape, hlk, hro⟩ := epsA32_max
  have hlk_eq := lookup_max.symm.trans hlk
  injection hlk_eq with hprod
  rcases Prod.mk.inj hprod with ⟨rfl, hprod2⟩
  rcases Prod.mk.inj hprod2 with ⟨hbody_eq, rfl⟩
  subst hbody_eq
  refine ⟨_, _, _, lookup_max, ?_⟩
  intro F s hcode hInv hWF hP hlookup hnt
  have hs := hro s hcode hInv hWF trivial hlookup hnt
  dsimp only at hs ⊢
  refine ⟨fun v hv => ?_, hs.2⟩
  obtain ⟨hInvWF, hch, hRe, hlf⟩ := hs.1 v hv
  exact ⟨hInvWF, hch, hRe, hlf, fun aw bw ha hb => max_body_exact s ha hb v hv⟩

/-- `A32`-strength port of `Group06Stack3.op_exchange_tail`: the shared tail
after the two slot computations (`max` call, range check, swap, `pc_add`). -/
private theorem op_exchange_tailA32 {F : Type} (s0 : PanSemStateFiniteExact 64 F) :
    HandlerRunA32 s0
      (fun t => ∃ nw mw : BitVec 64,
        t.locals.lookup (ofString "n") = some (.val (.word nw)) ∧
        t.locals.lookup (ofString "m") = some (.val (.word mw)) ∧
        nw.toNat ≤ 255 ∧ mw.toNat ≤ 255)
      true
      (.decCall (ofString "mx") .one (ofString "max")
        [.var .local (ofString "n"), .var .local (ofString "m")]
        (.seq
          (.ite (.cmp .lower
              (.load .one (.op .add [.var .global (ofString "ev"), .const 16#64]))
              (.op .add [.var .local (ofString "mx"), .const 1#64]))
            (.raise (ofString "EvmErr") (.const 2#64))
            .skip)
          (.seq
            (.call (some (none, none)) (ofString "stack_swap_positions")
              [.var .local (ofString "n"), .var .local (ofString "m")])
            (.seq
              (.call (some (none, none)) (ofString "pc_add") [.const 2#64])
              (.return (.const 0#64)))))) := by
  refine HandlerRunA32.decCall
    (Q := fun t => ∃ nw mw mxw : BitVec 64,
      t.locals.lookup (ofString "n") = some (.val (.word nw)) ∧
      t.locals.lookup (ofString "m") = some (.val (.word mw)) ∧
      t.locals.lookup (ofString "mx") = some (.val (.word mxw)) ∧
      mxw.toNat = Nat.max nw.toNat mw.toNat ∧ mxw.toNat ≤ 255)
    epsA32_max_args
    (fun t values b_m callee rs_m hc hi hw ⟨nw, mw, hn, hm, _, _⟩ hargs hl => by
      have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "max") values =
          some (b_m, callee, rs_m) := by rwa [← hc]
      obtain ⟨_, _, w1, w2, _, hw1, hw2⟩ := two_word_arg_lookup (by decide) lookup_max hl_orig
      exact ⟨w1, w2, hw1, hw2⟩)
    (fun t values body callee retShape v cpost hInv hWF hP hargs hl_orig hInvP hWFP hch hqc => by
      obtain ⟨nw, mw, hn, hm, hn_le, hm_le⟩ := hP
      have hev_args : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
          [.var .local (ofString "n"), .var .local (ofString "m")] =
          some [.val (.word nw), .val (.word mw)] := by
        rw [evalListHOLFinite_eq_toExact]
        simp [evalListHOLExact, evalHOLExact, hn, hm]
      rw [hev_args] at hargs; injection hargs with hvs; subst hvs
      obtain ⟨_, _, w1, w2, hvs_eq, hw1, hw2⟩ := two_word_arg_lookup (by decide) lookup_max hl_orig
      simp only [List.cons.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq, and_true] at hvs_eq
      rcases hvs_eq with ⟨rfl, rfl⟩
      obtain ⟨_, hmax⟩ := hqc
      obtain ⟨mxw, rfl, hmx_nat⟩ := hmax nw mw hw1 hw2
      have hmx_le : mxw.toNat ≤ 255 := by
        rw [hmx_nat]; exact Nat.max_le.2 ⟨hn_le, hm_le⟩
      refine ⟨nw, mw, mxw, ?_, ?_, ?_, hmx_nat, hmx_le⟩
      · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn,
          show ofString "mx" ≠ ofString "n" by decide]
      · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hm,
          show ofString "mx" ≠ ofString "m" by decide]
      · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
    ?_
  refine HandlerRunA32.seq_ite_raise_skip
    (Q := fun t => ∃ nw mw : BitVec 64,
      t.locals.lookup (ofString "n") = some (.val (.word nw)) ∧
      t.locals.lookup (ofString "m") = some (.val (.word mw)) ∧
      nw.toNat < memW t (globN t "ev" + 16) ∧
      mw.toNat < memW t (globN t "ev" + 16))
    (fun t hw _ ⟨nw, mw, mxw, hn, hm, hmx, hmx_nat, hmx_le⟩ => by
      have hlt := eval_lower_loadG_add1_eq_zero t "ev" 16#64 (ofString "mx") hmx hmx_le hw
      have h16 : (16#64 : BitVec 64).toNat = 16 := rfl
      rw [h16] at hlt
      have hn_le_mx : nw.toNat ≤ mxw.toNat := by rw [hmx_nat]; exact Nat.le_max_left _ _
      have hm_le_mx : mw.toNat ≤ mxw.toNat := by rw [hmx_nat]; exact Nat.le_max_right _ _
      exact ⟨nw, mw, hn, hm, by omega, by omega⟩)
    ?_
  refine seq_callA32_stack_swap
    (fun t w1 w2 _ ⟨nw, mw, hn, hm, hn_lt, hm_lt⟩ he1 he2 => by
      change t.locals.lookup (ofString "n") = some (.val (.word w1)) at he1
      change t.locals.lookup (ofString "m") = some (.val (.word w2)) at he2
      rw [hn] at he1; injection he1 with h1; injection h1 with h2; injection h2 with h3; subst h3
      rw [hm] at he2; injection he2 with h1; injection h1 with h2; injection h2 with h3; subst h3
      exact ⟨hn_lt, hm_lt⟩)
    (HandlerRunA32.seq_call_simple epsA32_pc_add (HandlerRunA32.ret _))

theorem op_exchange_chainSpecR32 : OpHandlerChainSpecR32 (ofString "op_exchange") := by
  refine opHandlerChainSpecR32_of_run 522 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_op_exchange rfl ?_
  intro F s0 _ _ _
  dsimp only [Guest.Software.guestFn_op_exchange, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine HandlerRunA32.seq_charge_gas_const (by decide) (by decide) ?_
  refine HandlerRunA32.decCall
    (Q := fun t => ∃ immw : BitVec 64,
      t.locals.lookup (ofString "imm") = some (.val (.word immw)) ∧ immw.toNat < 256)
    epsA32_code_imm_bounded
    (fun _ _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨_, immw, hv, himm_lt⟩ => by
      subst hv
      exact ⟨immw, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE], himm_lt⟩)
    ?_
  refine HandlerRunA32.seq_ite_raise_skip
    (Q := fun t => ∃ immw : BitVec 64,
      t.locals.lookup (ofString "imm") = some (.val (.word immw)) ∧ immw.toNat < 256)
    (fun _ _ _ hP => hP)
    ?_
  refine HandlerRunA32.dec
    (Q := fun t => ∃ kw : BitVec 64,
      t.locals.lookup (ofString "k") = some (.val (.word kw)) ∧ kw.toNat < 256)
    (fun t v hv _ _ ⟨immw, himm, himm_lt⟩ => by
      have hev : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
          (.op .xor [.var .local (ofString "imm"), .const 143#64]) =
          some (.val (.word (immw ^^^ 143#64))) := by
        simp [evalHOLExact, evalListHOLExact, himm, valueIsWord, valueWord, wordOpHOL, wordOp]
      rw [hev] at hv; injection hv with hv'; subst hv'
      refine ⟨immw ^^^ 143#64, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE], ?_⟩
      rw [BitVec.toNat_xor]
      have h143 : (143#64 : BitVec 64).toNat = 143 := rfl
      rw [h143]
      exact Nat.xor_lt_two_pow (n := 8) himm_lt (by decide))
    ?_
  refine HandlerRunA32.dec
    (Q := fun t => ∃ kw qw : BitVec 64,
      t.locals.lookup (ofString "k") = some (.val (.word kw)) ∧
      t.locals.lookup (ofString "q") = some (.val (.word qw)) ∧
      kw.toNat < 256 ∧ qw.toNat < 16)
    (fun t v hv _ _ ⟨kw, hk, hk_lt⟩ => by
      have h4 : (4#64 : BitVec 64).toNat = 4 := rfl
      have hev : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
          (.shift .lsr (.var .local (ofString "k")) (.const 4#64)) =
          some (.val (.word (kw >>> (4 : Nat)))) := by
        simp [evalHOLExact, hk, wordShiftHOL, h4]
      rw [hev] at hv; injection hv with hv'; subst hv'
      refine ⟨kw, kw >>> (4 : Nat),
        by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hk,
          show ofString "q" ≠ ofString "k" by decide],
        by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE],
        hk_lt, ?_⟩
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      have : (2 ^ 4 : Nat) = 16 := rfl
      omega)
    ?_
  refine HandlerRunA32.dec
    (Q := fun t => ∃ qw rw : BitVec 64,
      t.locals.lookup (ofString "q") = some (.val (.word qw)) ∧
      t.locals.lookup (ofString "r") = some (.val (.word rw)) ∧
      qw.toNat < 16 ∧ rw.toNat < 16)
    (fun t v hv _ _ ⟨kw, qw, hk, hq, _, hq_lt⟩ => by
      have hev : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
          (.op .and [.var .local (ofString "k"), .const 15#64]) =
          some (.val (.word (kw &&& 15#64))) := by
        simp [evalHOLExact, evalListHOLExact, hk, valueIsWord, valueWord, wordOpHOL, wordOp]
      rw [hev] at hv; injection hv with hv'; subst hv'
      refine ⟨qw, kw &&& 15#64,
        by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hq,
          show ofString "r" ≠ ofString "q" by decide],
        by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE],
        hq_lt, ?_⟩
      rw [BitVec.toNat_and]
      have h15 : (15#64 : BitVec 64).toNat = 15 := rfl
      rw [h15]
      exact Nat.and_lt_two_pow (n := 4) (x := kw.toNat) (by decide))
    ?_
  refine HandlerRunA32.dec
    (Q := fun t => ∃ qw rw : BitVec 64,
      t.locals.lookup (ofString "q") = some (.val (.word qw)) ∧
      t.locals.lookup (ofString "r") = some (.val (.word rw)) ∧
      qw.toNat < 16 ∧ rw.toNat < 16)
    (fun t v hv _ _ ⟨qw, rw, hq, hr, hq_lt, hr_lt⟩ =>
      ⟨qw, rw,
        by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hq,
          show ofString "n" ≠ ofString "q" by decide],
        by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hr,
          show ofString "n" ≠ ofString "r" by decide],
        hq_lt, hr_lt⟩)
    ?_
  refine HandlerRunA32.dec
    (Q := fun t => ∃ qw rw : BitVec 64,
      t.locals.lookup (ofString "q") = some (.val (.word qw)) ∧
      t.locals.lookup (ofString "r") = some (.val (.word rw)) ∧
      qw.toNat < 16 ∧ rw.toNat < 16)
    (fun t v hv _ _ ⟨qw, rw, hq, hr, hq_lt, hr_lt⟩ =>
      ⟨qw, rw,
        by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hq,
          show ofString "m" ≠ ofString "q" by decide],
        by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hr,
          show ofString "m" ≠ ofString "r" by decide],
        hq_lt, hr_lt⟩)
    ?_
  intro t hc hInv hWF hlen hR ⟨qw, rw, hq, hr, hq_lt, hr_lt⟩ hnt
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt ⊢
  have hcmp : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
      (.cmp .lower (.var .local (ofString "q")) (.var .local (ofString "r"))) =
      some (.val (.word (if qw < rw then 1#64 else 0#64))) := by
    simp [evalHOLExact, hq, hr, Compiler.Encoders.Asm.wordCmpHOL]
  rw [hcmp] at hnt ⊢; dsimp only at hnt ⊢
  by_cases hqr : qw < rw
  · have h10 : ¬ ((1#64 : BitVec 64) = 0) := by decide
    simp only [hqr, ↓reduceIte, h10] at hnt ⊢
    rw [← evaluateHOLFiniteState_seq_line780, eval_seq_seq] at hnt ⊢
    refine (HandlerRunA32.seq_assign_local
      (P := fun u => ∃ qw rw : BitVec 64,
        u.locals.lookup (ofString "q") = some (.val (.word qw)) ∧
        u.locals.lookup (ofString "r") = some (.val (.word rw)) ∧
        qw.toNat < 16 ∧ rw.toNat < 16)
      (Q := fun u => ∃ nw rw : BitVec 64,
        u.locals.lookup (ofString "n") = some (.val (.word nw)) ∧
        u.locals.lookup (ofString "r") = some (.val (.word rw)) ∧
        nw.toNat ≤ 255 ∧ rw.toNat < 16)
      (fun u v hv _ _ ⟨qw, rw, hq, hr, hq_lt, hr_lt⟩ => by
        have hev : @evalHOLExact 64 F _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a))
            (.op .add [.var .local (ofString "q"), .const 1#64]) =
            some (.val (.word (qw + 1#64))) := by
          simp [evalHOLExact, evalListHOLExact, hq, valueIsWord, valueWord, wordOpHOL, wordOp]
        rw [hev] at hv; injection hv with hv'; subst hv'
        refine ⟨qw + 1#64, rw,
          by simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE],
          by simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hr,
            show ofString "n" ≠ ofString "r" by decide],
          ?_, hr_lt⟩
        rw [BitVec.toNat_add]
        have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
        rw [h1, Nat.mod_eq_of_lt (by omega)]; omega)
      (HandlerRunA32.seq_assign_local
        (Q := fun u => ∃ nw mw : BitVec 64,
          u.locals.lookup (ofString "n") = some (.val (.word nw)) ∧
          u.locals.lookup (ofString "m") = some (.val (.word mw)) ∧
          nw.toNat ≤ 255 ∧ mw.toNat ≤ 255)
        (fun u v hv _ _ ⟨nw, rw, hn, hr, hn_le, hr_lt⟩ => by
          have hev : @evalHOLExact 64 F _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a))
              (.op .add [.var .local (ofString "r"), .const 1#64]) =
              some (.val (.word (rw + 1#64))) := by
            simp [evalHOLExact, evalListHOLExact, hr, valueIsWord, valueWord, wordOpHOL, wordOp]
          rw [hev] at hv; injection hv with hv'; subst hv'
          refine ⟨nw, rw + 1#64,
            by simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn,
              show ofString "m" ≠ ofString "n" by decide],
            by simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE],
            hn_le, ?_⟩
          rw [BitVec.toNat_add]
          have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
          rw [h1, Nat.mod_eq_of_lt (by omega)]; omega)
        (op_exchange_tailA32 s0))) t hc hInv hWF hlen hR ⟨qw, rw, hq, hr, hq_lt, hr_lt⟩ hnt
  · have h00 : (0#64 : BitVec 64) = 0 := rfl
    simp only [hqr, h00, ↓reduceIte] at hnt ⊢
    rw [← evaluateHOLFiniteState_seq_line780, eval_seq_seq] at hnt ⊢
    refine (HandlerRunA32.seq_assign_local
      (P := fun u => ∃ qw rw : BitVec 64,
        u.locals.lookup (ofString "q") = some (.val (.word qw)) ∧
        u.locals.lookup (ofString "r") = some (.val (.word rw)) ∧
        qw.toNat < 16 ∧ rw.toNat < 16)
      (Q := fun u => ∃ nw qw : BitVec 64,
        u.locals.lookup (ofString "n") = some (.val (.word nw)) ∧
        u.locals.lookup (ofString "q") = some (.val (.word qw)) ∧
        nw.toNat ≤ 255 ∧ qw.toNat < 16)
      (fun u v hv _ _ ⟨qw, rw, hq, hr, hq_lt, hr_lt⟩ => by
        have hev : @evalHOLExact 64 F _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a))
            (.op .add [.var .local (ofString "r"), .const 1#64]) =
            some (.val (.word (rw + 1#64))) := by
          simp [evalHOLExact, evalListHOLExact, hr, valueIsWord, valueWord, wordOpHOL, wordOp]
        rw [hev] at hv; injection hv with hv'; subst hv'
        refine ⟨rw + 1#64, qw,
          by simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE],
          by simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hq,
            show ofString "n" ≠ ofString "q" by decide],
          ?_, hq_lt⟩
        rw [BitVec.toNat_add]
        have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
        rw [h1, Nat.mod_eq_of_lt (by omega)]; omega)
      (HandlerRunA32.seq_assign_local
        (Q := fun u => ∃ nw mw : BitVec 64,
          u.locals.lookup (ofString "n") = some (.val (.word nw)) ∧
          u.locals.lookup (ofString "m") = some (.val (.word mw)) ∧
          nw.toNat ≤ 255 ∧ mw.toNat ≤ 255)
        (fun u v hv _ _ ⟨nw, qw, hn, hq, hn_le, hq_lt⟩ => by
          have hev : @evalHOLExact 64 F _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a))
              (.op .sub [.const 29#64, .var .local (ofString "q")]) =
              some (.val (.word (29#64 - qw))) := by
            simp [evalHOLExact, evalListHOLExact, hq, valueIsWord, valueWord, wordOpHOL, wordOp]
          rw [hev] at hv; injection hv with hv'; subst hv'
          refine ⟨nw, 29#64 - qw,
            by simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn,
              show ofString "m" ≠ ofString "n" by decide],
            by simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE],
            hn_le, ?_⟩
          have h29 : (29#64 : BitVec 64).toNat = 29 := rfl
          rw [BitVec.toNat_sub_of_le (BitVec.le_def.2 (by omega)), h29]
          omega)
        (op_exchange_tailA32 s0))) t hc hInv hWF hlen hR ⟨qw, rw, hq, hr, hq_lt, hr_lt⟩ hnt

/-! ## 7. The remaining open bundle -/

/-- The remaining `RemainingChainHandlersR32` fields after the 54 walks of
`ChainHandlersR32C2`/`ChainHandlersR32C3` and the three swap-family walks of
this file: the memory, storage/transient, account, environment (`op_blockhash`)
and `op_calldataload` families, plus the bounded `op_push`/`op_log` chain
specs. Field types are verbatim the corresponding `RemainingChainHandlersR32`
fields. -/
structure RemainingChainHandlersR32C4 : Prop where
  op_keccak : OpHandlerChainSpecR32 (ofString "op_keccak")
  op_balance : OpHandlerChainSpecR32 (ofString "op_balance")
  op_calldataload : OpHandlerChainSpecR32 (ofString "op_calldataload")
  op_calldatacopy : OpHandlerChainSpecR32 (ofString "op_calldatacopy")
  op_codecopy : OpHandlerChainSpecR32 (ofString "op_codecopy")
  op_extcodesize : OpHandlerChainSpecR32 (ofString "op_extcodesize")
  op_extcodecopy : OpHandlerChainSpecR32 (ofString "op_extcodecopy")
  op_returndatacopy : OpHandlerChainSpecR32 (ofString "op_returndatacopy")
  op_extcodehash : OpHandlerChainSpecR32 (ofString "op_extcodehash")
  op_blockhash : OpHandlerChainSpecR32 (ofString "op_blockhash")
  op_selfbalance : OpHandlerChainSpecR32 (ofString "op_selfbalance")
  op_mload : OpHandlerChainSpecR32 (ofString "op_mload")
  op_mstore : OpHandlerChainSpecR32 (ofString "op_mstore")
  op_mstore8 : OpHandlerChainSpecR32 (ofString "op_mstore8")
  op_sload : OpHandlerChainSpecR32 (ofString "op_sload")
  op_sstore : OpHandlerChainSpecR32 (ofString "op_sstore")
  op_tload : OpHandlerChainSpecR32 (ofString "op_tload")
  op_tstore : OpHandlerChainSpecR32 (ofString "op_tstore")
  op_push : OpPushBoundedChainSpecR32
  op_log : OpLogBoundedChainSpecR32

end InitECandidate.Solver.Wave8GuestInv.ContractParts.ChainHandlersR32C4
