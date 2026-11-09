import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.Group10CallsCreatesTail4

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
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

/-! ## Milestone 6 (call family, part 5): `op_delegatecall`

`op_delegatecall` mirrors `op_staticcall` (Tail2): the same stack pops (minus
the value slot), the same warm/access-cost/need prefix on the (masked) code
address, and the same delegation tail.  The only structural difference is the
`generic_call` argument vector: delegatecall forwards the caller's message
fields (`msg+56` value word, `msg+16` sender, `msg+32` recipient) and clears
the two static-call flags. -/

/-! ### `op_delegatecall` compiled prefix (nodes 1-9) -/


theorem op_delegatecall_prefix1_g10 {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {charged : Bool} {cont : ProgHOL 64}
    (hcont : HandlerRunA s0 scXQ charged cont) :
    HandlerRunA s0 (fun _ => True) charged
      (.decCall (ofString "gasv") (.comb [.one, .one, .one, .one]) (ofString "stack_pop") []
        (.decCall (ofString "cav") (.comb [.one, .one, .one, .one]) (ofString "stack_pop") []
          (.decCall (ofString "code_address0") .one (ofString "to_address_masked") [.var .local (ofString "cav")]
            (.decCall (ofString "in_start") (.comb [.one, .one, .one, .one]) (ofString "stack_pop") []
              (.decCall (ofString "in_size") (.comb [.one, .one, .one, .one]) (ofString "stack_pop") []
                (.decCall (ofString "out_start") (.comb [.one, .one, .one, .one]) (ofString "stack_pop") []
                  (.decCall (ofString "out_size") (.comb [.one, .one, .one, .one]) (ofString "stack_pop") []
                    (.dec (ofString "msg") .one
                      (.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 112)]))
                      (.decCall (ofString "x") (.comb [.one, .one]) (ofString "extend_memory_cost2")
                        [.var .local (ofString "in_start"), .var .local (ofString "in_size"),
                          .var .local (ofString "out_start"), .var .local (ofString "out_size")]
                        cont))))))))) := by
  refine HandlerRunA.decCall_simple epsA_stack_pop_le_g10 ?_
  refine HandlerRunA.decCall_simple epsA_stack_pop_le_g10 ?_
  refine HandlerRunA.decCall_simple epsA_to_address_masked ?_
  refine HandlerRunA.decCall_simple epsA_stack_pop_le_g10 ?_
  refine HandlerRunA.decCall_simple epsA_stack_pop_le_g10 ?_
  refine HandlerRunA.decCall_simple epsA_stack_pop_le_g10 ?_
  refine HandlerRunA.decCall_simple epsA_stack_pop_le_g10 ?_
  refine HandlerRunA.dec_simple ?_
  refine HandlerRunA.decCall (hf := epsA_extend_memory_cost2) ?_ ?_ hcont
  · intros; trivial
  · intro t values body callee retShape v cpost _ _ _ _ _ _ _ _ hQc
    obtain ⟨hlf, cw, ebw, hv, hbd⟩ := hQc
    refine ⟨cw, ebw, ?_, ?_⟩
    · dsimp only [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      first
        | rw [if_pos rfl, hv]
        | simp [hv]
    · rw [hlf]
      exact hbd

/-! ### The `op_delegatecall` tail after the delegation branch -/

abbrev dcExtCodeProg_g10 : ProgHOL 64 :=
  .decCall (ofString "code") (.comb [.one, .one]) (ofString "ext_code_of")
    [.var .local (ofString "code_address")]
    (.decCall (ofString "gw") .one (ofString "sat_word") [.var .local (ofString "gasv")]
      (.decCall (ofString "mcg") (.comb [.one, .one]) (ofString "calculate_message_call_gas")
        [.rstruct [.const (BitVec.ofNat 64 0), .const (BitVec.ofNat 64 0),
            .const (BitVec.ofNat 64 0), .const (BitVec.ofNat 64 0)],
          .var .local (ofString "gw"),
          .load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 64)]),
          .const (BitVec.ofNat 64 0), .const (BitVec.ofNat 64 0)]
        (.seq (.call (some (none, none)) (ofString "charge_gas")
            [.rfield 0 (.var .local (ofString "mcg"))])
          (.seq (.store (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 184)])
              (.op .sub [.load .one
                  (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 184)]),
                .rfield 1 (.var .local (ofString "mcg"))]))
            (.seq (.call (some (none, none)) (ofString "extend_memory")
                [.rfield 1 (.var .local (ofString "x"))])
              (.dec (ofString "reservoir") .one
                (.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 72)]))
                (.seq (.store (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 72)])
                    (.const (BitVec.ofNat 64 0)))
                  (.decCall (ofString "is") .one (ofString "sat_word")
                    [.var .local (ofString "in_start")]
                    (.decCall (ofString "isz") .one (ofString "sat_word")
                      [.var .local (ofString "in_size")]
                      (.decCall (ofString "os") .one (ofString "sat_word")
                        [.var .local (ofString "out_start")]
                        (.decCall (ofString "osz") .one (ofString "sat_word")
                          [.var .local (ofString "out_size")]
                          (.decCall (ofString "started") .one (ofString "generic_call")
                            [.rfield 1 (.var .local (ofString "mcg")),
                              .var .local (ofString "reservoir"),
                              .load (.comb [.one, .one, .one, .one]) (.op .add [.var .local (ofString "msg"),
                                  .const (BitVec.ofNat 64 56)]),
                              .load .one (.op .add [.var .local (ofString "msg"),
                                  .const (BitVec.ofNat 64 16)]),
                              .load .one (.op .add [.var .local (ofString "msg"),
                                  .const (BitVec.ofNat 64 32)]),
                              .var .local (ofString "code_address"),
                              .const (BitVec.ofNat 64 0), .const (BitVec.ofNat 64 0),
                              .var .local (ofString "is"), .var .local (ofString "isz"),
                              .var .local (ofString "os"), .var .local (ofString "osz"),
                              .rfield 0 (.var .local (ofString "code")),
                              .rfield 1 (.var .local (ofString "code")),
                              .rfield 0 (.var .local (ofString "dl")),
                              .const (BitVec.ofNat 64 0)]
                            (.seq (.ite (.cmp .equal (.var .local (ofString "started"))
                                (.const (BitVec.ofNat 64 0)))
                              (.call (some (none, none)) (ofString "pc_add")
                                [.const (BitVec.ofNat 64 1)])
                              .skip)
                              (.return (.const (BitVec.ofNat 64 0))))))))))))))))

theorem dcExtCodeChain_ccA_g10 {F : Type} (hW : WorldAccountSpecsA)
    (hgc : EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "generic_call")) :
    @ChildContinuationA F scXQ dcExtCodeProg_g10 := by
  apply ccA_decCall_g10 (Q := scXQ) hW.epsA_ext_code_of
    (hentry := fun t values body' callee ret' _ _ _ _ _ _ => trivial)
  · intro t values body callee rs v cpost _ _ hp _ _ _ _ _ hQc
    obtain ⟨hgk, _, hm32⟩ := hQc
    refine scXQ_of_pins_g10 hp ?_
    rw [globN_of_lookup_eq_g10 "ev" (hgk (ofString "ev") (by decide)).symm]
    exact hm32
  apply ccA_decCall_g10 (Q := scXQ) epsA_sat_word
    (hentry := fun t values body' callee ret' _ _ _ _ _ _ => trivial)
  · intro t values body callee rs v cpost _ _ hp _ _ _ _ _ hQc
    exact scXQ_setvar_g10 (by decide) (scXQ_of_locFrame_call_g10 hp hQc)
  apply ccA_decCall_g10 (Q := scXQ) epsA_calculate_message_call_gas
    (hentry := fun t values body' callee ret' _ _ _ _ _ _ => trivial)
  · intro t values body callee rs v cpost _ _ hp _ _ _ _ _ hQc
    exact scXQ_setvar_g10 (by decide) (scXQ_of_locFrame_call_g10 hp hQc)
  apply ccA_seq_call_g10 (Q := scXQ) epsA_charge_gas_keep32
    (hentry := fun t values body callee rs _ _ _ _ _ _ => trivial)
  · intro t values body callee rs v cpost _ _ hp _ _ _ hQc
    obtain ⟨hglob, hm32⟩ := hQc
    refine scXQ_of_pins_g10 hp ?_
    rw [globN_congr_g10 hglob "ev"]
    exact hm32
  apply ccA_seq_store_ev_g10 (Q := scXQ) 184 (by decide)
    (hval := fun t v _ hv => eval_op_word_g10 _ _ v hv)
    (hstep := fun t w _ hi _ hp => scXQ_of_updW_g10 184 (by decide) (by decide) hi w hp)
  apply ccA_seq_call_g10 (Q := XShQ_g10) epsA_extend_memory
    (hentry := fun t values body callee rs hc hi hw hp ha hl =>
      memoryExpansionLocal_callee_pre_g10 t hc hw hp ha hl)
    (hstep := fun t values body callee rs v cpost _ _ hp _ _ _ hQc => by
      obtain ⟨cw, ebw, hxl, _⟩ := hp
      exact ⟨cw, ebw, hxl⟩)
  apply ccA_dec_g10 (Q := XShQ_g10)
    (hinit := fun t v _ _ hp => xShQ_setvar_g10 (by decide) hp)
  apply ccA_seq_store_ev_g10 (Q := XShQ_g10) 72 (by decide)
    (hval := fun t v _ hv => ⟨(BitVec.ofNat 64 0), eval_const_word_g10 _ v hv⟩)
    (hstep := fun t w _ _ _ hp => xShQ_of_updW_g10 72 w hp)
  apply ccA_decCall_g10 (Q := XShQ_g10) epsA_sat_word
    (hentry := fun t values body' callee ret' _ _ _ _ _ _ => trivial)
  · intro t values body callee rs v cpost _ _ hp _ _ _ _ _ hQc
    exact xShQ_setvar_g10 (by decide) hp
  apply ccA_decCall_g10 (Q := XShQ_g10) epsA_sat_word
    (hentry := fun t values body' callee ret' _ _ _ _ _ _ => trivial)
  · intro t values body callee rs v cpost _ _ hp _ _ _ _ _ hQc
    exact xShQ_setvar_g10 (by decide) hp
  apply ccA_decCall_g10 (Q := XShQ_g10) epsA_sat_word
    (hentry := fun t values body' callee ret' _ _ _ _ _ _ => trivial)
  · intro t values body callee rs v cpost _ _ hp _ _ _ _ _ hQc
    exact xShQ_setvar_g10 (by decide) hp
  apply ccA_decCall_g10 (Q := XShQ_g10) epsA_sat_word
    (hentry := fun t values body' callee ret' _ _ _ _ _ _ => trivial)
  · intro t values body callee rs v cpost _ _ hp _ _ _ _ _ hQc
    exact xShQ_setvar_g10 (by decide) hp
  apply ccA_decCall_g10 (Q := XShQ_g10) hgc
    (hentry := fun t values body' callee ret' _ _ _ _ _ _ => trivial)
  · intro t values body callee rs v cpost _ _ hp _ _ _ _ _ hQc
    exact xShQ_setvar_g10 (by decide) hp
  apply ccA_seq_ite_g10
  · intro t w _ _
    exact ccA_seq_call_g10 (Q := fun _ => True) epsA_pc_add
      (hentry := fun t values body callee rs _ _ _ _ _ _ => trivial)
      (hstep := fun t values body callee rs v cpost _ _ _ _ _ _ hQc => trivial)
      (ccA_ret_g10 (.const (BitVec.ofNat 64 0)))
  · intro t _
    exact ccA_seq_skip_g10 (ccA_ret_g10 (.const (BitVec.ofNat 64 0)))

theorem dcDlChain_ccA_g10 {F : Type} (hW : WorldAccountSpecsA)
    (hgc : EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "generic_call")) :
    @ChildContinuationA F scXQ
      (.decCall (ofString "dl") (.comb [.one, .one, .one])
        (ofString "calculate_delegation_cost") [.var .local (ofString "code_address0")]
        (.dec (ofString "code_address") .one (.rfield 1 (.var .local (ofString "dl")))
          (.seq (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "dl")))
              (.const (BitVec.ofNat 64 0)))
            (.seq (.call (some (none, none)) (ofString "charge_gas")
                [.rfield 2 (.var .local (ofString "dl"))])
              (.call (some (none, none)) (ofString "warm_address")
                [.var .local (ofString "code_address")]))
            .skip)
            dcExtCodeProg_g10))) := by
  apply ccA_decCall_g10 (Q := scXQ) (epsA_cdc_full_g10 hW)
    (hentry := fun t values body' callee ret' _ _ _ _ _ _ => trivial)
  · intro t values body callee rs v cpost _ _ hp _ _ _ _ _ hQc
    obtain ⟨hpins, _, _⟩ := hQc
    obtain ⟨hev, hm32, _⟩ := hpins v rfl
    refine scXQ_setvar_g10 (by decide) (scXQ_of_pins_g10 hp ?_)
    rw [hev]
    exact hm32
  apply ccA_dec_g10 (Q := scXQ)
    (hinit := fun t v _ _ hp => scXQ_setvar_g10 (by decide) hp)
  apply ccA_seq_ite_g10
  · intro t w _ _
    rw [ccA_seq_seq_assoc_g10]
    apply ccA_seq_call_g10 (Q := scXQ) epsA_charge_gas_keep32
      (hentry := fun t values body callee rs _ _ _ _ _ _ => trivial)
    · intro t values body callee rs v cpost _ _ hp _ _ _ hQc
      obtain ⟨hglob, hm32⟩ := hQc
      refine scXQ_of_pins_g10 hp ?_
      rw [globN_congr_g10 hglob "ev"]
      exact hm32
    · apply ccA_seq_call_g10 (Q := scXQ) Group10.epsA_warm_address_keep32_g10
        (hentry := fun t values body callee rs _ _ _ _ _ _ => trivial)
      · intro t values body callee rs v cpost _ _ hp _ _ _ hQc
        obtain ⟨hgk, _, hm32⟩ := hQc
        refine scXQ_of_pins_g10 hp ?_
        rw [globN_of_lookup_eq_g10 "ev" (hgk (ofString "ev") (by decide)).symm]
        exact hm32
      · exact dcExtCodeChain_ccA_g10 hW hgc
  · intro t _
    exact ccA_seq_skip_g10 (dcExtCodeChain_ccA_g10 hW hgc)

theorem dcRest_ccA_g10 {F : Type} (hW : WorldAccountSpecsA)
    (hgc : EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "generic_call")) :
    @ChildContinuationA F scXQ
      (.seq (.ite (.cmp .equal (.var .local (ofString "warm")) (.const (BitVec.ofNat 64 0)))
          (.call (some (none, none)) (ofString "warm_address") [.var .local (ofString "code_address0")])
          .skip)
        (.decCall (ofString "dl") (.comb [.one, .one, .one])
          (ofString "calculate_delegation_cost") [.var .local (ofString "code_address0")]
          (.dec (ofString "code_address") .one (.rfield 1 (.var .local (ofString "dl")))
            (.seq (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "dl")))
                (.const (BitVec.ofNat 64 0)))
              (.seq (.call (some (none, none)) (ofString "charge_gas")
                  [.rfield 2 (.var .local (ofString "dl"))])
                (.call (some (none, none)) (ofString "warm_address")
                  [.var .local (ofString "code_address")]))
              .skip)
              dcExtCodeProg_g10)))) := by
  apply ccA_seq_ite_g10
  · intro t w _ _
    exact ccA_seq_call_g10 (Q := scXQ) Group10.epsA_warm_address_keep32_g10
      (hentry := fun t values body callee rs _ _ _ _ _ _ => trivial)
      (hstep := fun t values body callee rs v cpost _ _ hp _ _ _ hQc => by
        obtain ⟨hgk, _, hm32⟩ := hQc
        refine scXQ_of_pins_g10 hp ?_
        rw [globN_of_lookup_eq_g10 "ev" (hgk (ofString "ev") (by decide)).symm]
        exact hm32)
      (dcDlChain_ccA_g10 hW hgc)
  · intro t _
    exact ccA_seq_skip_g10 (dcDlChain_ccA_g10 hW hgc)

/-! ### The `op_delegatecall` need chain (nodes 14-16) -/

theorem op_delegatecall_needChain_g10 {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {charged : Bool} {cont : ProgHOL 64} (hW : WorldAccountSpecsA)
    (hgc : EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "generic_call"))
    (hcont : HandlerRunA s0 scXQ true cont) :
    HandlerRunA s0 (fun s => scXQ s ∧ AcQ_g10 s) charged
      (.decCall (ofString "need") .one (ofString "add_sat")
        [.var .local (ofString "access_cost"), .rfield 0 (.var .local (ofString "x"))]
        (.seq (.call (some (none, none)) (ofString "charge_gas") [.var .local (ofString "need")])
          cont)) := by
  apply HandlerRunA.decCall (Q := fun s => scXQ s ∧ NdQ_g10 s) epsA_add_sat_ge_g10
    (hentry := fun t values body' callee ret' _ _ _ _ _ _ => trivial)
  · intro t values body callee rs v cpost hi hw hp hargs hlk hi2 hw2 hch hQc
    obtain ⟨hlf, aw, rw, hla, hvw, hle⟩ := hQc
    obtain ⟨acw, hl_ac, hac⟩ := hp.2
    obtain ⟨v0, v1, hv0_ev, hv1_ev, hvals⟩ : ∃ v0 v1,
        @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
          (.var .local (ofString "access_cost")) = some v0 ∧
        @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
          (.rfield 0 (.var .local (ofString "x"))) = some v1 ∧
        values = [v0, v1] := by
      rw [evalListHOLFinite_eq_toExact] at hargs
      simp only [evalListHOLExact] at hargs
      rcases he0 : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
          (.var .local (ofString "access_cost")) with _ | v0
      · simp [he0] at hargs
      rcases he1 : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
          (.rfield 0 (.var .local (ofString "x"))) with _ | v1
      · simp [he0, he1] at hargs
      simp only [he0, he1, Option.some.injEq] at hargs
      exact ⟨v0, v1, rfl, rfl, hargs.symm⟩
    subst hvals
    obtain ⟨w0, w1, hv0w, hv1w, hla0, _⟩ := add_sat_args_lookup_g10 hlk
    have hv0_acw : t.locals.lookup (ofString "access_cost") = some (.val (.word w0)) := by
      rw [← hv0w]; exact hv0_ev
    have hw0_acw : w0 = acw := by
      have h := hl_ac.symm.trans hv0_acw
      injection h with h1
      injection h1 with h2
      injection h2 with h3
      exact h3.symm
    have hla' : callee.lookup (ofString "a") = some (.val (.word aw)) := hla
    have haw : aw = w0 := by
      have h := hla'.symm.trans hla0
      injection h with h1
      injection h1 with h2
      injection h2 with h3
    have hle_nat : aw.toNat ≤ rw.toNat := hle
    rw [haw, hw0_acw] at hle_nat
    have h100 : 100 ≤ acw.toNat := by rcases hac with rfl | rfl <;> simp
    refine ⟨scXQ_setvar_g10 (by decide) (scXQ_of_locFrame_call_g10 hp.1 hlf), rw, ?_, ?_⟩
    · dsimp only [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      first | rw [if_pos rfl, hvw] | simp [hvw]
    · omega
  apply HandlerRunA.seq_charge_gas_keep32_g10 (Q := scXQ)
    (hpos := fun t w hv _ _ hp => by
      obtain ⟨nw, hlk_n, hbound⟩ := hp.2
      have hev : t.locals.lookup (ofString "need") = some (.val (.word w)) := hv
      rw [hlk_n] at hev
      injection hev with h1
      injection h1 with h2
      injection h2 with h3
      subst h3
      omega)
    (hstep := fun t cpost _ _ hp _ _ _ hm32 _ => scXQ_of_pins_g10 hp.1 hm32)
    (hcont := hcont)

/-! ### The `op_delegatecall` compiled prefix (nodes 10-16) -/

theorem op_delegatecall_prefix2_g10 {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {charged : Bool} {cont : ProgHOL 64} (hW : WorldAccountSpecsA)
    (hgc : EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "generic_call"))
    (hcont : HandlerRunA s0 scXQ true cont) :
    HandlerRunA s0 scXQ charged
      (.decCall (ofString "warm") .one (ofString "is_warm_address") [.var .local (ofString "code_address0")]
        (.dec (ofString "access_cost") .one (.const (BitVec.ofNat 64 100))
          (.seq (.ite (.cmp .equal (.var .local (ofString "warm")) (.const (BitVec.ofNat 64 0)))
              (.assign .local (ofString "access_cost") (.const (BitVec.ofNat 64 3000))) .skip)
            (.decCall (ofString "need") .one (ofString "add_sat")
              [.var .local (ofString "access_cost"), .rfield 0 (.var .local (ofString "x"))]
              (.seq (.call (some (none, none)) (ofString "charge_gas")
                [.var .local (ofString "need")]) cont))))) := by
  apply HandlerRunA.decCall (Q := scXQ) epsA_is_warm_address
    (hentry := fun t values body' callee ret' _ _ _ _ _ _ => trivial)
  · intro t values body callee rs v cpost _ _ hp _ _ _ _ _ hQc
    exact scXQ_setvar_g10 (by decide) (scXQ_of_locFrame_call_g10 hp hQc)
  apply HandlerRunA.dec (Q := fun s => scXQ s ∧ AcQ_g10 s)
    (hinit := fun t v hv _ hp => by
      have hvw : v = .val (.word (BitVec.ofNat 64 100)) := eval_const_word_g10 _ v hv
      subst hvw
      refine ⟨scXQ_setvar_g10 (by decide) hp, (BitVec.ofNat 64 100), ?_, Or.inl rfl⟩
      dsimp only [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      first | rw [if_pos rfl] | simp)
  apply HandlerRunA.seq_ite_unit
  · intro t w _ _
    apply HandlerRunA.seq_assign_local (Q := fun s => scXQ s ∧ AcQ_g10 s)
      (hasgn := fun t v hv _ hp => by
        have hvw : v = .val (.word (BitVec.ofNat 64 3000)) := eval_const_word_g10 _ v hv
        subst hvw
        refine ⟨scXQ_setvar_g10 (by decide) hp.1, (BitVec.ofNat 64 3000), ?_, Or.inr rfl⟩
        dsimp only [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        first | rw [if_pos rfl] | simp)
    exact op_delegatecall_needChain_g10 hW hgc hcont
  · intro t _
    exact HandlerRunA.seq_skip (op_delegatecall_needChain_g10 hW hgc hcont)

/-! ### `op_delegatecall` assembly -/

theorem op_delegatecall_run_full_g10 {F : Type} (s0 : PanSemStateFiniteExact 64 F)
    (hW : WorldAccountSpecsA)
    (hgc : EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "generic_call")) :
    HandlerRunA s0 (fun _ => True) false (sourceFnBody Guest.Software.guestFn_op_delegatecall) :=
  op_delegatecall_prefix1_g10
    (op_delegatecall_prefix2_g10 hW hgc
      (handlerRunA_of_childContinuation_g10 s0 _ _ (dcRest_ccA_g10 hW hgc)))

/-- The `op_delegatecall` handler spec (guest AST index 605). -/
theorem op_delegatecall_specA_g10 (hW : WorldAccountSpecsA)
    (hgc : EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "generic_call")) :
    OpHandlerSpecA (ofString "op_delegatecall") := by
  refine opHandlerSpecA_of_run 605 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_op_delegatecall rfl ?_
  intro F s0 hInv0 hWF0 hnd0
  exact op_delegatecall_run_full_g10 s0 hW hgc


end InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB

