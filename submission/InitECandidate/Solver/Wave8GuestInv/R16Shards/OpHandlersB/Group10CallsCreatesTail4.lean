import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.Group10CallsCreatesTail3
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.HeadMemAlignedBridge
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.helpers_t4

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

/-! ## Milestone 5 (call family, part 3): `op_call`

`op_call` reuses the `op_callcode` machinery of `Group10CallsCreatesTail3`
with one addition forced by value transfer to a possibly-new account:

* `op_call` charges state gas (`183600`) for a possible new account
  (`new_account_charged`) and refunds it on the failure path
  (`credit_state_gas_refund`); both are bare statement calls, which need an
  evaluation-congruence combinator, and the state-gas charge must carry the
  `ev+32` keep-word across the call for the later `CcDLQ` transports.

This tail also defines the local world-account record extension
`WorldAccountSpecsCall_g10` used by the conditional 7-bundle child bridge. -/

/-- The word `BitVec.ofNat 64 (n + k)` stays distinct from `evw + o` whenever the
natural offsets are distinct and the head-ev bound keeps both inside 64 bits. -/
private theorem bitvec_ofNat_add_ne_g10 {n k : Nat} {evw o : BitVec 64}
    (hb : n + 280 ≤ 2 ^ 64) (ht : evw.toNat = n) (hk : k < 280)
    (hob : o.toNat < 280) (hne : k ≠ o.toNat) :
    BitVec.ofNat 64 (n + k) ≠ evw + o := by
  intro hcon
  have hc : (BitVec.ofNat 64 (n + k)).toNat = (evw + o).toNat := by rw [hcon]
  simp only [BitVec.toNat_ofNat] at hc
  rw [BitVec.toNat_add, ht] at hc
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hc
  omega

/-- `charge_state_gas` keeps every global and the head frame's `ev+32` keep-word;
the only writes are `ev+72`, `ev+64`, `ev+192` (the `Ret` footprint of
`charge_state_gas_run`), so the `HeadMemChainWF` transport of the public
`epsA_charge_state_gas` carries over unchanged. -/
theorem epsA_charge_state_gas_k32 :
    EvmPreservingSpecA (fun _ => True)
      (fun s _ post => post.globals = s.globals ∧
        memW post (globN s "ev" + 32) = memW s (globN s "ev" + 32))
      (ofString "charge_state_gas") := by
  obtain ⟨params, body, retShape, hlk, hspec⟩ := epsA_charge_state_gas
  have hlk_eq := lookup_charge_state_gas_b.symm.trans hlk
  injection hlk_eq with hprod
  rcases Prod.mk.inj hprod with ⟨rfl, hprod2⟩
  rcases Prod.mk.inj hprod2 with ⟨hbody_eq, rfl⟩
  subst hbody_eq
  refine ⟨_, _, _, lookup_charge_state_gas_b, ?_⟩
  intro F s hcode hInv hHMWF hP hlookup hnt
  have hs := hspec s hcode hInv hHMWF hP hlookup hnt
  obtain ⟨hb_ev, evw, hev_lk, htoNat⟩ := ev_word_bounds hInv
  rcases hrun : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_charge_state_gas) with ⟨r, post⟩
  rw [hrun] at hs; dsimp only at hs ⊢
  refine ⟨fun v hv => ?_, fun herr => ?_⟩
  · obtain ⟨⟨hInv_p, hWF_p⟩, hch, hR, hg⟩ := hs.1 v hv
    have hv' : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_charge_state_gas)).1
        = some (.returned v) := by rw [hrun]; dsimp only; exact hv
    have hret := HeadMemBridge.charge_state_gas_run s evw hcode hev_lk v hv'
    rw [hrun] at hret; dsimp only at hret
    obtain ⟨-, hmem, -, -⟩ := hret
    have h32 : memW post (globN s "ev" + 32) = memW s (globN s "ev" + 32) := by
      unfold memW
      rw [hmem (BitVec.ofNat 64 (globN s "ev" + 32))
        (bitvec_ofNat_add_ne_g10 hb_ev htoNat (by decide) (by decide) (by decide))
        (bitvec_ofNat_add_ne_g10 hb_ev htoNat (by decide) (by decide) (by decide))
        (bitvec_ofNat_add_ne_g10 hb_ev htoNat (by decide) (by decide) (by decide))]
    exact ⟨⟨hInv_p, hWF_p⟩, hch, hR, ⟨hg, h32⟩⟩
  · obtain ⟨⟨hInv_p, hWF_p⟩, hch, hR⟩ := hs.2 herr
    exact ⟨⟨hInv_p, hWF_p⟩, hch, hR⟩

/-- A terminal `.skip` satisfies `HandlerRunA` for any predicate: it evaluates
to `(none, t)`, which makes both `OpDispatchPostA` obligations vacuous. -/
theorem HandlerRunA.skip_bare_g10 {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {P : PanSemStateFiniteExact 64 F → Prop} {charged : Bool} :
    HandlerRunA s0 P charged .skip := by
  intro t hc hi hw hlen hR hp hnt
  rw [evaluateHOLFiniteState_skip] at hnt ⊢
  exact ⟨(fun ⟨v, hv⟩ => by cases hv), (fun ⟨v, hv⟩ => by cases hv)⟩

/-- A `.seq p .skip` evaluates exactly like `p`: the `none` branch runs `skip`
at the intermediate state (a no-op) and the `some` branch short-circuits to
the same pair the bare program produced. -/
theorem eval_seq_skip_id_g10 {F : Type} (t : PanSemStateFiniteExact 64 F) (p : ProgHOL 64) :
    evaluateHOLFiniteState t (.seq p .skip) = evaluateHOLFiniteState t p := by
  rw [evaluateHOLFiniteState_seq_line780]
  cases h : evaluateHOLFiniteState t p with
  | mk result middle =>
    cases result with
    | none => dsimp only; rw [evaluateHOLFiniteState_skip]
    | some r0 => rfl

/-- Evaluation congruence transfers `HandlerRunA` between extensionally equal
programs. -/
theorem HandlerRunA.prog_eval_congr_g10 {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {P : PanSemStateFiniteExact 64 F → Prop} {charged : Bool} {p1 p2 : ProgHOL 64}
    (h : ∀ t : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState t p1 = evaluateHOLFiniteState t p2)
    (h1 : HandlerRunA s0 P charged p1) : HandlerRunA s0 P charged p2 := by
  intro t hc hi hw hlen hR hp hnt
  rw [← h t] at hnt ⊢
  exact h1 t hc hi hw hlen hR hp hnt

/-- A bare statement call (no result binding, no continuation) satisfies
`HandlerRunA`: it is the `seq_call` of the same call with a `skip` continuation,
transported by evaluation congruence. -/
theorem HandlerRunA.call_bare_g10 {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {P : PanSemStateFiniteExact 64 F → Prop}
    {Pc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {Qc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → ValueHOL 64 →
      PanSemStateFiniteExact 64 F → Prop}
    {charged : Bool}
    {fname : MlS} {args : List (ExpHOL 64)}
    (hf : EvmPreservingSpecA Pc Qc fname)
    (hentry : ∀ t values body' callee ret',
      t.code = originalRuntimeCode → EvmInv t → Group10.HeadMemChainWF t → P t →
      evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) args = some values →
      lookupCodeHOLFinite t.code.lookup fname values = some (body', callee, ret') →
      Pc (callEntryStateHOLFinite t callee))
    (hstep : ∀ t values body callee retShape v cpost,
      EvmInv t → Group10.HeadMemChainWF t → P t →
      evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) args = some values →
      lookupCodeHOLFinite originalRuntimeCode.lookup fname values = some (body, callee, retShape) →
      EvmInv cpost → Group10.HeadMemChainWF cpost →
      evmChain cpost = evmChain (callEntryStateHOLFinite t callee) →
      Qc (callEntryStateHOLFinite t callee) v cpost →
      P { cpost with locals := t.locals }) :
    HandlerRunA s0 P charged (.call (some (none, none)) fname args) :=
  HandlerRunA.prog_eval_congr_g10
    (fun t => eval_seq_skip_id_g10 t (.call (some (none, none)) fname args))
    (HandlerRunA.seq_call (P := P) (Qc := Qc) hf hentry hstep
      (hcont := HandlerRunA.skip_bare_g10))

/-- The call-family world-account record: `WorldAccountSpecsA` strengthened with
the `ev+32` keep-word through `is_account_alive` (needed to carry `CcDLQ` across
the new-account probe).  The `charge_state_gas` strengthening is provable
(`epsA_charge_state_gas_k32` above) and therefore not a field. -/
structure WorldAccountSpecsCall_g10 extends WorldAccountSpecsA where
  epsA_is_account_alive_k32 :
    EvmPreservingSpecA (fun _ => True)
      (fun s _ post => GlobalsKept ["heap_ptr", "scratch_ptr"] s post ∧ evmR post = evmR s ∧
        memW post (globN s "ev" + 32) = memW s (globN s "ev" + 32))
      (ofString "is_account_alive")


/-! ### The `op_call` prefix through the `access_cost` ite

Compared to `op_callcode`, the stack pops drop the `to` local (the masked
address is itself the `to` local), `vz` is computed BEFORE the memory-expansion
cost, and a static-context check `raise`-ite sits between them.  The cost pins
(`CcVzQ`) therefore have to survive the `x`/`warm`/`access_cost` steps. -/

theorem op_call_prefix1_g10 {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {charged : Bool} {cont : ProgHOL 64}
    (hcont : HandlerRunA s0 (fun s => scXQ s ∧ EvmInv s0 ∧ AcQ_g10 s ∧ CcVzQ_g10 s) charged cont) :
    HandlerRunA s0 (fun _ => EvmInv s0) charged
      (.decCall (ofString "gasv") (.comb [.one, .one, .one, .one]) (ofString "stack_pop") []
        (.decCall (ofString "tov") (.comb [.one, .one, .one, .one]) (ofString "stack_pop") []
          (.decCall (ofString "to") .one (ofString "to_address_masked")
            [.var .local (ofString "tov")]
            (.decCall (ofString "value") (.comb [.one, .one, .one, .one]) (ofString "stack_pop") []
              (.decCall (ofString "in_start") (.comb [.one, .one, .one, .one]) (ofString "stack_pop") []
                (.decCall (ofString "in_size") (.comb [.one, .one, .one, .one]) (ofString "stack_pop") []
                  (.decCall (ofString "out_start") (.comb [.one, .one, .one, .one]) (ofString "stack_pop") []
                    (.decCall (ofString "out_size") (.comb [.one, .one, .one, .one]) (ofString "stack_pop") []
                      (.dec (ofString "msg") .one
                        (.load .one (.op .add [.var .global (ofString "ev"),
                          .const (BitVec.ofNat 64 112)]))
                        (.decCall (ofString "vz") .one (ofString "u256_is_zero")
                          [.var .local (ofString "value")]
                          (.seq
                            (.ite (.op .and
                                [.cmp .notEqual (.const (BitVec.ofNat 64 0))
                                  (.cmp .notEqual
                                    (.load .one (.op .add [.var .local (ofString "msg"),
                                      .const (BitVec.ofNat 64 144)]))
                                    (.const (BitVec.ofNat 64 0))),
                                 .cmp .notEqual (.const (BitVec.ofNat 64 0))
                                  (.cmp .equal (.var .local (ofString "vz"))
                                    (.const (BitVec.ofNat 64 0)))])
                              (.raise (ofString "EvmErr") (.const (BitVec.ofNat 64 8)))
                              .skip)
                            (.decCall (ofString "x") (.comb [.one, .one])
                              (ofString "extend_memory_cost2")
                              [.var .local (ofString "in_start"),
                                .var .local (ofString "in_size"),
                                .var .local (ofString "out_start"),
                                .var .local (ofString "out_size")]
                              (.decCall (ofString "warm") .one (ofString "is_warm_address")
                                [.var .local (ofString "to")]
                                (.dec (ofString "access_cost") .one
                                  (.const (BitVec.ofNat 64 100))
                                  (.seq
                                    (.ite (.cmp .equal (.var .local (ofString "warm"))
                                        (.const (BitVec.ofNat 64 0)))
                                      (.assign .local (ofString "access_cost")
                                        (.const (BitVec.ofNat 64 3000)))
                                      .skip)
                                    cont))))))))))))))) := by
  refine HandlerRunA.decCall_carry_g10 (P := fun _ => EvmInv s0)
    epsA_stack_pop_le_g10 (fun _ _ _ hp => hp) ?_
  refine HandlerRunA.decCall_carry_g10 (P := fun _ => EvmInv s0)
    epsA_stack_pop_le_g10 (fun _ _ _ hp => hp) ?_
  refine HandlerRunA.decCall_carry_g10 (P := fun _ => EvmInv s0)
    epsA_to_address_masked (fun _ _ _ hp => hp) ?_
  refine HandlerRunA.decCall_carry_g10 (P := fun _ => EvmInv s0)
    epsA_stack_pop_le_g10 (fun _ _ _ hp => hp) ?_
  refine HandlerRunA.decCall_carry_g10 (P := fun _ => EvmInv s0)
    epsA_stack_pop_le_g10 (fun _ _ _ hp => hp) ?_
  refine HandlerRunA.decCall_carry_g10 (P := fun _ => EvmInv s0)
    epsA_stack_pop_le_g10 (fun _ _ _ hp => hp) ?_
  refine HandlerRunA.decCall_carry_g10 (P := fun _ => EvmInv s0)
    epsA_stack_pop_le_g10 (fun _ _ _ hp => hp) ?_
  refine HandlerRunA.decCall_carry_g10 (P := fun _ => EvmInv s0)
    epsA_stack_pop_le_g10 (fun _ _ _ hp => hp) ?_
  refine HandlerRunA.dec_carry_g10 (P := fun _ => EvmInv s0) (fun _ _ hp => hp) ?_
  apply HandlerRunA.decCall (Q := fun s => EvmInv s0 ∧ CcVzQ_g10 s)
    Group10.epsA_u256_is_zero_sem_g10
    (hentry := fun t values body' callee ret' _ _ _ _ _ _ => trivial)
  · intro t values body callee rs v cpost _ _ hp hargs hlk _ _ _ hQc
    obtain ⟨hlf, z, hvz, hz01, hor⟩ := hQc
    obtain ⟨v0, hv0_ev, hvals⟩ : ∃ v0,
        @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
          (.var .local (ofString "value")) = some v0 ∧ values = [v0] := by
      rw [evalListHOLFinite_eq_toExact] at hargs
      simp only [evalListHOLExact] at hargs
      rcases he : @evalHOLExact 64 F _ t.toExact
          (fun a => Classical.propDecidable (t.memaddrs a))
          (.var .local (ofString "value")) with _ | v0
      · simp [he] at hargs
      · simp only [he, Option.some.injEq] at hargs; exact ⟨v0, rfl, hargs.symm⟩
    subst hvals
    obtain ⟨q0, q1, q2, q3, hv0_struct, ha_pin⟩ := u256_is_zero_args_lookup_g10 hlk
    have hval_pin : t.locals.lookup (ofString "value") =
        some (.rStruct [.val (.word q0), .val (.word q1), .val (.word q2),
          .val (.word q3)]) := by
      rw [← hv0_struct]
      exact hv0_ev
    refine ⟨hp, q0, q1, q2, q3, z, hval_pin, ?_, hz01, hor q0 q1 q2 q3 ha_pin⟩
    dsimp only [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    first | rw [if_pos rfl, hvz] | simp [hvz]
  · refine HandlerRunA.seq_ite_raise_skip (fun _ _ _ h => h) ?_
    refine HandlerRunA.decCall (Q := fun s => scXQ s ∧ EvmInv s0 ∧ CcVzQ_g10 s)
      epsA_extend_memory_cost2
      (hentry := fun t values body' callee ret' _ _ _ _ _ _ => trivial) ?_ ?_
    · intro t values body callee rs v cpost _ _ hp _ _ _ _ _ hQc
      obtain ⟨hlf, cw, ebw, hv, hbd⟩ := hQc
      obtain ⟨hinv, q0, q1, q2, q3, z, hval_pin, hvzp, hz01, hcorr⟩ := hp
      refine ⟨⟨cw, ebw, ?_, ?_⟩, hinv, q0, q1, q2, q3, z, ?_, ?_, hz01, hcorr⟩
      · dsimp only [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        first | rw [if_pos rfl, hv] | simp [hv]
      · rw [hlf]
        exact hbd
      · dsimp only [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        rw [if_neg (by decide)]
        exact hval_pin
      · dsimp only [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        rw [if_neg (by decide)]
        exact hvzp
    · apply HandlerRunA.decCall (Q := fun s => scXQ s ∧ EvmInv s0 ∧ CcVzQ_g10 s)
        epsA_is_warm_address
        (hentry := fun t values body' callee ret' _ _ _ _ _ _ => trivial)
      · intro t values body callee rs v cpost _ _ hp _ _ _ _ _ hQc
        obtain ⟨hsc, hinv, q0, q1, q2, q3, z, hval_pin, hvzp, hz01, hcorr⟩ := hp
        refine ⟨scXQ_setvar_g10 (by decide) (scXQ_of_locFrame_call_g10 hsc hQc), hinv,
          q0, q1, q2, q3, z, ?_, ?_, hz01, hcorr⟩
        · dsimp only [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          rw [if_neg (by decide)]
          exact hval_pin
        · dsimp only [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          rw [if_neg (by decide)]
          exact hvzp
      · apply HandlerRunA.dec
          (Q := fun s => scXQ s ∧ EvmInv s0 ∧ AcQ_g10 s ∧ CcVzQ_g10 s)
          (hinit := fun t v hv _ hp => by
            have hvw : v = .val (.word (BitVec.ofNat 64 100)) :=
              eval_const_word_g10 _ v hv
            subst hvw
            obtain ⟨hsc, hinv, hcz⟩ := hp
            obtain ⟨q0, q1, q2, q3, z, hval_pin, hvzp, hz01, hcorr⟩ := hcz
            refine ⟨scXQ_setvar_g10 (by decide) hsc, hinv,
              ⟨(BitVec.ofNat 64 100), ?_, Or.inl rfl⟩,
              q0, q1, q2, q3, z, ?_, ?_, hz01, hcorr⟩
            · dsimp only [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
              first | rw [if_pos rfl] | simp
            · dsimp only [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
              rw [if_neg (by decide)]
              exact hval_pin
            · dsimp only [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
              rw [if_neg (by decide)]
              exact hvzp)
        apply HandlerRunA.seq_ite_unit
        · intro t w _ _
          apply HandlerRunA.seq_assign_local
            (Q := fun s => scXQ s ∧ EvmInv s0 ∧ AcQ_g10 s ∧ CcVzQ_g10 s)
            (hasgn := fun t v hv _ hp => by
              have hvw : v = .val (.word (BitVec.ofNat 64 3000)) :=
                eval_const_word_g10 _ v hv
              subst hvw
              obtain ⟨hsc, hinv, hac, hcz⟩ := hp
              obtain ⟨acw, hl_ac, hacd⟩ := hac
              obtain ⟨q0, q1, q2, q3, z, hval_pin, hvzp, hz01, hcorr⟩ := hcz
              refine ⟨scXQ_setvar_g10 (by decide) hsc, hinv,
                ⟨(BitVec.ofNat 64 3000), ?_, Or.inr rfl⟩,
                q0, q1, q2, q3, z, ?_, ?_, hz01, hcorr⟩
              · dsimp only [setKvarHOLFinite, setVarHOLFinite,
                  HolFiniteMapExact.lookup_update, FUPDATE]
                first | rw [if_pos rfl] | simp
              · dsimp only [setKvarHOLFinite, setVarHOLFinite,
                  HolFiniteMapExact.lookup_update, FUPDATE]
                rw [if_neg (by decide)]
                exact hval_pin
              · dsimp only [setKvarHOLFinite, setVarHOLFinite,
                  HolFiniteMapExact.lookup_update, FUPDATE]
                rw [if_neg (by decide)]
                exact hvzp)
          exact hcont
        · intro t _
          exact HandlerRunA.seq_skip hcont

/-- The `op_call` prefix (nodes up to the `need` charge; the `transfer_cost`
and `need` chains are shared verbatim with `op_callcode`). -/
theorem op_call_prefix_g10 {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {cont : ProgHOL 64}
    (hcont : HandlerRunA s0 (fun t => CcPQ_g10 s0 t) true cont) :
    HandlerRunA s0 (fun _ => EvmInv s0) false
      (.decCall (ofString "gasv") (.comb [.one, .one, .one, .one]) (ofString "stack_pop") []
        (.decCall (ofString "tov") (.comb [.one, .one, .one, .one]) (ofString "stack_pop") []
          (.decCall (ofString "to") .one (ofString "to_address_masked")
            [.var .local (ofString "tov")]
            (.decCall (ofString "value") (.comb [.one, .one, .one, .one]) (ofString "stack_pop") []
              (.decCall (ofString "in_start") (.comb [.one, .one, .one, .one]) (ofString "stack_pop") []
                (.decCall (ofString "in_size") (.comb [.one, .one, .one, .one]) (ofString "stack_pop") []
                  (.decCall (ofString "out_start") (.comb [.one, .one, .one, .one]) (ofString "stack_pop") []
                    (.decCall (ofString "out_size") (.comb [.one, .one, .one, .one]) (ofString "stack_pop") []
                      (.dec (ofString "msg") .one
                        (.load .one (.op .add [.var .global (ofString "ev"),
                          .const (BitVec.ofNat 64 112)]))
                        (.decCall (ofString "vz") .one (ofString "u256_is_zero")
                          [.var .local (ofString "value")]
                          (.seq
                            (.ite (.op .and
                                [.cmp .notEqual (.const (BitVec.ofNat 64 0))
                                  (.cmp .notEqual
                                    (.load .one (.op .add [.var .local (ofString "msg"),
                                      .const (BitVec.ofNat 64 144)]))
                                    (.const (BitVec.ofNat 64 0))),
                                 .cmp .notEqual (.const (BitVec.ofNat 64 0))
                                  (.cmp .equal (.var .local (ofString "vz"))
                                    (.const (BitVec.ofNat 64 0)))])
                              (.raise (ofString "EvmErr") (.const (BitVec.ofNat 64 8)))
                              .skip)
                            (.decCall (ofString "x") (.comb [.one, .one])
                              (ofString "extend_memory_cost2")
                              [.var .local (ofString "in_start"),
                                .var .local (ofString "in_size"),
                                .var .local (ofString "out_start"),
                                .var .local (ofString "out_size")]
                              (.decCall (ofString "warm") .one (ofString "is_warm_address")
                                [.var .local (ofString "to")]
                                (.dec (ofString "access_cost") .one
                                  (.const (BitVec.ofNat 64 100))
                                  (.seq
                                    (.ite (.cmp .equal (.var .local (ofString "warm"))
                                        (.const (BitVec.ofNat 64 0)))
                                      (.assign .local (ofString "access_cost")
                                        (.const (BitVec.ofNat 64 3000)))
                                      .skip)
                                    (.dec (ofString "transfer_cost") .one
                                      (.const (BitVec.ofNat 64 0))
                                      (.seq
                                        (.ite (.cmp .equal (.var .local (ofString "vz"))
                                            (.const (BitVec.ofNat 64 0)))
                                          (.assign .local (ofString "transfer_cost")
                                            (.const (BitVec.ofNat 64 11300)))
                                          .skip)
                                        (.decCall (ofString "need") .one (ofString "add_sat")
                                          [.op .add [.var .local (ofString "access_cost"),
                                            .var .local (ofString "transfer_cost")],
                                           .rfield 0 (.var .local (ofString "x"))]
                                          (.seq
                                            (.call (some (none, none)) (ofString "charge_gas")
                                              [.var .local (ofString "need")])
                                            cont))))))))))))))))))) := by
  exact op_call_prefix1_g10
    (op_callcode_tcChain_g10 (op_callcode_needChain_g10 hcont))

/-! ### The `op_call` rest: congruence short-hands for the `alive`-free tail

The new-account probe `decCall alive ... is_account_alive` has to be swapped
out of its `seq` with `callRest`, which requires the rest to be insensitive to
the `alive` slot.  The short-hands below assemble the `EvalCongP`/`ListCongP`
witnesses for the shapes occurring in that rest. -/

/-- One-element argument-list congruence. -/
private theorem lcg1_g10t4 {F : Type} {nm : MlS} {e : ExpHOL 64}
    (h : EvalCongP_g10t4 (F := F) nm e) : ListCongP_g10t4 (F := F) nm [e] :=
  listCongP_cons_g10t4 h listCongP_nil_g10t4

/-- Two-element argument-list congruence. -/
private theorem lcg2_g10t4 {F : Type} {nm : MlS} {e1 e2 : ExpHOL 64}
    (h1 : EvalCongP_g10t4 (F := F) nm e1) (h2 : EvalCongP_g10t4 (F := F) nm e2) :
    ListCongP_g10t4 (F := F) nm [e1, e2] :=
  listCongP_cons_g10t4 h1 (lcg1_g10t4 h2)

/-- The `ev + c` address expression. -/
private theorem ecgEvAdd_g10t4 {F : Type} {nm : MlS} {c : BitVec 64} :
    EvalCongP_g10t4 (F := F) nm
      (.op .add [.var .global (ofString "ev"), .const c]) :=
  evalCongP_op_g10t4 (lcg2_g10t4 evalCongP_var_global_g10t4 (evalCongP_const_g10t4 c))

/-- The `load sh (ev + c)` word read. -/
private theorem ecgEvLoad_g10t4 {F : Type} {nm : MlS} {sh : ShapeHOL} {c : BitVec 64} :
    EvalCongP_g10t4 (F := F) nm
      (.load sh (.op .add [.var .global (ofString "ev"), .const c])) :=
  evalCongP_load_g10t4 ecgEvAdd_g10t4

/-- The `load sh (k + c)` local-relative read, `k` outside the swapped slot. -/
private theorem ecgLocLoad_g10t4 {F : Type} {nm k : MlS} {sh : ShapeHOL} {c : BitVec 64}
    (hk : k ≠ nm) : EvalCongP_g10t4 (F := F) nm
      (.load sh (.op .add [.var .local k, .const c])) :=
  evalCongP_load_g10t4
    (evalCongP_op_g10t4
      (lcg2_g10t4 (evalCongP_var_local_g10t4 hk) (evalCongP_const_g10t4 c)))

/-- The `k.i` record-field read, `k` outside the swapped slot. -/
private theorem ecgRF_g10t4 {F : Type} {nm k : MlS} {i : Nat} (hk : k ≠ nm) :
    EvalCongP_g10t4 (F := F) nm (.rfield i (.var .local k)) :=
  evalCongP_rfield_g10t4 (evalCongP_var_local_g10t4 hk)

/-- The `k != c` comparison, `k` outside the swapped slot. -/
private theorem ecgCmpC_g10t4 {F : Type} {nm k : MlS} {o : Flapjack.Cmp} {c : BitVec 64}
    (hk : k ≠ nm) : EvalCongP_g10t4 (F := F) nm (.cmp o (.var .local k) (.const c)) :=
  evalCongP_cmp_g10t4 (evalCongP_var_local_g10t4 hk) (evalCongP_const_g10t4 c)

/-- The `op_call` rest after the new-account block: the `sat_word` /
`calculate_message_call_gas` chain, the gas-word/reservoir ledger, and the
insufficient-funds ite down to the terminal `started`-test continuation. -/
def callRestProg_g10 : ProgHOL 64 :=
  .decCall (ofString "gw") .one (ofString "sat_word") [.var .local (ofString "gasv")]
    (.decCall (ofString "mcg") (.comb [.one, .one]) (ofString "calculate_message_call_gas")
      [.var .local (ofString "value"), .var .local (ofString "gw"),
       .load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 64)]),
       .const (BitVec.ofNat 64 0), .const (BitVec.ofNat 64 0)]
      (.seq (.call (some (none, none)) (ofString "charge_gas")
          [.rfield 0 (.var .local (ofString "mcg"))])
        (.seq (.store (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 184)])
            (.op .sub [.load .one (.op .add [.var .global (ofString "ev"),
                .const (BitVec.ofNat 64 184)]),
              .rfield 1 (.var .local (ofString "mcg"))]))
          (.seq (.call (some (none, none)) (ofString "extend_memory")
              [.rfield 1 (.var .local (ofString "x"))])
            (.dec (ofString "reservoir") .one
              (.load .one (.op .add [.var .global (ofString "ev"),
                .const (BitVec.ofNat 64 72)]))
              (.seq (.store (.op .add [.var .global (ofString "ev"),
                  .const (BitVec.ofNat 64 72)])
                  (.const (BitVec.ofNat 64 0)))
                (.decCall (ofString "sender") .one (ofString "get_account")
                  [.load .one (.op .add [.var .local (ofString "msg"),
                     .const (BitVec.ofNat 64 32)])]
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
                              [.rstruct [.const (BitVec.ofNat 64 0),
                                .const (BitVec.ofNat 64 0), .const (BitVec.ofNat 64 0),
                                .const (BitVec.ofNat 64 0)]])
                            (.dec (ofString "empty") .one
                              (.var .global (ofString "evm_empty"))
                              (.seq (.call (some (none, none)) (ofString "set_retdata")
                                  [.var .local (ofString "empty"),
                                   .const (BitVec.ofNat 64 0)])
                                (.seq (.store (.op .add [.var .global (ofString "ev"),
                                      .const (BitVec.ofNat 64 64)])
                                    (.op .add [.load .one (.op .add
                                        [.var .global (ofString "ev"),
                                         .const (BitVec.ofNat 64 64)]),
                                      .rfield 1 (.var .local (ofString "mcg"))]))
                                  (.seq (.store (.op .add [.var .global (ofString "ev"),
                                      .const (BitVec.ofNat 64 72)])
                                      (.op .add [.load .one (.op .add
                                          [.var .global (ofString "ev"),
                                           .const (BitVec.ofNat 64 72)]),
                                        .var .local (ofString "reservoir")]))
                                    (.ite (.cmp .notEqual
                                        (.var .local (ofString "new_account_charged"))
                                        (.const (BitVec.ofNat 64 0)))
                                      (.call (some (none, none))
                                          (ofString "credit_state_gas_refund")
                                        [.const (BitVec.ofNat 64 183600)])
                                      .skip))))))
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
                                     .load .one (.op .add [.var .local (ofString "msg"),
                                       .const (BitVec.ofNat 64 32)]),
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
                                     .var .local (ofString "new_account_charged")]))))))
                        callcodeContProg_g10))))))))))

/-- The `op_call` rest is insensitive to the `alive` slot: it is the terminal
swap obligation for moving the `is_account_alive` probe out of the `seq`. -/
theorem callRestNoread_g10 {F : Type} :
    ContNoreadP_g10 (F := F) (ofString "alive") callRestProg_g10 := by
  simp only [callRestProg_g10]
  refine cnp_decCall_g10t4 (lcg1_g10t4 (evalCongP_var_local_g10t4 (by decide))) ?_
  refine cnp_decCall_g10t4 ?_ ?_
  · exact listCongP_cons_g10t4 (evalCongP_var_local_g10t4 (by decide))
      (listCongP_cons_g10t4 (evalCongP_var_local_g10t4 (by decide))
        (listCongP_cons_g10t4 ecgEvLoad_g10t4
          (listCongP_cons_g10t4 (evalCongP_const_g10t4 _)
            (listCongP_cons_g10t4 (evalCongP_const_g10t4 _)
              listCongP_nil_g10t4))))
  · refine cnp_seq_g10t4 (cnp_call_g10t4 (lcg1_g10t4 (ecgRF_g10t4 (by decide)))) ?_
    refine cnp_seq_g10t4 (cnp_store_g10t4 ecgEvAdd_g10t4 ?_) ?_
    · exact evalCongP_op_g10t4 (lcg2_g10t4 ecgEvLoad_g10t4 (ecgRF_g10t4 (by decide)))
    refine cnp_seq_g10t4 (cnp_call_g10t4 (lcg1_g10t4 (ecgRF_g10t4 (by decide)))) ?_
    refine cnp_dec_g10t4 ecgEvLoad_g10t4 ?_
    refine cnp_seq_g10t4 (cnp_store_g10t4 ecgEvAdd_g10t4 (evalCongP_const_g10t4 _)) ?_
    refine cnp_decCall_g10t4 (lcg1_g10t4 (ecgLocLoad_g10t4 (by decide))) ?_
    refine cnp_decCall_g10t4 (listCongP_cons_g10t4 (ecgLocLoad_g10t4 (by decide))
        (lcg1_g10t4 (evalCongP_var_local_g10t4 (by decide)))) ?_
    refine cnp_dec_g10t4 (evalCongP_const_g10t4 _) ?_
    refine cnp_seq_g10t4 (cnp_ite_g10t4
        (ecgCmpC_g10t4 (by decide : ofString "insufficient" ≠ ofString "alive")) ?_ ?_) ?_
    · refine cnp_seq_g10t4 (cnp_call_g10t4 (lcg1_g10t4 (evalCongP_rstruct_g10t4
          (listCongP_cons_g10t4 (evalCongP_const_g10t4 _)
            (listCongP_cons_g10t4 (evalCongP_const_g10t4 _)
              (listCongP_cons_g10t4 (evalCongP_const_g10t4 _)
                (listCongP_cons_g10t4 (evalCongP_const_g10t4 _)
                  listCongP_nil_g10t4))))))) ?_
      refine cnp_dec_g10t4 evalCongP_var_global_g10t4 ?_
      refine cnp_seq_g10t4 (cnp_call_g10t4 (listCongP_cons_g10t4
          (evalCongP_var_local_g10t4 (by decide))
          (lcg1_g10t4 (evalCongP_const_g10t4 _)))) ?_
      refine cnp_seq_g10t4 (cnp_store_g10t4 ecgEvAdd_g10t4
          (evalCongP_op_g10t4 (lcg2_g10t4 ecgEvLoad_g10t4
            (ecgRF_g10t4 (by decide))))) ?_
      refine cnp_seq_g10t4 (cnp_store_g10t4 ecgEvAdd_g10t4
          (evalCongP_op_g10t4 (lcg2_g10t4 ecgEvLoad_g10t4
            (evalCongP_var_local_g10t4 (by decide))))) ?_
      exact cnp_ite_g10t4 (ecgCmpC_g10t4 (by decide))
        (cnp_call_g10t4 (lcg1_g10t4 (evalCongP_const_g10t4 _))) cnp_skip_g10t4
    · refine cnp_decCall_g10t4 (lcg1_g10t4 (evalCongP_var_local_g10t4 (by decide))) ?_
      refine cnp_decCall_g10t4 (lcg1_g10t4 (evalCongP_var_local_g10t4 (by decide))) ?_
      refine cnp_decCall_g10t4 (lcg1_g10t4 (evalCongP_var_local_g10t4 (by decide))) ?_
      refine cnp_decCall_g10t4 (lcg1_g10t4 (evalCongP_var_local_g10t4 (by decide))) ?_
      exact cnp_call_assign_local_g10t4 (by decide)
        (listCongP_cons_g10t4 (ecgRF_g10t4 (by decide))
          (listCongP_cons_g10t4 (evalCongP_var_local_g10t4 (by decide))
            (listCongP_cons_g10t4 (evalCongP_var_local_g10t4 (by decide))
              (listCongP_cons_g10t4 (ecgLocLoad_g10t4 (by decide))
                (listCongP_cons_g10t4 (evalCongP_var_local_g10t4 (by decide))
                  (listCongP_cons_g10t4 (evalCongP_var_local_g10t4 (by decide))
                    (listCongP_cons_g10t4 (evalCongP_const_g10t4 _)
                      (listCongP_cons_g10t4 (evalCongP_const_g10t4 _)
                        (listCongP_cons_g10t4 (evalCongP_var_local_g10t4 (by decide))
                          (listCongP_cons_g10t4 (evalCongP_var_local_g10t4 (by decide))
                            (listCongP_cons_g10t4 (evalCongP_var_local_g10t4 (by decide))
                              (listCongP_cons_g10t4 (evalCongP_var_local_g10t4 (by decide))
                                (listCongP_cons_g10t4 (ecgRF_g10t4 (by decide))
                                  (listCongP_cons_g10t4 (ecgRF_g10t4 (by decide))
                                    (listCongP_cons_g10t4 (ecgRF_g10t4 (by decide))
                                      (listCongP_cons_g10t4
                                        (evalCongP_var_local_g10t4 (by decide))
                                        listCongP_nil_g10t4))))))))))))))))
    · exact cnp_seq_g10t4
        (cnp_ite_g10t4 (ecgCmpC_g10t4 (by decide))
          (cnp_call_g10t4 (lcg1_g10t4 (evalCongP_const_g10t4 _))) cnp_skip_g10t4)
        (cnp_return_g10t4 (evalCongP_const_g10t4 _))

/-! ### The `op_call` tail walk -/

/-- The warm-ite on the pre-computed `warm` flag (warming the recipient). -/
theorem callWarmIte_g10 {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    (hgc : EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "generic_call")) {cont : ProgHOL 64}
    (hcont : HandlerRunA s0 (fun t => CcPQ_g10 s0 t) true cont) :
    HandlerRunA s0 (fun t => CcPQ_g10 s0 t) true
      (.seq
        (.ite (.cmp .equal (.var .local (ofString "warm")) (.const (BitVec.ofNat 64 0)))
          (.call (some (none, none)) (ofString "warm_address")
            [.var .local (ofString "to")])
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

/-- The `calculate_delegation_cost` call on the recipient. -/
theorem callDl_g10 {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    (hW : WorldAccountSpecsA)
    (hgc : EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "generic_call")) {cont : ProgHOL 64}
    (hcont : HandlerRunA s0 (fun t => CcDLQ_g10 s0 t) true cont) :
    HandlerRunA s0 (fun t => CcPQ_g10 s0 t) true
      (.decCall (ofString "dl") (.comb [.one, .one, .one])
          (ofString "calculate_delegation_cost")
        [.var .local (ofString "to")] cont) := by
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

/-- The `get_account` call on the message sender address. -/
theorem callSender2_g10 {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    (hW : WorldAccountSpecsA)
    (hgc : EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "generic_call")) {cont : ProgHOL 64}
    (hcont : HandlerRunA s0 (fun t => CcR2Q_g10 s0 t) true cont) :
    HandlerRunA s0 (fun t => CcR2Q_g10 s0 t) true
      (.decCall (ofString "sender") .one (ofString "get_account")
        [.load .one (.op .add [.var .local (ofString "msg"), .const (BitVec.ofNat 64 32)])]
        cont) := by
  refine HandlerRunA.decCall hW.epsA_get_account (Q := fun t => CcR2Q_g10 s0 t) ?_ ?_ hcont
  · intro t values body' callee ret' hc hi hw hp hargs hl
    exact trivial
  · intro t values body callee retShape v cpost hi hw hp hargs hl hi_cp hw_cp hch_cp hQc
    obtain ⟨hgk, hRev⟩ := hQc
    exact CcR2Q_setVarRes_g10 (by decide) (le_of_eq (hRev.trans evmR_entry_eq_g10)) hp

/-- The `generic_call` of the sufficient-funds branch of `op_call` (sender
address read from the message, new-account flag as the last argument). -/
theorem callGenericCall2_g10 {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    (hgc : EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "generic_call")) :
    HandlerRunA s0 (fun t => CcR2Q_g10 s0 t) true
      (.seq
        (.call (some (some (.local, ofString "started"), none)) (ofString "generic_call")
          [.rfield 1 (.var .local (ofString "mcg")),
           .var .local (ofString "reservoir"),
           .var .local (ofString "value"),
           .load .one (.op .add [.var .local (ofString "msg"), .const (BitVec.ofNat 64 32)]),
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
           .var .local (ofString "new_account_charged")])
        callcodeContProg_g10) :=
  HandlerRunA.seq_call_assign_local hgc
    (fun t values body' callee ret' hc hi hw hp hargs hl => trivial)
    (fun t values body callee retShape v cpost hi hw hp hargs hl hshp hi_cp hw_cp hch_cp hQc =>
      CcR2Q_setVarRes_g10 (by decide)
        (le_of_eq ((evmR_congr_full_g10 hQc).trans evmR_entry_eq_g10)) hp)
    (HandlerRunA.weaken (fun t ht hp => trivial) callcodeCont_run_g10)

/-- The `op_call` insufficient-funds tail: like `op_callcode`'s, but the
failure path refunds the new-account state-gas charge when it was made. -/
theorem callInsfTail2_g10 {F : Type} {s0 : PanSemStateFiniteExact 64 F}
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
                  (.seq (.store (.op .add [.var .global (ofString "ev"),
                      .const (BitVec.ofNat 64 72)])
                    (.op .add
                      [.load .one (.op .add [.var .global (ofString "ev"),
                         .const (BitVec.ofNat 64 72)]),
                       .var .local (ofString "reservoir")]))
                    (.ite (.cmp .notEqual (.var .local (ofString "new_account_charged"))
                        (.const (BitVec.ofNat 64 0)))
                      (.call (some (none, none)) (ofString "credit_state_gas_refund")
                        [.const (BitVec.ofNat 64 183600)])
                      .skip))))))
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
                     .load .one (.op .add [.var .local (ofString "msg"),
                       .const (BitVec.ofNat 64 32)]),
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
                     .var .local (ofString "new_account_charged")]))))))
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
        · refine HandlerRunA.seq_assoc ?_
          refine HandlerRunA.seq_store_ev_off_charged_g10 (off := 72)
            (P := fun _ => True) (Q := fun _ => True) (by omega) ?_ ?_ ?_
          · intro t v hp hv
            exact eval_op_word_g10 BinOp.add _ v hv
          · intro t w heval hi hw hp hR_lt
            obtain ⟨hInv1, hWF1, hch1, hRle⟩ :=
              evOff_store_evmStep_g10 (Q := fun _ => True) t w 72 (Or.inr rfl) hi hw
            exact ⟨hInv1, hWF1, hch1, trivial, lt_of_le_of_lt hRle hR_lt⟩
          · refine HandlerRunA.seq_ite_unit (fun t w heval hw0 => ?_) (fun t heval => ?_)
            · exact HandlerRunA.seq_call epsA_credit_state_gas_refund
                (Q := fun _ => True)
                (fun t values body' callee ret' hc hi hw hp hargs hl => trivial)
                (fun t values body callee retShape v cpost hi hw hp hargs hl
                    hi_cp hw_cp hch_cp hQc => trivial)
                callcodeCont_run_g10
            · exact HandlerRunA.seq_skip callcodeCont_run_g10
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
        · refine seq_decCall_swap_g10
            (callcodeCont_noread_g10 (nm := ofString "osz") (by decide)) ?_
          refine HandlerRunA.decCall epsA_sat_word (Q := fun t => CcR2Q_g10 s0 t) ?_ ?_ ?_
          · intro t values body' callee ret' hc hi hw hp hargs hl
            exact trivial
          · intro t values body callee retShape v cpost hi hw hp hargs hl hi_cp hw_cp hch_cp hQc
            exact CcR2Q_setVarRes_g10 (by decide)
              (le_of_eq ((evmR_congr_full_g10 hQc).trans evmR_entry_eq_g10)) hp
          · exact callGenericCall2_g10 hgc

/-- The new-account-charging block of `op_call`: when a value transfer may
create the recipient, probe `is_account_alive` and charge the state gas; the
probe is swapped out of its `seq` with the `alive`-insensitive rest. -/
theorem callNacBlock_g10 {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    (hW : WorldAccountSpecsCall_g10)
    (hgc : EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "generic_call")) :
    HandlerRunA s0 (fun t => CcDLQ_g10 s0 t) true
      (.dec (ofString "new_account_charged") .one (.const (BitVec.ofNat 64 0))
        (.seq
          (.ite (.cmp .equal (.var .local (ofString "vz")) (.const (BitVec.ofNat 64 0)))
            (.decCall (ofString "alive") .one (ofString "is_account_alive")
              [.var .local (ofString "to")]
              (.ite (.cmp .equal (.var .local (ofString "alive"))
                  (.const (BitVec.ofNat 64 0)))
                (.seq (.assign .local (ofString "new_account_charged")
                    (.const (BitVec.ofNat 64 1)))
                  (.call (some (none, none)) (ofString "charge_state_gas")
                    [.const (BitVec.ofNat 64 183600)]))
                .skip))
            .skip)
          callRestProg_g10)) := by
  have hrest : HandlerRunA s0 (fun t => CcDLQ_g10 s0 t) true callRestProg_g10 := by
    simp only [callRestProg_g10]
    exact callcodeGw_g10
      (callcodeMcg_g10
        (callcodeChargeMcg_g10
          (callcodeStore184_g10
            (callcodeExtend_g10
              (callcodeReservoir_g10
                (callcodeStore72z_g10
                  (callSender2_g10 hW.toWorldAccountSpecsA hgc
                    (callcodeInsufficient_g10 hgc
                      (callcodeStarted_g10 hgc
                        (callInsfTail2_g10 hgc))))))))))
  refine HandlerRunA.dec_carry_g10 (fun t v hp => CcDLQ_setVar_g10 (by decide) hp) ?_
  refine HandlerRunA.seq_ite_unit (fun t w heval hw0 => ?_) (fun t heval => ?_)
  · refine seq_decCall_swap_g10 (contNoreadP_to_g10 callRestNoread_g10) ?_
    refine HandlerRunA.decCall hW.epsA_is_account_alive_k32
      (Q := fun t => CcDLQ_g10 s0 t) ?_ ?_ ?_
    · intro t values body' callee ret' hc hi hw hp hargs hl
      exact trivial
    · intro t values body callee retShape v cpost hi hw hp hargs hl hi_cp hw_cp hch_cp hQc
      obtain ⟨hgk, hRev, hm32⟩ := hQc
      have hRr : evmR (setVarHOLFinite (ofString "alive") v { cpost with locals := t.locals })
          = evmR cpost := (evm_congr (s := cpost)
        (t := setVarHOLFinite (ofString "alive") v { cpost with locals := t.locals }) rfl rfl).2.1
      refine CcDLQ_lu_g10
        (lu6_setVarRes_ne_g10 t cpost (ofString "alive") v (by decide)) ?_ ?_ ?_ hp
      · exact le_of_eq (hRr.trans (hRev.trans evmR_entry_eq_g10))
      · exact (globN_of_lookup_eq_g10 "ev" (hgk (ofString "ev") (by decide)).symm)
      · exact hm32
    · refine HandlerRunA.seq_ite_unit (fun t w heval hw0 => ?_) (fun t heval => ?_)
      · refine HandlerRunA.seq_assoc ?_
        refine HandlerRunA.seq_assign_local
          (fun t v hv hi hp => CcDLQ_setVar_g10 (by decide) hp) ?_
        refine HandlerRunA.seq_call (epsA_keepR_g10 epsA_charge_state_gas_k32)
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
        · exact hrest
      · exact HandlerRunA.seq_skip hrest
  · exact HandlerRunA.seq_skip hrest

/-- The `op_call` tail: everything after the prefix's `charge_gas [need]`. -/
theorem op_call_tail_g10 {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    (hW : WorldAccountSpecsCall_g10)
    (hgc : EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "generic_call")) :
    HandlerRunA s0 (fun t => CcPQ_g10 s0 t) true
      (.seq
        (.ite (.cmp .equal (.var .local (ofString "warm")) (.const (BitVec.ofNat 64 0)))
          (.call (some (none, none)) (ofString "warm_address")
            [.var .local (ofString "to")])
          .skip)
        (.decCall (ofString "dl") (.comb [.one, .one, .one])
            (ofString "calculate_delegation_cost")
          [.var .local (ofString "to")]
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
                (.dec (ofString "new_account_charged") .one (.const (BitVec.ofNat 64 0))
                  (.seq
                    (.ite (.cmp .equal (.var .local (ofString "vz"))
                        (.const (BitVec.ofNat 64 0)))
                      (.decCall (ofString "alive") .one (ofString "is_account_alive")
                        [.var .local (ofString "to")]
                        (.ite (.cmp .equal (.var .local (ofString "alive"))
                            (.const (BitVec.ofNat 64 0)))
                          (.seq (.assign .local (ofString "new_account_charged")
                              (.const (BitVec.ofNat 64 1)))
                            (.call (some (none, none)) (ofString "charge_state_gas")
                              [.const (BitVec.ofNat 64 183600)]))
                          .skip))
                      .skip)
                    callRestProg_g10))))))) :=
  callWarmIte_g10 hgc
    (callDl_g10 hW.toWorldAccountSpecsA hgc
      (callcodeCodeAddr_g10 hW.toWorldAccountSpecsA hgc
        (callcodeCode_g10 hW.toWorldAccountSpecsA hgc
          (callNacBlock_g10 hW hgc))))

/-- The full `op_call` run at the source body. -/
theorem op_call_run_full_g10 (hW : WorldAccountSpecsCall_g10)
    (hgc : EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "generic_call")) {F : Type} (s0 : PanSemStateFiniteExact 64 F) :
    HandlerRunA s0 (fun _ => EvmInv s0) false
      (sourceFnBody Guest.Software.guestFn_op_call) :=
  op_call_prefix_g10 (op_call_tail_g10 hW hgc)

/-- The `op_call` handler spec (guest AST index 603). -/
theorem op_call_specA_g10 (hW : WorldAccountSpecsCall_g10)
    (hgc : EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "generic_call")) :
    OpHandlerSpecA (ofString "op_call") := by
  refine opHandlerSpecA_of_run_seed_g10 603 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_op_call rfl ?_
  intro F s0 hInv0 hWF0 hnd0
  exact op_call_run_full_g10 hW hgc s0

end InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB
