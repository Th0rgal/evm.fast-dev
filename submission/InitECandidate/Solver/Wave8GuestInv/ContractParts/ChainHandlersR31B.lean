import InitECandidate.Solver.Wave8GuestInv.ContractParts.StrongBridgesR29
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers.U256WsSpecs
import InitECandidate.Solver.Wave8GuestInv.ContractParts.ChainHandlersR31A1
import InitECandidate.Solver.Wave8GuestInv.ContractParts.ChainHandlersR31A2

/-! # Wave 8 R31 S1: Chain-WF handler specs for the remaining opcodes (part B)

`OpHandlerChainSpec` leaves, proof-complete, for the Group 04-05 environment and block
opcodes, proved with the `Group09ChainWF.HandlerRunA` combinator framework.  Companion
to `StrongBridgesR29.RemainingChainHandlersR29`.
-/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.ContractParts.ChainHandlersR31B

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
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers
open InitECandidate.Solver.Wave8Contracts.M23
open InitECandidate.Solver.Wave8GuestInv.ContractParts.StrongBridges
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.Group09ChainWF
open InitECandidate.Solver.Wave8GuestInv.ContractParts.ChainHandlersR31A

/-! ## 1. `epsA` leaves for the environment callees -/

theorem epsA_address_to_u256_g09 :
    Group09ChainWF.EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "address_to_u256") := epsA_g10_to_g09 epsA_address_to_u256

theorem epsA_u256_from_be :
    Group09ChainWF.EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "u256_from_be") :=
  epsA_of_readOnly 86 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_from_be rfl
    opRoCallees opRoCallees_good rfl

theorem epsA_block_env :
    Group09ChainWF.EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "block_env") :=
  epsA_of_readOnly 550 (by rw [guestAst_len]; decide) Guest.Software.guestFn_block_env rfl
    opRoCallees opRoCallees_good rfl

private theorem lookup_taylor_exponential_local_g31 :
    originalRuntimeCode.lookup (ofString "taylor_exponential") =
      some ([(ofString "factor", .one), (ofString "numerator", .one), (ofString "denominator", .one)],
            InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
              (extractFn Guest.Software.guestFn_taylor_exponential).body,
            .comb [.one, .one, .one, .one]) :=
  lookup_of_guestAst_getElem 232 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_taylor_exponential) rfl

theorem epsA_calculate_blob_gas_price_g31 :
    Group09ChainWF.EvmPreservingSpecA (fun _ => True) (fun _ _ _ => True)
      (ofString "calculate_blob_gas_price") := by
  refine epsA_of_wsSafe_g31 233 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_calculate_blob_gas_price rfl ?_
  intro F s hs _
  dsimp only [extractFn, Guest.Software.guestFn_calculate_blob_gas_price,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural,
    Option.map, List.map]
  refine WsSafe.decCall ?_ ?_
  · intro vals body callee rs _ hl _
    have hraw := lookupCodeHOLFinite_eq_some s.code.lookup (ofString "taylor_exponential") vals body callee rs hl
    rw [hs.code] at hraw
    simp only [lookupCodeHOLExact, lookup_taylor_exponential_local_g31] at hraw
    split at hraw
    · have hb : body = _ := (Prod.mk.inj (Option.some.inj hraw)).1.symm
      subst body
      exact taylor_exponential_wsSafe (hs.with_locals_clock callee (s.clock - 1))
    · simp at hraw
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _
    exact WsSafe.return_exp _ _ _


theorem op_pc_specA : Group09ChainWF.OpHandlerSpecA (ofString "op_pc") := by
  refine opHandlerSpecA_of_run 505 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_pc rfl ?_
  intro F s0 hInv0 _ hnd0
  dsimp only [Guest.Software.guestFn_op_pc, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine HandlerRunA.seq_charge_gas_exact (Q := fun _ => True) ?_ ?_ ?_
  · intro t w hv _ _ _
    simp only [evalHOLExact] at hv
    injection hv with h1
    injection h1 with h2
    injection h2 with h3
    subst h3
    decide
  · intro t cpost amtw _ _ _ _ _ _ _ _ _ _
    trivial
  · exact
    HandlerRunA.seq_call_simple epsA_stack_push_word_g09 (HandlerRunA.seq_call_simple epsA_pc_add (HandlerRunA.ret _))

theorem op_pc_chainSpec : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_pc") :=
  (opHandlerChainSpec_iff _).mp (opHandlerChainSpecA_of_g09 op_pc_specA)

theorem op_gas_specA : Group09ChainWF.OpHandlerSpecA (ofString "op_gas") := by
  refine opHandlerSpecA_of_run 506 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_gas rfl ?_
  intro F s0 hInv0 _ hnd0
  dsimp only [Guest.Software.guestFn_op_gas, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine HandlerRunA.seq_charge_gas_exact (Q := fun _ => True) ?_ ?_ ?_
  · intro t w hv _ _ _
    simp only [evalHOLExact] at hv
    injection hv with h1
    injection h1 with h2
    injection h2 with h3
    subst h3
    decide
  · intro t cpost amtw _ _ _ _ _ _ _ _ _ _
    trivial
  · exact
    HandlerRunA.seq_call_simple epsA_stack_push_word_g09 (HandlerRunA.seq_call_simple epsA_pc_add (HandlerRunA.ret _))

theorem op_gas_chainSpec : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_gas") :=
  (opHandlerChainSpec_iff _).mp (opHandlerChainSpecA_of_g09 op_gas_specA)

theorem op_jumpdest_specA : Group09ChainWF.OpHandlerSpecA (ofString "op_jumpdest") := by
  refine opHandlerSpecA_of_run 507 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_jumpdest rfl ?_
  intro F s0 hInv0 _ hnd0
  dsimp only [Guest.Software.guestFn_op_jumpdest, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine HandlerRunA.seq_charge_gas_exact (Q := fun _ => True) ?_ ?_ ?_
  · intro t w hv _ _ _
    simp only [evalHOLExact] at hv
    injection hv with h1
    injection h1 with h2
    injection h2 with h3
    subst h3
    decide
  · intro t cpost amtw _ _ _ _ _ _ _ _ _ _
    trivial
  · exact
    HandlerRunA.seq_call_simple epsA_pc_add (HandlerRunA.ret _)

theorem op_jumpdest_chainSpec : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_jumpdest") :=
  (opHandlerChainSpec_iff _).mp (opHandlerChainSpecA_of_g09 op_jumpdest_specA)

theorem op_msize_specA : Group09ChainWF.OpHandlerSpecA (ofString "op_msize") := by
  refine opHandlerSpecA_of_run 511 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_msize rfl ?_
  intro F s0 hInv0 _ hnd0
  dsimp only [Guest.Software.guestFn_op_msize, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine HandlerRunA.seq_charge_gas_exact (Q := fun _ => True) ?_ ?_ ?_
  · intro t w hv _ _ _
    simp only [evalHOLExact] at hv
    injection hv with h1
    injection h1 with h2
    injection h2 with h3
    subst h3
    decide
  · intro t cpost amtw _ _ _ _ _ _ _ _ _ _
    trivial
  · exact
    HandlerRunA.seq_call_simple epsA_stack_push_word_g09 (HandlerRunA.seq_call_simple epsA_pc_add (HandlerRunA.ret _))

theorem op_msize_chainSpec : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_msize") :=
  (opHandlerChainSpec_iff _).mp (opHandlerChainSpecA_of_g09 op_msize_specA)

theorem op_pop_specA : Group09ChainWF.OpHandlerSpecA (ofString "op_pop") := by
  refine opHandlerSpecA_of_run 513 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_pop rfl ?_
  intro F s0 hInv0 _ hnd0
  dsimp only [Guest.Software.guestFn_op_pop, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine HandlerRunA.decCall_simple epsA_stack_pop ?_
  refine HandlerRunA.seq_charge_gas_exact (Q := fun _ => True) ?_ ?_ ?_
  · intro t w hv _ _ _
    simp only [evalHOLExact] at hv
    injection hv with h1
    injection h1 with h2
    injection h2 with h3
    subst h3
    decide
  · intro t cpost amtw _ _ _ _ _ _ _ _ _ _
    trivial
  · exact
    HandlerRunA.seq_call_simple epsA_pc_add (HandlerRunA.ret _)

theorem op_pop_chainSpec : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_pop") :=
  (opHandlerChainSpec_iff _).mp (opHandlerChainSpecA_of_g09 op_pop_specA)

theorem epsA_code_imm :
    Group09ChainWF.EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "code_imm") :=
  epsA_of_readOnly 518 (by rw [guestAst_len]; decide) Guest.Software.guestFn_code_imm rfl
    opRoCallees opRoCallees_good rfl

theorem lookup_decode_single :
    originalRuntimeCode.lookup (ofString "decode_single") =
      some ([(ofString "x", .one)], sourceFnBody Guest.Software.guestFn_decode_single, .one) :=
  lookup_of_guestAst_getElem 519 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_decode_single) rfl

theorem epsA_decode_single :
    Group09ChainWF.EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "decode_single") := by
  refine ⟨_, _, _, lookup_decode_single, ?_⟩
  intro F s hcode hInv hWF _ hlookup hnt
  dsimp only
  have hno_ret_err {r0 : Option (PanSemResultExact 64)} {P1 P2 : Prop}
      (h1 : ∀ v, r0 ≠ some (.returned v)) (h2 : ¬ IsEvmErr r0) :
      (∀ v, r0 = some (.returned v) → P1) ∧ (IsEvmErr r0 → P2) :=
    ⟨fun v hv => (h1 v hv).elim, fun he => (h2 he).elim⟩
  have herr_triv {P1 P2 : Prop} :
      (∀ v, (some PanSemResultExact.error : Option (PanSemResultExact 64)) = some (.returned v) → P1) ∧
      (IsEvmErr (some PanSemResultExact.error) → P2) :=
    hno_ret_err (fun _ h => by cases h) (by rintro ⟨_, h⟩; cases h)
  have hbody : sourceFnBody Guest.Software.guestFn_decode_single =
      .seq (.ite (.cmp .notEqual (.const (0#64))
          (.op .or [.cmp .notLower (.const (90#64)) (.var .local (ofString "x")),
            .cmp .notLower (.var .local (ofString "x")) (.const (128#64))]))
        (.return (.op .and [.op .add [.var .local (ofString "x"), .const (145#64)], .const (255#64)]))
        .skip)
      (.seq (.raise (ofString "EvmErr") (.const (10#64))) (.return (.const (0#64)))) := rfl
  rw [hbody, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
  split
  · rename_i w hw
    by_cases hw0 : w = 0
    · subst hw0
      simp only [↓reduceIte, evaluateHOLFiniteState_skip]
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_raise]
      dsimp only [evalHOLExact]
      cases hs_esh : s.eshapes.lookup (ofString "EvmErr") with
      | none => dsimp only; exact herr_triv
      | some sh =>
        dsimp only
        by_cases hcond : shapeOfHOLExact (.val (.word (10#64))) = sh ∧
            sizeOfShapeWithContextHOL s.structs (shapeOfHOLExact (.val (.word (10#64)))) ≤ 32
        · rw [if_pos hcond]; dsimp only
          have hInv' : EvmInv (emptyLocalsHOLFinite s) :=
            localsFree_evmInv s _ s.clock hInv
          have hwf' : HeadMemChainWF (emptyLocalsHOLFinite s) :=
            headMemChainWF_locals s _ s.clock hWF
          have hc := R11Shards.OpDispatchSpec.evm_congr (s := s) (t := emptyLocalsHOLFinite s) rfl rfl
          constructor
          · intro _ h; cases h
          · intro _
            exact ⟨⟨hInv', hwf'⟩, evmChain_congr rfl rfl, le_of_eq hc.2.1⟩
        · rw [if_neg hcond]; dsimp only; exact herr_triv
    · simp only [hw0, ↓reduceIte]
      rw [evaluateHOLFiniteState_return]
      rcases hev_ret : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
          (.op .and [.op .add [.var .local (ofString "x"), .const (145#64)], .const (255#64)]) with _ | rv
      · dsimp only; exact herr_triv
      · dsimp only
        by_cases hsz : sizeOfShapeWithContextHOL s.structs (shapeOfHOLExact rv) ≤ 32
        · rw [if_pos hsz]; dsimp only
          have hInv' : EvmInv (emptyLocalsHOLFinite s) := localsFree_evmInv s _ s.clock hInv
          have hwf' : HeadMemChainWF (emptyLocalsHOLFinite s) :=
            headMemChainWF_locals s _ s.clock hWF
          have hc := R11Shards.OpDispatchSpec.evm_congr (s := s) (t := emptyLocalsHOLFinite s) rfl rfl
          exact ⟨fun _ _ => ⟨⟨hInv', hwf'⟩, evmChain_congr rfl rfl, le_of_eq hc.2.1, rfl⟩,
            by rintro ⟨_, h⟩; cases h⟩
        · rw [if_neg hsz]; dsimp only; exact herr_triv
  · dsimp only; exact herr_triv


end InitECandidate.Solver.Wave8GuestInv.ContractParts.ChainHandlersR31B

/-! ## 2. Extra `HandlerRunA` combinators (adapted from the plain framework) -/
namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB
namespace Group09ChainWF

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
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers
open InitECandidate.Solver.Wave8Contracts.M23

local notation "evmR" => R11Shards.OpDispatchSpec.evmR

theorem HandlerRunA.dec_simple {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {charged : Bool} {nm : MlS} {sh : ShapeHOL} {init : ExpHOL 64} {body : ProgHOL 64}
    (hbody : Group09ChainWF.HandlerRunA s0 (fun _ => True) charged body) :
    Group09ChainWF.HandlerRunA s0 (fun _ => True) charged (.dec nm sh init body) :=
  Group09ChainWF.HandlerRunA.dec (fun _ _ _ _ _ _ => trivial) hbody

theorem HandlerRunA.raise_other {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {P : PanSemStateFiniteExact 64 F → Prop} {charged : Bool} {eid : MlS}
    (hne : eid ≠ ofString "EvmErr") (e : ExpHOL 64) :
    Group09ChainWF.HandlerRunA s0 P charged (.raise eid e) := by
  intro t _ _ _ _ _ _ _
  rw [evaluateHOLFiniteState_raise]
  split
  · dsimp only
    split
    · refine opDispatchPostA_other (fun _ h => by cases h) ?_
      rintro ⟨_, h⟩; injection h with h'; injection h' with h1 _; exact hne h1
    · exact opDispatchPostA_error s0 t
  · exact opDispatchPostA_error s0 t

theorem HandlerRunA.seq_ite_nonfallthrough_skip {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {P : PanSemStateFiniteExact 64 F → Prop} {charged : Bool}
    {cond : ExpHOL 64} {yes cont : ProgHOL 64}
    (hnn : ∀ u : PanSemStateFiniteExact 64 F, (evaluateHOLFiniteState u yes).1 ≠ none)
    (hyes : Group09ChainWF.HandlerRunA s0 P charged yes)
    (hcont : Group09ChainWF.HandlerRunA s0 P charged cont) :
    Group09ChainWF.HandlerRunA s0 P charged (.seq (.ite cond yes .skip) cont) := by
  intro t hc hi hwf hlen hR hP hnt
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt ⊢
  revert hnt
  split
  · rename_i w hw
    by_cases hw0 : w = 0
    · subst hw0; simp only [↓reduceIte, evaluateHOLFiniteState_skip]
      intro hnt; exact hcont t hc hi hwf hlen hR hP hnt
    · simp only [hw0, ↓reduceIte]
      have hy_nn := hnn t
      rcases hy : evaluateHOLFiniteState t yes with ⟨ry, sy⟩
      rw [hy] at hy_nn
      cases ry with
      | none => exact absurd rfl hy_nn
      | some r0 =>
        dsimp only; intro hnt
        have hr := hyes t hc hi hwf hlen hR hP (by rw [hy]; exact hnt)
        rw [hy] at hr; exact hr
  · intro _; exact opDispatchPostA_error s0 t

theorem HandlerRunA.seq_ite_other_skip {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {P : PanSemStateFiniteExact 64 F → Prop} {charged : Bool}
    {cond : ExpHOL 64} {eid : MlS} {errExp : ExpHOL 64} {cont : ProgHOL 64}
    (hne : eid ≠ ofString "EvmErr")
    (hcont : Group09ChainWF.HandlerRunA s0 P charged cont) :
    Group09ChainWF.HandlerRunA s0 P charged (.seq (.ite cond (.raise eid errExp) .skip) cont) := by
  refine Group09ChainWF.HandlerRunA.seq_ite_nonfallthrough_skip ?_ (Group09ChainWF.HandlerRunA.raise_other hne errExp) hcont
  intro u
  rw [evaluateHOLFiniteState_raise]
  split
  · dsimp only; split <;> simp
  · simp

theorem HandlerRunA.seq_ite_simple {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {charged : Bool} {cond : ExpHOL 64} {yes no cont : ProgHOL 64}
    (hyes : Group09ChainWF.HandlerRunA s0 (fun _ => True) charged (.seq yes cont))
    (hno : Group09ChainWF.HandlerRunA s0 (fun _ => True) charged (.seq no cont)) :
    Group09ChainWF.HandlerRunA s0 (fun _ => True) charged (.seq (.ite cond yes no) cont) := by
  intro t hc hi hwf hlen hR _ hnt
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt ⊢
  revert hnt
  split
  · rename_i w hw
    by_cases hw0 : w = 0
    · subst hw0; simp only [↓reduceIte]
      rw [← evaluateHOLFiniteState_seq_line780]
      intro hnt; exact hno t hc hi hwf hlen hR trivial hnt
    · simp only [hw0, ↓reduceIte]
      rw [← evaluateHOLFiniteState_seq_line780]
      intro hnt; exact hyes t hc hi hwf hlen hR trivial hnt
  · intro _; exact opDispatchPostA_error s0 t

theorem HandlerRunA.seq_decCall_call_simple {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {Q1 Q2 : ∀ {F : Type}, PanSemStateFiniteExact 64 F → ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    {charged : Bool}
    {nm : MlS} {sh : ShapeHOL} {fn1 fn2 : MlS} {args1 args2 : List (ExpHOL 64)} {cont : ProgHOL 64}
    (hf1 : Group09ChainWF.EvmPreservingSpecA (fun _ => True) Q1 fn1)
    (hf2 : Group09ChainWF.EvmPreservingSpecA (fun _ => True) Q2 fn2)
    (hcont : Group09ChainWF.HandlerRunA s0 (fun _ => True) charged cont) :
    Group09ChainWF.HandlerRunA s0 (fun _ => True) charged
      (.seq (.decCall nm sh fn1 args1 (.call (some (none, none)) fn2 args2)) cont) := by
  intro t hc hi hwf hlen hR _ hnt
  obtain ⟨params1, body1, ret1, hlook1, hspec1⟩ := hf1
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt ⊢
  rcases hargs1 : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) args1 with _ | vals1
  · exact opDispatchPostA_error s0 t
  · simp only [hargs1] at hnt ⊢
    rcases hl1 : lookupCodeHOLFinite t.code.lookup fn1 vals1 with _ | ⟨body1', callee1, ret1'⟩
    · exact opDispatchPostA_error s0 t
    · simp only [hl1] at hnt ⊢
      by_cases hz1 : t.clock = 0
      · simp [hz1] at hnt
      · simp only [hz1, ↓reduceIte] at hnt ⊢
        have hb1 : body1' = body1 :=
          lookupCodeHOLFinite_installed_body t.code.lookup fn1 params1 body1 body1'
            ret1 ret1' vals1 callee1 (by rw [hc]; exact hlook1) hl1
        subst body1'
        have hr1 : ret1' = ret1 := by
          have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
            t.code.lookup fn1 vals1 body1 callee1 ret1' hl1
          rw [hc] at hx; simp only [Flapjack.lookupCodeHOLExact, hlook1] at hx
          split at hx
          · exact (congrArg (fun x => x.2.2) (Option.some.inj hx)).symm
          · cases hx
        subst ret1'
        have hInv_ce1 : EvmInv (callEntryStateHOLFinite t callee1) :=
          localsFree_evmInv t callee1 (t.clock - 1) hi
        have hWF_ce1 : HeadMemChainWF (callEntryStateHOLFinite t callee1) :=
          headMemChainWF_locals t callee1 (t.clock - 1) hwf
        have hl1_orig : lookupCodeHOLFinite originalRuntimeCode.lookup fn1 vals1 =
            some (body1, callee1, ret1) := by rwa [← hc]
        have hmeta1 := (PanRunBounded.evaluateHOLFiniteState_metadata
          (callEntryStateHOLFinite t callee1) body1).1
        rcases hrun1 : evaluateHOLFiniteState (callEntryStateHOLFinite t callee1) body1 with ⟨res1, cpost1⟩
        simp only [hrun1] at hnt hmeta1 ⊢
        change cpost1.code = t.code at hmeta1
        have hc_ce1 := R11Shards.OpDispatchSpec.evm_congr (s := t) (t := callEntryStateHOLFinite t callee1) rfl rfl
        have hQ1 (hsafe : res1 ≠ some .timeOut) :
            (∀ v, res1 = some (.returned v) →
              (EvmInv cpost1 ∧ HeadMemChainWF cpost1) ∧
              evmChain cpost1 = evmChain (callEntryStateHOLFinite t callee1) ∧
              evmR cpost1 ≤ evmR (callEntryStateHOLFinite t callee1) ∧
              Q1 (callEntryStateHOLFinite t callee1) v cpost1) ∧
            (IsEvmErr res1 →
              (EvmInv cpost1 ∧ HeadMemChainWF cpost1) ∧
              evmChain cpost1 = evmChain (callEntryStateHOLFinite t callee1) ∧
              evmR cpost1 ≤ evmR (callEntryStateHOLFinite t callee1)) := by
          have hs := hspec1 (callEntryStateHOLFinite t callee1) hc hInv_ce1 hWF_ce1 trivial
            ⟨vals1, hl1_orig⟩ (by rw [hrun1]; exact hsafe)
          dsimp only at hs; rw [hrun1] at hs; exact hs
        cases res1 with
        | none => exact opDispatchPostA_error s0 cpost1
        | some r1 =>
          cases r1 with
          | timeOut => simp at hnt
          | returned v1 =>
            dsimp only at hnt ⊢
            by_cases hsh1 : (shapeEqHOL (shapeOfHOLExact v1) sh && shapeEqHOL (shapeOfHOLExact v1) ret1) = true
            · rw [if_pos hsh1] at hnt ⊢
              dsimp only at hnt ⊢
              obtain ⟨⟨hInv_cp1, hWF_cp1⟩, hch_cp1, hR_cp1, _⟩ := (hQ1 (by simp)).1 v1 rfl
              let u := setVarHOLFinite nm v1 { cpost1 with locals := t.locals }
              have hcode_u : u.code = originalRuntimeCode := hmeta1.trans hc
              have hInv_u : EvmInv u := localsFree_evmInv cpost1 u.locals cpost1.clock hInv_cp1
              have hWF_u : HeadMemChainWF u := headMemChainWF_locals cpost1 u.locals cpost1.clock hWF_cp1
              have hc_u := R11Shards.OpDispatchSpec.evm_congr (s := cpost1) (t := u) rfl rfl
              have hlen_u : (evmChain u).length = (evmChain s0).length := by
                rw [hc_u.2.2.1, hch_cp1, hc_ce1.2.2.1]; exact hlen
              have hR_u : if charged then evmR u < evmR s0 else evmR u ≤ evmR s0 :=
                rboundA_step_g09
                  (by have h1 := hc_u.2.1; have h2 := hc_ce1.2.1; have h3 := hR_cp1; omega) hR
              have hcall_ret : Group09ChainWF.HandlerRunA s0 (fun _ => True) charged
                  (.seq (.call (some (none, none)) fn2 args2) (.raise (ofString "EvmErr") (.const 0))) :=
                Group09ChainWF.HandlerRunA.seq_call_simple hf2 (Group09ChainWF.HandlerRunA.raise_evmErr (.const 0))
              obtain ⟨params2, body2, ret2, hlook2, hspec2⟩ := hf2
              have hfold_u : setVarHOLFinite nm v1 { cpost1 with locals := t.locals } = u := rfl
              rw [hfold_u] at hnt ⊢
              rcases hev2 : evaluateHOLFiniteState u (.call (some (none, none)) fn2 args2) with ⟨r2, sp2⟩
              simp only [hev2] at hnt ⊢
              cases r2 with
              | some rr =>
                dsimp only at hnt ⊢
                have hcall := hcall_ret u hcode_u hInv_u hWF_u hlen_u hR_u trivial
                rw [evaluateHOLFiniteState_seq_line780, hev2] at hcall
                dsimp only at hcall
                exact opDispatchPostA_congr_lc rfl (hcall hnt)
              | none =>
                dsimp only at hnt ⊢
                rw [evaluateHOLFiniteState_call] at hev2
                rcases hargs2 : evalListHOLFinite u (h := fun a => Classical.propDecidable (u.memaddrs a)) args2 with _ | vals2
                · rw [hargs2] at hev2; simp at hev2
                · rw [hargs2] at hev2; dsimp only at hev2
                  rcases hl2 : lookupCodeHOLFinite u.code.lookup fn2 vals2 with _ | ⟨body2', callee2, ret2'⟩
                  · rw [hl2] at hev2; simp at hev2
                  · rw [hl2] at hev2; dsimp only at hev2
                    by_cases hz2 : u.clock = 0
                    · rw [if_pos hz2] at hev2; simp at hev2
                    · rw [if_neg hz2] at hev2
                      have hb2 : body2' = body2 :=
                        lookupCodeHOLFinite_installed_body u.code.lookup fn2 params2 body2 body2'
                          ret2 ret2' vals2 callee2 (by rw [hcode_u]; exact hlook2) hl2
                      subst body2'
                      have hr2 : ret2' = ret2 := by
                        have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
                          u.code.lookup fn2 vals2 body2 callee2 ret2' hl2
                        rw [hcode_u] at hx; simp only [Flapjack.lookupCodeHOLExact, hlook2] at hx
                        split at hx
                        · exact (congrArg (fun x => x.2.2) (Option.some.inj hx)).symm
                        · cases hx
                      subst ret2'
                      have hInv_ce2 : EvmInv (callEntryStateHOLFinite u callee2) :=
                        localsFree_evmInv u callee2 (u.clock - 1) hInv_u
                      have hWF_ce2 : HeadMemChainWF (callEntryStateHOLFinite u callee2) :=
                        headMemChainWF_locals u callee2 (u.clock - 1) hWF_u
                      have hl2_orig : lookupCodeHOLFinite originalRuntimeCode.lookup fn2 vals2 =
                          some (body2, callee2, ret2) := by rwa [← hcode_u]
                      have hmeta2 := (PanRunBounded.evaluateHOLFiniteState_metadata
                        (callEntryStateHOLFinite u callee2) body2).1
                      rcases hrun2 : evaluateHOLFiniteState (callEntryStateHOLFinite u callee2) body2 with ⟨res2, cpost2⟩
                      rw [hrun2] at hev2 hmeta2
                      change cpost2.code = u.code at hmeta2
                      cases res2 with
                      | none => simp at hev2
                      | some rr2 =>
                        cases rr2 with
                        | returned v2 =>
                          dsimp only at hev2
                          split at hev2
                          · injection hev2 with _ hsp2
                            subst sp2
                            have hs2 := hspec2 (callEntryStateHOLFinite u callee2) hcode_u hInv_ce2
                              hWF_ce2 trivial ⟨vals2, hl2_orig⟩ (by rw [hrun2]; simp)
                            dsimp only at hs2; rw [hrun2] at hs2; dsimp only at hs2
                            obtain ⟨⟨hInv_cp2, hWF_cp2⟩, hch_cp2, hR_cp2, _⟩ := hs2.1 v2 rfl
                            have hc_ce2 := R11Shards.OpDispatchSpec.evm_congr (s := u) (t := callEntryStateHOLFinite u callee2) rfl rfl
                            let restored : PanSemStateFiniteExact 64 F :=
                              { cpost2 with locals := HolFiniteMapExact.resVarEq u.locals (nm, t.locals.lookup nm) }
                            have hcode_rest : restored.code = originalRuntimeCode := hmeta2.trans hcode_u
                            have hInv_rest : EvmInv restored :=
                              localsFree_evmInv cpost2 restored.locals cpost2.clock hInv_cp2
                            have hWF_rest : HeadMemChainWF restored :=
                              headMemChainWF_locals cpost2 restored.locals cpost2.clock hWF_cp2
                            have hc_rest := R11Shards.OpDispatchSpec.evm_congr (s := cpost2) (t := restored) rfl rfl
                            have hlen_rest : (evmChain restored).length = (evmChain s0).length := by
                              rw [hc_rest.2.2.1, hch_cp2, hc_ce2.2.2.1]; exact hlen_u
                            have hR_rest : if charged then evmR restored < evmR s0 else evmR restored ≤ evmR s0 :=
                              rboundA_step_g09
                                (by have h1 := hc_rest.2.1; have h2 := hc_ce2.2.1; have h3 := hR_cp2; omega) hR_u
                            exact hcont restored hcode_rest hInv_rest hWF_rest hlen_rest hR_rest trivial hnt
                          · simp at hev2
                        | timeOut | exception _ _ | «break» | «continue» | finalFfi _ | error => simp at hev2
            · rw [if_neg hsh1] at hnt ⊢
              exact opDispatchPostA_error s0 cpost1
          | exception eid ev =>
            by_cases heid : eid = ofString "EvmErr"
            · subst heid
              obtain ⟨⟨hInv_cp1, hWF_cp1⟩, hch_cp1, hR_cp1⟩ := (hQ1 (by simp)).2 ⟨ev, rfl⟩
              have hInv_el : EvmInv cpost1.emptyLocalsHOLFinite :=
                localsFree_evmInv cpost1 _ cpost1.clock hInv_cp1
              have hWF_el : HeadMemChainWF cpost1.emptyLocalsHOLFinite :=
                headMemChainWF_locals cpost1 _ cpost1.clock hWF_cp1
              have hc_el := R11Shards.OpDispatchSpec.evm_congr (s := cpost1) (t := cpost1.emptyLocalsHOLFinite) rfl rfl
              refine ⟨?_, fun _ => ⟨⟨hInv_el, hWF_el⟩, ?_, ?_⟩⟩
              · rintro ⟨_, h⟩; cases h
              · rw [hc_el.2.2.1, hch_cp1, hc_ce1.2.2.1]; exact hlen
              · dsimp only
                have h0 := rboundA_to_le_g09 hR
                have h1 := hc_el.2.1
                have h2 := hc_ce1.2.1
                have h3 := hR_cp1
                omega
            · refine opDispatchPostA_other (fun _ h => by cases h) ?_
              rintro ⟨_, h⟩; injection h with h'; injection h' with h1 _; exact heid h1
          | «break» => exact opDispatchPostA_error s0 cpost1
          | «continue» => exact opDispatchPostA_error s0 cpost1
          | finalFfi _ =>
            refine opDispatchPostA_other (fun _ h => by cases h) ?_
            rintro ⟨_, h⟩; cases h
          | error => exact opDispatchPostA_error s0 cpost1.emptyLocalsHOLFinite



theorem HandlerRunA.seq_ite_raise_skip {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {P Q : PanSemStateFiniteExact 64 F → Prop} {charged : Bool}
    {cond : ExpHOL 64} {errExp : ExpHOL 64} {cont : ProgHOL 64}
    (hfalse : ∀ t,
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) cond = some (.val (.word 0)) →
      EvmInv t → P t → Q t)
    (hcont : HandlerRunA s0 Q charged cont) :
    HandlerRunA s0 P charged (.seq (.ite cond (.raise (ofString "EvmErr") errExp) .skip) cont) := by
  intro t hc hi hwf hlen hR hp hn
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hn ⊢
  revert hn
  split
  · rename_i w he
    by_cases hz : w = 0
    · subst hz; simp only [↓reduceIte, evaluateHOLFiniteState_skip]
      intro hn; exact hcont t hc hi hwf hlen hR (hfalse t he hi hp) hn
    · simp only [hz, ↓reduceIte]
      rcases hraise : evaluateHOLFiniteState t (.raise (ofString "EvmErr") errExp) with ⟨rr, sr⟩
      cases rr with
      | none => exact absurd hraise (fun h => raise_ne_none t _ errExp (by rw [h]))
      | some _ =>
        dsimp only; intro hn
        have hr := (HandlerRunA.raise_evmErr (P := P) (charged := charged) errExp) t hc hi hwf hlen hR hp
          (by rw [hraise]; exact hn)
        rw [hraise] at hr; exact hr
  · intro _; exact opDispatchPostA_error s0 t

end Group09ChainWF
end InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB

namespace InitECandidate.Solver.Wave8GuestInv.ContractParts.ChainHandlersR31B
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
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers
open InitECandidate.Solver.Wave8Contracts.M23
open InitECandidate.Solver.Wave8GuestInv.ContractParts.StrongBridges
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.Group09ChainWF
open InitECandidate.Solver.Wave8GuestInv.ContractParts.ChainHandlersR31A

local notation "evmR" => R11Shards.OpDispatchSpec.evmR

/-! ## 3. The simple environment and block handlers -/

theorem op_address_specA : Group09ChainWF.OpHandlerSpecA (ofString "op_address") := by
  refine opHandlerSpecA_of_run 531 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_address rfl ?_
  intro F s0 hInv0 _ hnd0
  dsimp only [Guest.Software.guestFn_op_address, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine Group09ChainWF.HandlerRunA.seq_charge_gas_exact (Q := fun _ => True) ?_ ?_ ?_
  · intro t w hv _ _ _
    simp only [evalHOLExact] at hv
    injection hv with h1
    injection h1 with h2
    injection h2 with h3
    subst h3
    decide
  · intro t cpost amtw _ _ _ _ _ _ _ _ _ _
    trivial
  · exact Group09ChainWF.HandlerRunA.decCall_simple epsA_address_to_u256_g09 (Group09ChainWF.HandlerRunA.seq_call_simple epsA_stack_push_g09 (Group09ChainWF.HandlerRunA.seq_call_simple epsA_pc_add (Group09ChainWF.HandlerRunA.ret _)))

theorem op_address_chainSpec : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_address") :=
  (opHandlerChainSpec_iff _).mp (opHandlerChainSpecA_of_g09 op_address_specA)

theorem op_origin_specA : Group09ChainWF.OpHandlerSpecA (ofString "op_origin") := by
  refine opHandlerSpecA_of_run 533 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_origin rfl ?_
  intro F s0 hInv0 _ hnd0
  dsimp only [Guest.Software.guestFn_op_origin, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine Group09ChainWF.HandlerRunA.seq_charge_gas_exact (Q := fun _ => True) ?_ ?_ ?_
  · intro t w hv _ _ _
    simp only [evalHOLExact] at hv
    injection hv with h1
    injection h1 with h2
    injection h2 with h3
    subst h3
    decide
  · intro t cpost amtw _ _ _ _ _ _ _ _ _ _
    trivial
  · exact Group09ChainWF.HandlerRunA.dec_simple (Group09ChainWF.HandlerRunA.decCall_simple epsA_address_to_u256_g09 (Group09ChainWF.HandlerRunA.seq_call_simple epsA_stack_push_g09 (Group09ChainWF.HandlerRunA.seq_call_simple epsA_pc_add (Group09ChainWF.HandlerRunA.ret _))))

theorem op_origin_chainSpec : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_origin") :=
  (opHandlerChainSpec_iff _).mp (opHandlerChainSpecA_of_g09 op_origin_specA)

theorem op_caller_specA : Group09ChainWF.OpHandlerSpecA (ofString "op_caller") := by
  refine opHandlerSpecA_of_run 534 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_caller rfl ?_
  intro F s0 hInv0 _ hnd0
  dsimp only [Guest.Software.guestFn_op_caller, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine Group09ChainWF.HandlerRunA.seq_charge_gas_exact (Q := fun _ => True) ?_ ?_ ?_
  · intro t w hv _ _ _
    simp only [evalHOLExact] at hv
    injection hv with h1
    injection h1 with h2
    injection h2 with h3
    subst h3
    decide
  · intro t cpost amtw _ _ _ _ _ _ _ _ _ _
    trivial
  · exact Group09ChainWF.HandlerRunA.decCall_simple epsA_address_to_u256_g09 (Group09ChainWF.HandlerRunA.seq_call_simple epsA_stack_push_g09 (Group09ChainWF.HandlerRunA.seq_call_simple epsA_pc_add (Group09ChainWF.HandlerRunA.ret _)))

theorem op_caller_chainSpec : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_caller") :=
  (opHandlerChainSpec_iff _).mp (opHandlerChainSpecA_of_g09 op_caller_specA)

theorem op_callvalue_specA : Group09ChainWF.OpHandlerSpecA (ofString "op_callvalue") := by
  refine opHandlerSpecA_of_run 535 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_callvalue rfl ?_
  intro F s0 hInv0 _ hnd0
  dsimp only [Guest.Software.guestFn_op_callvalue, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine Group09ChainWF.HandlerRunA.seq_charge_gas_exact (Q := fun _ => True) ?_ ?_ ?_
  · intro t w hv _ _ _
    simp only [evalHOLExact] at hv
    injection hv with h1
    injection h1 with h2
    injection h2 with h3
    subst h3
    decide
  · intro t cpost amtw _ _ _ _ _ _ _ _ _ _
    trivial
  · exact Group09ChainWF.HandlerRunA.seq_call_simple epsA_stack_push_g09 (Group09ChainWF.HandlerRunA.seq_call_simple epsA_pc_add (Group09ChainWF.HandlerRunA.ret _))

theorem op_callvalue_chainSpec : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_callvalue") :=
  (opHandlerChainSpec_iff _).mp (opHandlerChainSpecA_of_g09 op_callvalue_specA)

theorem op_calldatasize_specA : Group09ChainWF.OpHandlerSpecA (ofString "op_calldatasize") := by
  refine opHandlerSpecA_of_run 537 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_calldatasize rfl ?_
  intro F s0 hInv0 _ hnd0
  dsimp only [Guest.Software.guestFn_op_calldatasize, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine Group09ChainWF.HandlerRunA.seq_charge_gas_exact (Q := fun _ => True) ?_ ?_ ?_
  · intro t w hv _ _ _
    simp only [evalHOLExact] at hv
    injection hv with h1
    injection h1 with h2
    injection h2 with h3
    subst h3
    decide
  · intro t cpost amtw _ _ _ _ _ _ _ _ _ _
    trivial
  · exact Group09ChainWF.HandlerRunA.seq_call_simple epsA_stack_push_word_g09 (Group09ChainWF.HandlerRunA.seq_call_simple epsA_pc_add (Group09ChainWF.HandlerRunA.ret _))

theorem op_calldatasize_chainSpec : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_calldatasize") :=
  (opHandlerChainSpec_iff _).mp (opHandlerChainSpecA_of_g09 op_calldatasize_specA)

theorem op_codesize_specA : Group09ChainWF.OpHandlerSpecA (ofString "op_codesize") := by
  refine opHandlerSpecA_of_run 540 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_codesize rfl ?_
  intro F s0 hInv0 _ hnd0
  dsimp only [Guest.Software.guestFn_op_codesize, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine Group09ChainWF.HandlerRunA.seq_charge_gas_exact (Q := fun _ => True) ?_ ?_ ?_
  · intro t w hv _ _ _
    simp only [evalHOLExact] at hv
    injection hv with h1
    injection h1 with h2
    injection h2 with h3
    subst h3
    decide
  · intro t cpost amtw _ _ _ _ _ _ _ _ _ _
    trivial
  · exact Group09ChainWF.HandlerRunA.seq_call_simple epsA_stack_push_word_g09 (Group09ChainWF.HandlerRunA.seq_call_simple epsA_pc_add (Group09ChainWF.HandlerRunA.ret _))

theorem op_codesize_chainSpec : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_codesize") :=
  (opHandlerChainSpec_iff _).mp (opHandlerChainSpecA_of_g09 op_codesize_specA)

theorem op_gasprice_specA : Group09ChainWF.OpHandlerSpecA (ofString "op_gasprice") := by
  refine opHandlerSpecA_of_run 542 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_gasprice rfl ?_
  intro F s0 hInv0 _ hnd0
  dsimp only [Guest.Software.guestFn_op_gasprice, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine Group09ChainWF.HandlerRunA.seq_charge_gas_exact (Q := fun _ => True) ?_ ?_ ?_
  · intro t w hv _ _ _
    simp only [evalHOLExact] at hv
    injection hv with h1
    injection h1 with h2
    injection h2 with h3
    subst h3
    decide
  · intro t cpost amtw _ _ _ _ _ _ _ _ _ _
    trivial
  · exact Group09ChainWF.HandlerRunA.dec_simple (Group09ChainWF.HandlerRunA.seq_call_simple epsA_stack_push_g09 (Group09ChainWF.HandlerRunA.seq_call_simple epsA_pc_add (Group09ChainWF.HandlerRunA.ret _)))

theorem op_gasprice_chainSpec : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_gasprice") :=
  (opHandlerChainSpec_iff _).mp (opHandlerChainSpecA_of_g09 op_gasprice_specA)

theorem op_returndatasize_specA : Group09ChainWF.OpHandlerSpecA (ofString "op_returndatasize") := by
  refine opHandlerSpecA_of_run 546 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_returndatasize rfl ?_
  intro F s0 hInv0 _ hnd0
  dsimp only [Guest.Software.guestFn_op_returndatasize, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine Group09ChainWF.HandlerRunA.seq_charge_gas_exact (Q := fun _ => True) ?_ ?_ ?_
  · intro t w hv _ _ _
    simp only [evalHOLExact] at hv
    injection hv with h1
    injection h1 with h2
    injection h2 with h3
    subst h3
    decide
  · intro t cpost amtw _ _ _ _ _ _ _ _ _ _
    trivial
  · exact Group09ChainWF.HandlerRunA.seq_call_simple epsA_stack_push_word_g09 (Group09ChainWF.HandlerRunA.seq_call_simple epsA_pc_add (Group09ChainWF.HandlerRunA.ret _))

theorem op_returndatasize_chainSpec : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_returndatasize") :=
  (opHandlerChainSpec_iff _).mp (opHandlerChainSpecA_of_g09 op_returndatasize_specA)

theorem op_gaslimit_specA : Group09ChainWF.OpHandlerSpecA (ofString "op_gaslimit") := by
  refine opHandlerSpecA_of_run 558 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_gaslimit rfl ?_
  intro F s0 hInv0 _ hnd0
  dsimp only [Guest.Software.guestFn_op_gaslimit, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine Group09ChainWF.HandlerRunA.seq_charge_gas_exact (Q := fun _ => True) ?_ ?_ ?_
  · intro t w hv _ _ _
    simp only [evalHOLExact] at hv
    injection hv with h1
    injection h1 with h2
    injection h2 with h3
    subst h3
    decide
  · intro t cpost amtw _ _ _ _ _ _ _ _ _ _
    trivial
  · exact Group09ChainWF.HandlerRunA.decCall_simple epsA_block_env (Group09ChainWF.HandlerRunA.seq_call_simple epsA_stack_push_word_g09 (Group09ChainWF.HandlerRunA.seq_call_simple epsA_pc_add (Group09ChainWF.HandlerRunA.ret _)))

theorem op_gaslimit_chainSpec : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_gaslimit") :=
  (opHandlerChainSpec_iff _).mp (opHandlerChainSpecA_of_g09 op_gaslimit_specA)

theorem op_chainid_specA : Group09ChainWF.OpHandlerSpecA (ofString "op_chainid") := by
  refine opHandlerSpecA_of_run 559 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_chainid rfl ?_
  intro F s0 hInv0 _ hnd0
  dsimp only [Guest.Software.guestFn_op_chainid, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine Group09ChainWF.HandlerRunA.seq_charge_gas_exact (Q := fun _ => True) ?_ ?_ ?_
  · intro t w hv _ _ _
    simp only [evalHOLExact] at hv
    injection hv with h1
    injection h1 with h2
    injection h2 with h3
    subst h3
    decide
  · intro t cpost amtw _ _ _ _ _ _ _ _ _ _
    trivial
  · exact Group09ChainWF.HandlerRunA.decCall_simple epsA_block_env (Group09ChainWF.HandlerRunA.seq_call_simple epsA_stack_push_word_g09 (Group09ChainWF.HandlerRunA.seq_call_simple epsA_pc_add (Group09ChainWF.HandlerRunA.ret _)))

theorem op_chainid_chainSpec : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_chainid") :=
  (opHandlerChainSpec_iff _).mp (opHandlerChainSpecA_of_g09 op_chainid_specA)

theorem op_basefee_specA : Group09ChainWF.OpHandlerSpecA (ofString "op_basefee") := by
  refine opHandlerSpecA_of_run 551 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_basefee rfl ?_
  intro F s0 hInv0 _ hnd0
  dsimp only [Guest.Software.guestFn_op_basefee, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine Group09ChainWF.HandlerRunA.seq_charge_gas_exact (Q := fun _ => True) ?_ ?_ ?_
  · intro t w hv _ _ _
    simp only [evalHOLExact] at hv
    injection hv with h1
    injection h1 with h2
    injection h2 with h3
    subst h3
    decide
  · intro t cpost amtw _ _ _ _ _ _ _ _ _ _
    trivial
  · exact Group09ChainWF.HandlerRunA.decCall_simple epsA_block_env (Group09ChainWF.HandlerRunA.seq_call_simple epsA_stack_push_g09 (Group09ChainWF.HandlerRunA.seq_call_simple epsA_pc_add (Group09ChainWF.HandlerRunA.ret _)))

theorem op_basefee_chainSpec : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_basefee") :=
  (opHandlerChainSpec_iff _).mp (opHandlerChainSpecA_of_g09 op_basefee_specA)

theorem op_blobhash_specA : Group09ChainWF.OpHandlerSpecA (ofString "op_blobhash") := by
  refine opHandlerSpecA_of_run 552 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_blobhash rfl ?_
  intro F s0 hInv0 _ hnd0
  dsimp only [Guest.Software.guestFn_op_blobhash, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine Group09ChainWF.HandlerRunA.decCall_simple epsA_stack_pop ?_
  refine Group09ChainWF.HandlerRunA.seq_charge_gas_exact (Q := fun _ => True) ?_ ?_ ?_
  · intro t w hv _ _ _
    simp only [evalHOLExact] at hv
    injection hv with h1
    injection h1 with h2
    injection h2 with h3
    subst h3
    decide
  · intro t cpost amtw _ _ _ _ _ _ _ _ _ _
    trivial
  · exact
    Group09ChainWF.HandlerRunA.dec_simple (Group09ChainWF.HandlerRunA.dec_simple (Group09ChainWF.HandlerRunA.decCall_simple epsA_sat_word_g09 (Group09ChainWF.HandlerRunA.seq_ite_simple (Group09ChainWF.HandlerRunA.seq_decCall_call_simple epsA_u256_from_be epsA_stack_push_g09 (Group09ChainWF.HandlerRunA.seq_call_simple epsA_pc_add (Group09ChainWF.HandlerRunA.ret _))) (Group09ChainWF.HandlerRunA.seq_call_simple epsA_stack_push_g09 (Group09ChainWF.HandlerRunA.seq_call_simple epsA_pc_add (Group09ChainWF.HandlerRunA.ret _))))))

theorem op_blobbasefee_specA : Group09ChainWF.OpHandlerSpecA (ofString "op_blobbasefee") := by
  refine opHandlerSpecA_of_run 553 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_blobbasefee rfl ?_
  intro F s0 hInv0 _ hnd0
  dsimp only [Guest.Software.guestFn_op_blobbasefee, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine Group09ChainWF.HandlerRunA.seq_charge_gas_exact (Q := fun _ => True) ?_ ?_ ?_
  · intro t w hv _ _ _
    simp only [evalHOLExact] at hv
    injection hv with h1
    injection h1 with h2
    injection h2 with h3
    subst h3
    decide
  · intro t cpost amtw _ _ _ _ _ _ _ _ _ _
    trivial
  · exact Group09ChainWF.HandlerRunA.decCall_simple epsA_block_env (Group09ChainWF.HandlerRunA.decCall_simple epsA_calculate_blob_gas_price_g31 (Group09ChainWF.HandlerRunA.seq_call_simple epsA_stack_push_g09 (Group09ChainWF.HandlerRunA.seq_call_simple epsA_pc_add (Group09ChainWF.HandlerRunA.ret _))))

theorem op_blobbasefee_chainSpec : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_blobbasefee") :=
  (opHandlerChainSpec_iff _).mp (opHandlerChainSpecA_of_g09 op_blobbasefee_specA)

theorem op_slotnum_specA : Group09ChainWF.OpHandlerSpecA (ofString "op_slotnum") := by
  refine opHandlerSpecA_of_run 561 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_slotnum rfl ?_
  intro F s0 hInv0 _ hnd0
  dsimp only [Guest.Software.guestFn_op_slotnum, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine Group09ChainWF.HandlerRunA.seq_charge_gas_exact (Q := fun _ => True) ?_ ?_ ?_
  · intro t w hv _ _ _
    simp only [evalHOLExact] at hv
    injection hv with h1
    injection h1 with h2
    injection h2 with h3
    subst h3
    decide
  · intro t cpost amtw _ _ _ _ _ _ _ _ _ _
    trivial
  · exact Group09ChainWF.HandlerRunA.decCall_simple epsA_block_env (Group09ChainWF.HandlerRunA.seq_call_simple epsA_stack_push_word_g09 (Group09ChainWF.HandlerRunA.seq_call_simple epsA_pc_add (Group09ChainWF.HandlerRunA.ret _)))

theorem op_slotnum_chainSpec : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_slotnum") :=
  (opHandlerChainSpec_iff _).mp (opHandlerChainSpecA_of_g09 op_slotnum_specA)

theorem op_coinbase_specA : Group09ChainWF.OpHandlerSpecA (ofString "op_coinbase") := by
  refine opHandlerSpecA_of_run 555 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_coinbase rfl ?_
  intro F s0 hInv0 _ hnd0
  dsimp only [Guest.Software.guestFn_op_coinbase, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine Group09ChainWF.HandlerRunA.seq_charge_gas_exact (Q := fun _ => True) ?_ ?_ ?_
  · intro t w hv _ _ _
    simp only [evalHOLExact] at hv
    injection hv with h1
    injection h1 with h2
    injection h2 with h3
    subst h3
    decide
  · intro t cpost amtw _ _ _ _ _ _ _ _ _ _
    trivial
  · exact Group09ChainWF.HandlerRunA.decCall_simple epsA_block_env (Group09ChainWF.HandlerRunA.decCall_simple epsA_address_to_u256_g09 (Group09ChainWF.HandlerRunA.seq_call_simple epsA_stack_push_g09 (Group09ChainWF.HandlerRunA.seq_call_simple epsA_pc_add (Group09ChainWF.HandlerRunA.ret _))))

theorem op_coinbase_chainSpec : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_coinbase") :=
  (opHandlerChainSpec_iff _).mp (opHandlerChainSpecA_of_g09 op_coinbase_specA)

theorem op_timestamp_specA : Group09ChainWF.OpHandlerSpecA (ofString "op_timestamp") := by
  refine opHandlerSpecA_of_run 556 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_timestamp rfl ?_
  intro F s0 hInv0 _ hnd0
  dsimp only [Guest.Software.guestFn_op_timestamp, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine Group09ChainWF.HandlerRunA.seq_charge_gas_exact (Q := fun _ => True) ?_ ?_ ?_
  · intro t w hv _ _ _
    simp only [evalHOLExact] at hv
    injection hv with h1
    injection h1 with h2
    injection h2 with h3
    subst h3
    decide
  · intro t cpost amtw _ _ _ _ _ _ _ _ _ _
    trivial
  · exact Group09ChainWF.HandlerRunA.decCall_simple epsA_block_env (Group09ChainWF.HandlerRunA.seq_call_simple epsA_stack_push_word_g09 (Group09ChainWF.HandlerRunA.seq_call_simple epsA_pc_add (Group09ChainWF.HandlerRunA.ret _)))

theorem op_timestamp_chainSpec : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_timestamp") :=
  (opHandlerChainSpec_iff _).mp (opHandlerChainSpecA_of_g09 op_timestamp_specA)

theorem op_number_specA : Group09ChainWF.OpHandlerSpecA (ofString "op_number") := by
  refine opHandlerSpecA_of_run 557 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_number rfl ?_
  intro F s0 hInv0 _ hnd0
  dsimp only [Guest.Software.guestFn_op_number, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine Group09ChainWF.HandlerRunA.seq_charge_gas_exact (Q := fun _ => True) ?_ ?_ ?_
  · intro t w hv _ _ _
    simp only [evalHOLExact] at hv
    injection hv with h1
    injection h1 with h2
    injection h2 with h3
    subst h3
    decide
  · intro t cpost amtw _ _ _ _ _ _ _ _ _ _
    trivial
  · exact Group09ChainWF.HandlerRunA.decCall_simple epsA_block_env (Group09ChainWF.HandlerRunA.seq_call_simple epsA_stack_push_word_g09 (Group09ChainWF.HandlerRunA.seq_call_simple epsA_pc_add (Group09ChainWF.HandlerRunA.ret _)))

theorem op_number_chainSpec : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_number") :=
  (opHandlerChainSpec_iff _).mp (opHandlerChainSpecA_of_g09 op_number_specA)

theorem op_prevrandao_specA : Group09ChainWF.OpHandlerSpecA (ofString "op_prevrandao") := by
  refine opHandlerSpecA_of_run 560 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_prevrandao rfl ?_
  intro F s0 hInv0 _ hnd0
  dsimp only [Guest.Software.guestFn_op_prevrandao, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine Group09ChainWF.HandlerRunA.seq_charge_gas_exact (Q := fun _ => True) ?_ ?_ ?_
  · intro t w hv _ _ _
    simp only [evalHOLExact] at hv
    injection hv with h1
    injection h1 with h2
    injection h2 with h3
    subst h3
    decide
  · intro t cpost amtw _ _ _ _ _ _ _ _ _ _
    trivial
  · exact Group09ChainWF.HandlerRunA.decCall_simple epsA_block_env (Group09ChainWF.HandlerRunA.decCall_simple epsA_u256_from_be (Group09ChainWF.HandlerRunA.seq_call_simple epsA_stack_push_g09 (Group09ChainWF.HandlerRunA.seq_call_simple epsA_pc_add (Group09ChainWF.HandlerRunA.ret _))))

theorem op_prevrandao_chainSpec : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_prevrandao") :=
  (opHandlerChainSpec_iff _).mp (opHandlerChainSpecA_of_g09 op_prevrandao_specA)

theorem op_dup_specA : Group09ChainWF.OpHandlerSpecA (ofString "op_dup") := by
  refine opHandlerSpecA_of_run 515 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_dup rfl ?_
  intro F s0 hInv0 _ hnd0
  dsimp only [Guest.Software.guestFn_op_dup, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine Group09ChainWF.HandlerRunA.seq_charge_gas_exact (Q := fun _ => True) ?_ ?_ ?_
  · intro t w hv _ _ _
    simp only [evalHOLExact] at hv
    injection hv with h1
    injection h1 with h2
    injection h2 with h3
    subst h3
    decide
  · intro t cpost amtw _ _ _ _ _ _ _ _ _ _
    trivial
  · exact
    Group09ChainWF.HandlerRunA.dec_simple (Group09ChainWF.HandlerRunA.seq_ite_raise_skip (fun _ _ _ _ => trivial) (Group09ChainWF.HandlerRunA.dec_simple (Group09ChainWF.HandlerRunA.seq_call_simple epsA_stack_push_g09 (Group09ChainWF.HandlerRunA.seq_call_simple epsA_pc_add (Group09ChainWF.HandlerRunA.ret _)))))

theorem op_dup_chainSpec : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_dup") :=
  (opHandlerChainSpec_iff _).mp (opHandlerChainSpecA_of_g09 op_dup_specA)


theorem op_dupn_specA : Group09ChainWF.OpHandlerSpecA (ofString "op_dupn") := by
  refine opHandlerSpecA_of_run 520 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_dupn rfl ?_
  intro F s0 hInv0 _ hnd0
  dsimp only [Guest.Software.guestFn_op_dupn, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine Group09ChainWF.HandlerRunA.seq_charge_gas_exact (Q := fun _ => True) ?_ ?_ ?_
  · intro t w hv _ _ _
    simp only [evalHOLExact] at hv
    injection hv with h1
    injection h1 with h2
    injection h2 with h3
    subst h3
    decide
  · intro t cpost amtw _ _ _ _ _ _ _ _ _ _
    trivial
  · exact
    Group09ChainWF.HandlerRunA.decCall_simple epsA_code_imm
      (Group09ChainWF.HandlerRunA.decCall_simple epsA_decode_single
        (Group09ChainWF.HandlerRunA.seq_ite_raise_skip (fun _ _ _ _ => trivial)
          (Group09ChainWF.HandlerRunA.dec_simple
            (Group09ChainWF.HandlerRunA.dec_simple
              (Group09ChainWF.HandlerRunA.seq_call_simple epsA_stack_push_g09
                (Group09ChainWF.HandlerRunA.seq_call_simple epsA_pc_add
                  (Group09ChainWF.HandlerRunA.ret _)))))))

theorem op_dupn_chainSpec : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_dupn") :=
  (opHandlerChainSpec_iff _).mp (opHandlerChainSpecA_of_g09 op_dupn_specA)

end InitECandidate.Solver.Wave8GuestInv.ContractParts.ChainHandlersR31B
