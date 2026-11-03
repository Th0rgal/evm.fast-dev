import InitECandidate.Solver.Wave8GuestInv.R11Adapters.FbClosure3

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unusedSectionVars false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.R11Adapters.Closure4

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup InitECandidate.Solver.GuestUniformClockBound
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.P12_P15.Common

theorem lookup_digits_divmod_spec' :
    originalRuntimeCode.lookup (ofString "digits_divmod") =
      some ([(ofString "u", .one), (ofString "m", .one), (ofString "d", .comb [.one, .one, .one, .one])],
            InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
              (extractFn Guest.Software.guestFn_digits_divmod).body,
            .comb [.one, .one, .one, .one]) :=
  lookup_of_guestAst_getElem 68 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_digits_divmod) rfl

theorem three_arg_lookup_digits_divmod'
    {vu vm vd : ValueHOL 64} {body' : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {ret' : ShapeHOL}
    (hl : PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup
      (ofString "digits_divmod") [vu, vm, vd] = some (body', callee, ret')) :
    callee.lookup (ofString "m") = some vm := by
  have hraw := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some _ _ _ _ _ _ hl
  simp only [lookupCodeHOLExact, lookup_digits_divmod_spec'] at hraw
  split at hraw
  · have hfn : callee.lookup = _ := (Prod.mk.inj (Prod.mk.inj (Option.some.inj hraw)).2).1.symm
    have hm := congrFun hfn (ofString "m")
    simpa [FUPDATE_LIST, FUPDATE,
      show ofString "m" ≠ ofString "d" by decide] using hm
  · cases hraw

theorem three_args_eval_eq' {F : Type} (s : PanSemStateFiniteExact 64 F)
    (e1 e2 e3 : ExpHOL 64) (vals : List (ValueHOL 64))
    (h : evalListHOLFinite s (h := fun x => Classical.propDecidable (s.memaddrs x))
      [e1, e2, e3] = some vals) :
    ∃ v1 v2 v3, evalAt s e2 = some v2 ∧ vals = [v1, v2, v3] := by
  rcases h1 : evalAt s e1 with _ | v1; · simp [evalListHOLFinite, evalListHOLExact, h1] at h
  rcases h2 : evalAt s e2 with _ | v2; · simp [evalListHOLFinite, evalListHOLExact, h1, h2] at h
  rcases h3 : evalAt s e3 with _ | v3; · simp [evalListHOLFinite, evalListHOLExact, h1, h2, h3] at h
  refine ⟨v1, v2, v3, rfl, ?_⟩
  simpa [evalListHOLFinite, evalListHOLExact, h1, h2, h3] using h.symm

theorem tail_digits_divmod_const (u m : ExpHOL 64) (c : Nat) (hc : c ≤ 16) :
    TerminatingProgBoundedOn GuestInv
      (.call none (ofString "digits_divmod") [u, .const (BitVec.ofNat 64 c), m])
      (K.«digits_divmod» + 1) := by
  apply TerminatingProgBoundedOn.tailCall_on
    (Pc := P13.DivMod.DigitsDivModGuard) P13.DivMod.fb_digits_divmod_guarded
  intro F s values _ callee _ hcode hg hargs hl
  obtain ⟨_, v2, _, hv2, rfl⟩ := three_args_eval_eq' s _ _ _ values hargs
  have hv2_eq : v2 = .val (.word (BitVec.ofNat 64 c)) := by
    simpa [evalAt, evalHOLExact] using hv2.symm
  subst hv2_eq
  rw [hcode] at hl
  have hcm := three_arg_lookup_digits_divmod' hl
  refine ⟨guestInv_callEntry s callee hg, ?_⟩
  simp only [locN, callEntryStateHOLFinite, hcm, BitVec.toNat_ofNat]
  omega

theorem «fb_u256_addmod» :
    TerminatingFunBoundedOn GuestInv (ofString "u256_addmod") K.«u256_addmod» := by
  have h0 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_u256_add_carry»
  have h1 := P13.DivMod.fb_u256_mod
  have h2 := P13.Callees.fb_u256_to_digits
  fb_unfold 75 Guest.Software.guestFn_u256_addmod
  apply TerminatingProgBoundedOn.weaken'
  · apply TerminatingProgBoundedOn.seq_guestInv
    · exact TerminatingProgBoundedOn.ite_on (straightOn _ rfl) (straightOn _ rfl)
    · apply decCall_guestInv' h0
      apply dec_guestInv
      apply TerminatingProgBoundedOn.seq_guestInv
      · exact TerminatingProgBoundedOn.ite_on
          (TerminatingProgBoundedOn.tailCall_guestInv h1 _) (straightOn _ rfl)
      · apply dec_guestInv
        apply TerminatingProgBoundedOn.seq_guestInv
        · exact call_guestInv' h2
        · apply TerminatingProgBoundedOn.seq_guestInv
          · exact straightOn _ rfl
          · apply TerminatingProgBoundedOn.seq_guestInv
            · exact straightOn _ rfl
            · exact tail_digits_divmod_const _ _ 10 (by decide)
  · have hD : domainBytes + 1 + 1 ≤ 2 ^ 64 + 1 := by rw [domainBytes_eq]; decide
    unfold K.«u256_addmod»
    generalize_K
    try simp only [nat_max_eq]
    omega

theorem «fb_u256_mulmod» :
    TerminatingFunBoundedOn GuestInv (ofString "u256_mulmod") K.«u256_mulmod» := by
  have h0 := P13.Callees.fb_mul64x64
  have h1 := P13.DivMod.fb_u256_mod
  have h2 := P13.Callees.fb_u256_to_digits
  have h3 := InitECandidate.Solver.Wave8GuestInv.R11Adapters.«fb_u256_mul_full»
  fb_unfold 76 Guest.Software.guestFn_u256_mulmod
  apply TerminatingProgBoundedOn.weaken'
  · apply TerminatingProgBoundedOn.seq_guestInv
    · exact TerminatingProgBoundedOn.ite_on (straightOn _ rfl) (straightOn _ rfl)
    · apply dec_guestInv
      apply TerminatingProgBoundedOn.seq_guestInv
      · apply TerminatingProgBoundedOn.ite_on
        · apply decCall_guestInv' h0
          apply TerminatingProgBoundedOn.seq_guestInv
          · exact TerminatingProgBoundedOn.ite_on
              (TerminatingProgBoundedOn.tailCall_guestInv h1 _) (straightOn _ rfl)
          · apply TerminatingProgBoundedOn.seq_guestInv
            · exact call_guestInv' h2
            · exact tail_digits_divmod_const _ _ 4 (by decide)
        · exact straightOn _ rfl
      · apply decCall_guestInv' h3
        apply TerminatingProgBoundedOn.seq_guestInv
        · exact call_guestInv' h2
        · apply TerminatingProgBoundedOn.seq_guestInv
          · exact call_guestInv' h2
          · exact tail_digits_divmod_const _ _ 16 (by decide)
  · have hD : domainBytes + 1 + 1 ≤ 2 ^ 64 + 1 := by rw [domainBytes_eq]; decide
    unfold K.«u256_mulmod»
    generalize_K
    simp only [Nat.max_def]
    split_ifs <;> omega

theorem «fb_op_addmod» :
    TerminatingFunBoundedOn GuestInv (ofString "op_addmod") K.«op_addmod» := by
  have h0 := P13.Callees.fb_stack_pop
  have h1 := P13.Callees.fb_charge_gas
  have h2 := «fb_u256_addmod»
  have h3 := P13.Callees.fb_stack_push
  have h4 := P13.Callees.fb_pc_add
  fb_prove2 482 Guest.Software.guestFn_op_addmod K.«op_addmod»

theorem «fb_op_mulmod» :
    TerminatingFunBoundedOn GuestInv (ofString "op_mulmod") K.«op_mulmod» := by
  have h0 := P13.Callees.fb_stack_pop
  have h1 := P13.Callees.fb_charge_gas
  have h2 := «fb_u256_mulmod»
  have h3 := P13.Callees.fb_stack_push
  have h4 := P13.Callees.fb_pc_add
  fb_prove2 483 Guest.Software.guestFn_op_mulmod K.«op_mulmod»

end InitECandidate.Solver.Wave8GuestInv.R11Adapters.Closure4
