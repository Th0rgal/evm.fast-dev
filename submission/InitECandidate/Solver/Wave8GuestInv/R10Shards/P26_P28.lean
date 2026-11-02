import InitECandidate.Solver.Wave8GuestInv.Primitives
import InitECandidate.Solver.GuestTrapOutcomes

/-! Shards P26 + P27 + P28: all 21 R11 `Primitives` fields (table/crypto/evm/mpt/ssz init functions
and host input / HTR payload request). -/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

/-! ## Section 1: P26 `fb_*` Bounds and `ro_secp256k1_init` -/

private theorem TerminatingProgBounded.call {fname : MlS} {B : Nat}
    (hfun : TerminatingFunBounded fname B)
    (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64)) :
    TerminatingProgBounded (.call (some (destination, none)) fname arguments) (B + 1) := by
  obtain ⟨params, body, ret, hlook, hbody⟩ := hfun
  intro F state hcode hnt
  rcases hargs : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments with
    _ | values
  · have hout : evaluateHOLFiniteState state (.call (some (destination, none)) fname arguments) =
        (some .error, state) := by rw [evaluateHOLFiniteState_call, hargs]
    rw [hout]; exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
  · rcases hl : lookupCodeHOLFinite state.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · have hout : evaluateHOLFiniteState state (.call (some (destination, none)) fname arguments) =
          (some .error, state) := by rw [evaluateHOLFiniteState_call, hargs]; simp only [hl]
      rw [hout]; exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
    · have hsame := lookupCodeHOLFinite_installed_body state.code.lookup fname params body body'
        ret ret' values callee (by rw [hcode]; exact hlook) hl
      subst hsame
      by_cases hz : state.clock = 0
      · exfalso; apply hnt; rw [evaluateHOLFiniteState_call, hargs]; simp [hl, hz]
      · rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body' with
          ⟨res, post⟩
        have hntb : res ≠ some .timeOut := by
          intro h; subst h; apply hnt; rw [evaluateHOLFiniteState_call, hargs]; simp [hl, hz, hrun]
        have hb := hbody (callEntryStateHOLFinite state callee) hcode (by rw [hrun]; exact hntb)
        rw [hrun] at hb
        obtain ⟨hspent, hkept⟩ := hb
        change state.clock - 1 ≤ post.clock + B at hspent
        change post.clock ≤ state.clock - 1 at hkept
        have hpair := evaluate_call_body_clock_no_timeout
          state post fname destination arguments values body' callee ret' res hargs hl hz hrun hntb
        dsimp only at hpair
        rw [hpair.2]
        exact ⟨by omega, by omega⟩

private theorem ub_trap_with : TerminatingFunBounded (ofString "trap_with") K.«trap_with» := by
  refine ⟨_, _, _, originalRuntimeCode_lookup_of_guestAst_getElem 3
    (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_trap_with) rfl, ?_⟩
  exact TerminatingProgBounded.straight _ rfl

private theorem ub_alloc : TerminatingFunBounded (ofString "alloc") K.«alloc» := by
  refine ⟨_, _, _, originalRuntimeCode_lookup_of_guestAst_getElem 7
    (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_alloc) rfl, ?_⟩
  exact TerminatingProgBounded.dec _ _ _
    (TerminatingProgBounded.seq
      (TerminatingProgBounded.ite
        (TerminatingProgBounded.call ub_trap_with _ _)
        (TerminatingProgBounded.straight _ rfl))
      (TerminatingProgBounded.dec _ _ _
        (TerminatingProgBounded.seq
          (TerminatingProgBounded.ite
            (TerminatingProgBounded.call ub_trap_with _ _)
            (TerminatingProgBounded.straight _ rfl))
          (TerminatingProgBounded.straight _ rfl))))

private theorem ub_bls_consts_init :
    TerminatingFunBounded (ofString "bls_consts_init") K.«bls_consts_init» := by
  refine ⟨_, _, _, originalRuntimeCode_lookup_of_guestAst_getElem 696
    (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_bls_consts_init) rfl, ?_⟩
  exact TerminatingProgBounded.seq
    (TerminatingProgBounded.straight _ rfl)
    (TerminatingProgBounded.seq
      (TerminatingProgBounded.call ub_alloc _ _)
      (TerminatingProgBounded.straight _ rfl))

private theorem ub_bls_lib_init :
    TerminatingFunBounded (ofString "bls_lib_init") K.«bls_lib_init» := by
  refine ⟨_, _, _, originalRuntimeCode_lookup_of_guestAst_getElem 801
    (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_bls_lib_init) rfl, ?_⟩
  exact TerminatingProgBounded.seq
    (TerminatingProgBounded.call ub_bls_consts_init _ _)
    (TerminatingProgBounded.straight _ rfl)

private theorem ub_bls_precompiles_init :
    TerminatingFunBounded (ofString "bls_precompiles_init") K.«bls_precompiles_init» := by
  refine ⟨_, _, _, originalRuntimeCode_lookup_of_guestAst_getElem 811
    (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_bls_precompiles_init) rfl, ?_⟩
  exact TerminatingProgBounded.seq
    (TerminatingProgBounded.straight _ rfl)
    (TerminatingProgBounded.seq
      (TerminatingProgBounded.call ub_bls_lib_init _ _)
      (TerminatingProgBounded.seq
        (TerminatingProgBounded.call ub_alloc _ _)
        (TerminatingProgBounded.straight _ rfl)))

theorem fb_bls_precompiles_init :
    TerminatingFunBoundedOn GuestInv (ofString "bls_precompiles_init") K.«bls_precompiles_init» :=
  TerminatingFunBoundedOn.of_unconditional ub_bls_precompiles_init

private theorem ub_bn254_init :
    TerminatingFunBounded (ofString "bn254_init") K.«bn254_init» := by
  refine ⟨_, _, _, originalRuntimeCode_lookup_of_guestAst_getElem 648
    (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_bn254_init) rfl, ?_⟩
  exact TerminatingProgBounded.seq (TerminatingProgBounded.straight _ rfl)
    (TerminatingProgBounded.seq (TerminatingProgBounded.call ub_alloc _ _)
    (TerminatingProgBounded.seq (TerminatingProgBounded.straight _ rfl)
    (TerminatingProgBounded.seq (TerminatingProgBounded.straight _ rfl)
    (TerminatingProgBounded.seq (TerminatingProgBounded.straight _ rfl)
    (TerminatingProgBounded.seq (TerminatingProgBounded.straight _ rfl)
    (TerminatingProgBounded.seq (TerminatingProgBounded.straight _ rfl)
    (TerminatingProgBounded.seq (TerminatingProgBounded.straight _ rfl)
    (TerminatingProgBounded.seq (TerminatingProgBounded.straight _ rfl)
    (TerminatingProgBounded.seq (TerminatingProgBounded.straight _ rfl)
    (TerminatingProgBounded.seq (TerminatingProgBounded.straight _ rfl)
    (TerminatingProgBounded.seq (TerminatingProgBounded.straight _ rfl)
    (TerminatingProgBounded.seq (TerminatingProgBounded.straight _ rfl)
    (TerminatingProgBounded.seq (TerminatingProgBounded.straight _ rfl)
    (TerminatingProgBounded.seq (TerminatingProgBounded.call ub_alloc _ _)
      (TerminatingProgBounded.straight _ rfl)))))))))))))))

theorem fb_bn254_init :
    TerminatingFunBoundedOn GuestInv (ofString "bn254_init") K.«bn254_init» :=
  TerminatingFunBoundedOn.of_unconditional ub_bn254_init

private theorem ub_keccak_init :
    TerminatingFunBounded (ofString "keccak_init") K.«keccak_init» := by
  refine ⟨_, _, _, originalRuntimeCode_lookup_of_guestAst_getElem 100
    (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_keccak_init) rfl, ?_⟩
  exact TerminatingProgBounded.seq (TerminatingProgBounded.call ub_alloc _ _)
    (TerminatingProgBounded.seq (TerminatingProgBounded.call ub_alloc _ _)
      (TerminatingProgBounded.seq (TerminatingProgBounded.call ub_alloc _ _)
        (TerminatingProgBounded.straight _ rfl)))

theorem fb_keccak_init :
    TerminatingFunBoundedOn GuestInv (ofString "keccak_init") K.«keccak_init» :=
  TerminatingFunBoundedOn.of_unconditional ub_keccak_init

private theorem ub_ripemd160_init :
    TerminatingFunBounded (ofString "ripemd160_init") K.«ripemd160_init» := by
  refine ⟨_, _, _, originalRuntimeCode_lookup_of_guestAst_getElem 612
    (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_ripemd160_init) rfl, ?_⟩
  exact TerminatingProgBounded.seq (TerminatingProgBounded.straight _ rfl)
    (TerminatingProgBounded.seq (TerminatingProgBounded.call ub_alloc _ _)
    (TerminatingProgBounded.seq (TerminatingProgBounded.call ub_alloc _ _)
    (TerminatingProgBounded.seq (TerminatingProgBounded.call ub_alloc _ _)
    (TerminatingProgBounded.seq (TerminatingProgBounded.call ub_alloc _ _)
      (TerminatingProgBounded.straight _ rfl)))))

theorem fb_ripemd160_init :
    TerminatingFunBoundedOn GuestInv (ofString "ripemd160_init") K.«ripemd160_init» :=
  TerminatingFunBoundedOn.of_unconditional ub_ripemd160_init

private theorem ub_secp256k1_init :
    TerminatingFunBounded (ofString "secp256k1_init") K.«secp256k1_init» := by
  refine ⟨_, _, _, originalRuntimeCode_lookup_of_guestAst_getElem 148
    (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_secp256k1_init) rfl, ?_⟩
  exact TerminatingProgBounded.straight _ rfl

theorem fb_secp256k1_init :
    TerminatingFunBoundedOn GuestInv (ofString "secp256k1_init") K.«secp256k1_init» :=
  TerminatingFunBoundedOn.of_unconditional ub_secp256k1_init

private theorem ub_sha256_init :
    TerminatingFunBounded (ofString "sha256_init") K.«sha256_init» := by
  refine ⟨_, _, _, originalRuntimeCode_lookup_of_guestAst_getElem 91
    (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_sha256_init) rfl, ?_⟩
  exact TerminatingProgBounded.seq (TerminatingProgBounded.call ub_alloc _ _)
    (TerminatingProgBounded.seq (TerminatingProgBounded.call ub_alloc _ _)
      (TerminatingProgBounded.straight _ rfl))

theorem fb_sha256_init :
    TerminatingFunBoundedOn GuestInv (ofString "sha256_init") K.«sha256_init» :=
  TerminatingFunBoundedOn.of_unconditional ub_sha256_init

private theorem ub_u256_ws_init :
    TerminatingFunBounded (ofString "u256_ws_init") K.«u256_ws_init» := by
  refine ⟨_, _, _, originalRuntimeCode_lookup_of_guestAst_getElem 38
    (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_u256_ws_init) rfl, ?_⟩
  exact TerminatingProgBounded.seq
    (TerminatingProgBounded.ite
      (TerminatingProgBounded.call ub_alloc _ _)
      (TerminatingProgBounded.straight _ rfl))
    (TerminatingProgBounded.straight _ rfl)

theorem fb_u256_ws_init :
    TerminatingFunBoundedOn GuestInv (ofString "u256_ws_init") K.«u256_ws_init» :=
  TerminatingFunBoundedOn.of_unconditional ub_u256_ws_init

theorem ro_secp256k1_init : ReadOnlyFn (ofString "secp256k1_init") := by
  refine ⟨[], sourceFnBody Guest.Software.guestFn_secp256k1_init, .one,
    lookup_of_guestAst_getElem 148 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_secp256k1_init) rfl, ?_⟩
  intro F s _ _ _ _ _
  have hbody : sourceFnBody Guest.Software.guestFn_secp256k1_init = .return (.const 0) := rfl
  rw [hbody, evaluateHOLFiniteState_return]
  dsimp only [evalHOLExact, isValidValueHOLExact, shapeEqHOL, shapeOfHOLExact]
  split
  · rfl
  · cases s; rfl


end InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28
