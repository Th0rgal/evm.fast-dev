import InitECandidate.Solver.Wave8GuestInv.Deliveries.M14.Base

/-! `ro_fee_mul`: `fee_mul` (AST line 32778) is read-only.
Walks `mul64x64` (AST 1127) -> `u256_mul_full` (AST 1230) -> `fee_mul` (AST 32778). -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace InitECandidate.Solver.Wave8Contracts.M14

open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup

def isPureLocalBody (roCallee : MlS → Bool) : ProgHOL 64 → Bool
  | .skip => true
  | .return _ => true
  | .raise _ _ => true
  | .assign .local _ _ => true
  | .primitive _ _ _ => true
  | .dec _ _ _ b => isPureLocalBody roCallee b
  | .seq a b => isPureLocalBody roCallee a && isPureLocalBody roCallee b
  | .ite _ a b => isPureLocalBody roCallee a && isPureLocalBody roCallee b
  | .while _ b => isPureLocalBody roCallee b
  | .decCall _ _ fn _ b => roCallee fn && isPureLocalBody roCallee b
  | _ => false

theorem ReadOnlyProg.of_pureLocalBody {roCallee : MlS → Bool}
    (hcallee : ∀ fn, roCallee fn = true → ReadOnlyFn fn) :
    ∀ {p : ProgHOL 64}, isPureLocalBody roCallee p = true → ReadOnlyProg p
  | .skip, _ => ReadOnlyProg.skip
  | .return e, _ => ReadOnlyProg.ret e
  | .raise eid e, _ => ReadOnlyProg.raise eid e
  | .assign .local nm e, _ => ReadOnlyProg.assign_local nm e
  | .assign .global _ _, h => by simp [isPureLocalBody] at h
  | .primitive nm op args, _ => ReadOnlyProg.primitive nm op args
  | .dec nm sh init b, h => by
    simp only [isPureLocalBody] at h
    exact ReadOnlyProg.dec nm sh init (ReadOnlyProg.of_pureLocalBody hcallee h)
  | .seq a b, h => by
    simp only [isPureLocalBody, Bool.and_eq_true] at h
    exact ReadOnlyProg.seq
      (ReadOnlyProg.of_pureLocalBody hcallee h.1)
      (ReadOnlyProg.of_pureLocalBody hcallee h.2)
  | .ite c a b, h => by
    simp only [isPureLocalBody, Bool.and_eq_true] at h
    exact ReadOnlyProg.ite c
      (ReadOnlyProg.of_pureLocalBody hcallee h.1)
      (ReadOnlyProg.of_pureLocalBody hcallee h.2)
  | .while c b, h => by
    simp only [isPureLocalBody] at h
    exact ReadOnlyProg.while_loop c (ReadOnlyProg.of_pureLocalBody hcallee h)
  | .decCall nm sh fn args b, h => by
    simp only [isPureLocalBody, Bool.and_eq_true] at h
    exact ReadOnlyProg.decCall (hcallee fn h.1) nm sh args
      (ReadOnlyProg.of_pureLocalBody hcallee h.2)
  | .store _ _, h => by simp [isPureLocalBody] at h
  | .storeByte _ _, h => by simp [isPureLocalBody] at h
  | .store32 _ _, h => by simp [isPureLocalBody] at h
  | .break, h => by simp [isPureLocalBody] at h
  | .continue, h => by simp [isPureLocalBody] at h
  | .call _ _ _, h => by simp [isPureLocalBody] at h
  | .extCall _ _ _ _ _, h => by simp [isPureLocalBody] at h
  | .shMemLoad _ _ _ _, h => by simp [isPureLocalBody] at h
  | .shMemStore _ _ _, h => by simp [isPureLocalBody] at h
  | .annot _ _, h => by simp [isPureLocalBody] at h
  | .tick, h => by simp [isPureLocalBody] at h

private theorem ro_mul64x64_aux : ReadOnlyFn (ofString "mul64x64") := by
  refine readOnlyFn_of_guestAst 59 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_mul64x64 rfl ?_
  exact ReadOnlyProg.of_pureLocalBody (roCallee := fun _ => false)
    (fun _ h => by cases h) (by decide)

private theorem ro_u256_mul_full_aux : ReadOnlyFn (ofString "u256_mul_full") := by
  refine readOnlyFn_of_guestAst 61 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_mul_full rfl ?_
  refine ReadOnlyProg.of_pureLocalBody
    (roCallee := fun fn => fn == ofString "mul64x64") ?_ (by decide)
  intro fn hfn
  have heq : fn = ofString "mul64x64" := by simpa using hfn
  subst heq
  exact ro_mul64x64_aux

theorem «ro_fee_mul» : ReadOnlyFn (ofString "fee_mul") := by
  refine readOnlyFn_of_guestAst 867 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_fee_mul rfl ?_
  refine ReadOnlyProg.of_pureLocalBody
    (roCallee := fun fn => fn == ofString "u256_mul_full") ?_ (by decide)
  intro fn hfn
  have heq : fn = ofString "u256_mul_full" := by simpa using hfn
  subst heq
  exact ro_u256_mul_full_aux

end InitECandidate.Solver.Wave8Contracts.M14
