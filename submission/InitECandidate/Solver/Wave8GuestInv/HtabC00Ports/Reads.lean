import InitECandidate.Solver.Wave8GuestInv.HtabC00Ports.LightBatch

/-! The core of `htab_del_spec`: from `HtabWF` before a deleting run of `htab_del` and the exact
final memory (`DelPostR` over the memory `M'` after the order-slot move), the table exit. -/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

namespace InitECandidate.Solver.Wave8M19.Htab

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.Wave8M19

theorem updW_ofNat_ne (M : BitVec 64 → HolWordLab 64) (x : Nat) (w a : BitVec 64)
    (h : a.toNat ≠ x % 2 ^ 64) : updW M (BitVec.ofNat 64 x) w a = M a := by
  unfold updW
  rw [if_neg]
  intro e; apply h; rw [e]; simp

theorem bv0_toNat : (0 : BitVec 64).toNat = 0 := rfl

theorem rdN_ite (c : Prop) [Decidable c] (A B : BitVec 64 → HolWordLab 64) (a : Nat) :
    rdN (if c then A else B) a = if c then rdN A a else rdN B a := by split <;> rfl

theorem fn_ite_apply (c : Prop) [Decidable c] (A B : BitVec 64 → HolWordLab 64) (a : BitVec 64) :
    (if c then A else B) a = if c then A a else B a := by split <;> rfl

theorem wv_ite (c : Prop) [Decidable c] (a b : HolWordLab 64) :
    wv (if c then a else b) = if c then wv a else wv b := by split <;> rfl

theorem toNat_ite (c : Prop) [Decidable c] (a b : BitVec 64) :
    (if c then a else b).toNat = if c then a.toNat else b.toNat := by split <;> rfl

/-- Two offsets within 32-byte nodes coincide exactly when both node and field agree. -/
theorem node_addr_eq_iff (base n p k off : Nat) (hk : k < 32) (hoff : off < 32) :
    base + 32 * n + k = base + 32 * p + off ↔ n = p ∧ k = off := by omega

/-- Reads through word stores at numeric addresses, deciding address (in)equalities by `omega`. -/
syntax "rdsimp" "[" Lean.Parser.Tactic.simpLemma,* "]" (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| rdsimp [$ts,*] $[$loc]?) => `(tactic| simp (disch := omega) only [an0, an8, an16, ah24,
      ah56, ah72, ao8, rdN_upd, wv_toNat_ofNat, updW_ofNat_ne, ← BitVec.toNat_inj, bv0_toNat,
      rdN_ite, fn_ite_apply, wv_ite, toNat_ite, Nat.mod_eq_of_lt, node_addr_eq_iff, if_pos, if_neg, if_true, if_false, ite_self, $ts,*] $[$loc]?)


/-- Revision 9 additionally preserves the key length and stride. -/
def ExitR9 {F : Type} (t : Nat) (s post : PanSemStateFiniteExact 64 F) : Prop :=
  ExitR t s post ∧ hdr post t 0 = hdr s t 0 ∧ hdr post t 1 = hdr s t 1

end InitECandidate.Solver.Wave8M19.Htab
