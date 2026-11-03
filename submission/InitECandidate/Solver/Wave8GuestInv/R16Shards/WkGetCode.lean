import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkAcctWsBase

/-! Standalone verified proofs for C08 `WorldKeeps` leaves:
- `«wk_record_pre_state_read»`
- `«wk_mark_account_created»`
- `«wk_get_code»`
-/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16WkAcctWs

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.GuestGlobalKeep
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28

/-! ## 1. Role-slot disjointness helpers for `bs+72` and `ts+{8,24,40,56}` -/

theorem nonValueSlot_of_wrs {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat)
    (t0 : Nat) (roleName : String)
    (hT : TablesTyped s S)
    (ht0_nz : t0 ≠ 0)
    (ht0_S : t0 ∈ S)
    (ht0_wrs : (t0, roleName) ∈ worldRoleSlots s)
    (hne_bs32 : "bs+32" ≠ roleName)
    (hne_ts32 : "ts+32" ≠ roleName)
    (hne_ba : "bal_accounts" ≠ roleName)
    (hne_bstor : "bal.stor" ≠ roleName)
    (hne_ws32 : "ws+32" ≠ roleName) :
    t0 ∈ S ∧
    (globN s "bs" ≠ 0 → memW s (globN s "bs" + 32) ≠ t0) ∧
    (globN s "ts" ≠ 0 → memW s (globN s "ts" + 32) ≠ t0) ∧
    globN s "bal_accounts" ≠ t0 ∧
    (∀ ad ∈ balRecords s, memW s ad ≠ t0) ∧
    (globN s "ws" ≠ 0 → memW s (globN s "ws" + 32) ≠ t0) := by
  have hroles := hT.2.2.2.2.2.2.2.2.2.2.2
  refine ⟨ht0_S, ?_, ?_, ?_, ?_, ?_⟩
  · intro hbs h32
    have h32_nz : memW s (globN s "bs" + 32) ≠ 0 := by rw [h32]; exact ht0_nz
    have hm : (memW s (globN s "bs" + 32), "bs+32") ∈ worldRoleSlots s := by
      apply mem_worldRoleSlots_recRole s "bs" 32 "bs+32" hbs h32_nz
      apply List.mem_append.2; left; apply List.mem_append.2; right
      unfold recRoles; simp [hbs]
    exact slot_ne_of_diff_nonshared_role hroles hm ht0_wrs hne_bs32 h32
  · intro hts h32
    have h32_nz : memW s (globN s "ts" + 32) ≠ 0 := by rw [h32]; exact ht0_nz
    have hm : (memW s (globN s "ts" + 32), "ts+32") ∈ worldRoleSlots s := by
      apply mem_worldRoleSlots_recRole s "ts" 32 "ts+32" hts h32_nz
      apply List.mem_append.2; right
      unfold recRoles; simp [hts]
    exact slot_ne_of_diff_nonshared_role hroles hm ht0_wrs hne_ts32 h32
  · intro hba
    have hba_nz : globN s "bal_accounts" ≠ 0 := by rw [hba]; exact ht0_nz
    have hm : (globN s "bal_accounts", "bal_accounts") ∈ worldRoleSlots s := by
      unfold worldRoleSlots
      refine List.mem_filter.2 ⟨?_, by simp [hba_nz]⟩
      apply List.mem_append.2; left; apply List.mem_append.2; left
      apply List.mem_append.2; left; apply List.mem_append.2; right; simp
    exact slot_ne_of_diff_nonshared_role hroles hm ht0_wrs hne_ba hba
  · intro ad had had0
    have had0_nz : memW s ad ≠ 0 := by rw [had0]; exact ht0_nz
    have hm : (memW s ad, "bal.stor") ∈ worldRoleSlots s := by
      unfold worldRoleSlots
      refine List.mem_filter.2 ⟨?_, by simp [had0_nz]⟩
      apply List.mem_append.2; right
      exact List.mem_flatMap.2 ⟨ad, had, by simp⟩
    exact slot_ne_of_diff_nonshared_role hroles hm ht0_wrs hne_bstor had0
  · intro hws h32
    have h32_nz : memW s (globN s "ws" + 32) ≠ 0 := by rw [h32]; exact ht0_nz
    have hm : (memW s (globN s "ws" + 32), "ws+32") ∈ worldRoleSlots s := by
      apply mem_worldRoleSlots_recRole s "ws" 32 "ws+32" hws h32_nz
      apply List.mem_append.2; left; apply List.mem_append.2; left
      unfold recRoles; simp [hws]
    exact slot_ne_of_diff_nonshared_role hroles hm ht0_wrs hne_ws32 h32

theorem nonValueSlot_bs72 {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat)
    (hT : TablesTyped s S) (hbs_nz : globN s "bs" ≠ 0)
    (ht0_nz : memW s (globN s "bs" + (72 : BitVec 64).toNat) ≠ 0) :
    let t0 := memW s (globN s "bs" + (72 : BitVec 64).toNat)
    t0 ∈ S ∧
    (globN s "bs" ≠ 0 → memW s (globN s "bs" + 32) ≠ t0) ∧
    (globN s "ts" ≠ 0 → memW s (globN s "ts" + 32) ≠ t0) ∧
    globN s "bal_accounts" ≠ t0 ∧
    (∀ ad ∈ balRecords s, memW s ad ≠ t0) ∧
    (globN s "ws" ≠ 0 → memW s (globN s "ws" + 32) ≠ t0) := by
  have hc : (72 : BitVec 64).toNat = 72 := by decide
  rw [hc] at ht0_nz ⊢
  have ht0_S : memW s (globN s "bs" + 72) ∈ S := by
    rcases hT.2.2.2.2.1 72 (by simp [bsTableSlots]) hbs_nz with h0 | hm
    · exact absurd h0 ht0_nz
    · exact hm
  have ht0_wrs : (memW s (globN s "bs" + 72), "bs+72") ∈ worldRoleSlots s := by
    apply mem_worldRoleSlots_recRole s "bs" 72 "bs+72" hbs_nz ht0_nz
    apply List.mem_append.2; left; apply List.mem_append.2; right
    unfold recRoles; simp [hbs_nz]
  exact nonValueSlot_of_wrs s S _ "bs+72" hT ht0_nz ht0_S ht0_wrs
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem nonValueSlot_ts8 {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat)
    (hT : TablesTyped s S) (hts_nz : globN s "ts" ≠ 0)
    (ht0_nz : memW s (globN s "ts" + (8 : BitVec 64).toNat) ≠ 0) :
    let t0 := memW s (globN s "ts" + (8 : BitVec 64).toNat)
    t0 ∈ S ∧
    (globN s "bs" ≠ 0 → memW s (globN s "bs" + 32) ≠ t0) ∧
    (globN s "ts" ≠ 0 → memW s (globN s "ts" + 32) ≠ t0) ∧
    globN s "bal_accounts" ≠ t0 ∧
    (∀ ad ∈ balRecords s, memW s ad ≠ t0) ∧
    (globN s "ws" ≠ 0 → memW s (globN s "ws" + 32) ≠ t0) := by
  have hc : (8 : BitVec 64).toNat = 8 := by decide
  rw [hc] at ht0_nz ⊢
  have ht0_S : memW s (globN s "ts" + 8) ∈ S := by
    rcases hT.2.2.2.2.2.1 8 (by simp [tsTableSlots]) hts_nz with h0 | hm
    · exact absurd h0 ht0_nz
    · exact hm
  have ht0_wrs : (memW s (globN s "ts" + 8), "ts+8") ∈ worldRoleSlots s := by
    apply mem_worldRoleSlots_recRole s "ts" 8 "ts+8" hts_nz ht0_nz
    apply List.mem_append.2; right
    unfold recRoles; simp [hts_nz]
  exact nonValueSlot_of_wrs s S _ "ts+8" hT ht0_nz ht0_S ht0_wrs
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem nonValueSlot_ts24 {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat)
    (hT : TablesTyped s S) (hts_nz : globN s "ts" ≠ 0)
    (ht0_nz : memW s (globN s "ts" + (24 : BitVec 64).toNat) ≠ 0) :
    let t0 := memW s (globN s "ts" + (24 : BitVec 64).toNat)
    t0 ∈ S ∧
    (globN s "bs" ≠ 0 → memW s (globN s "bs" + 32) ≠ t0) ∧
    (globN s "ts" ≠ 0 → memW s (globN s "ts" + 32) ≠ t0) ∧
    globN s "bal_accounts" ≠ t0 ∧
    (∀ ad ∈ balRecords s, memW s ad ≠ t0) ∧
    (globN s "ws" ≠ 0 → memW s (globN s "ws" + 32) ≠ t0) := by
  have hc : (24 : BitVec 64).toNat = 24 := by decide
  rw [hc] at ht0_nz ⊢
  have ht0_S : memW s (globN s "ts" + 24) ∈ S := by
    rcases hT.2.2.2.2.2.1 24 (by simp [tsTableSlots]) hts_nz with h0 | hm
    · exact absurd h0 ht0_nz
    · exact hm
  have ht0_wrs : (memW s (globN s "ts" + 24), "ts+24") ∈ worldRoleSlots s := by
    apply mem_worldRoleSlots_recRole s "ts" 24 "ts+24" hts_nz ht0_nz
    apply List.mem_append.2; right
    unfold recRoles; simp [hts_nz]
  exact nonValueSlot_of_wrs s S _ "ts+24" hT ht0_nz ht0_S ht0_wrs
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem nonValueSlot_ts40 {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat)
    (hT : TablesTyped s S) (hts_nz : globN s "ts" ≠ 0)
    (ht0_nz : memW s (globN s "ts" + (40 : BitVec 64).toNat) ≠ 0) :
    let t0 := memW s (globN s "ts" + (40 : BitVec 64).toNat)
    t0 ∈ S ∧
    (globN s "bs" ≠ 0 → memW s (globN s "bs" + 32) ≠ t0) ∧
    (globN s "ts" ≠ 0 → memW s (globN s "ts" + 32) ≠ t0) ∧
    globN s "bal_accounts" ≠ t0 ∧
    (∀ ad ∈ balRecords s, memW s ad ≠ t0) ∧
    (globN s "ws" ≠ 0 → memW s (globN s "ws" + 32) ≠ t0) := by
  have hc : (40 : BitVec 64).toNat = 40 := by decide
  rw [hc] at ht0_nz ⊢
  have ht0_S : memW s (globN s "ts" + 40) ∈ S := by
    rcases hT.2.2.2.2.2.1 40 (by simp [tsTableSlots]) hts_nz with h0 | hm
    · exact absurd h0 ht0_nz
    · exact hm
  have ht0_wrs : (memW s (globN s "ts" + 40), "ts+40") ∈ worldRoleSlots s := by
    apply mem_worldRoleSlots_recRole s "ts" 40 "ts+40" hts_nz ht0_nz
    apply List.mem_append.2; right
    unfold recRoles; simp [hts_nz]
  exact nonValueSlot_of_wrs s S _ "ts+40" hT ht0_nz ht0_S ht0_wrs
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem nonValueSlot_ts56 {F : Type} (s : PanSemStateFiniteExact 64 F) (S : List Nat)
    (hT : TablesTyped s S) (hts_nz : globN s "ts" ≠ 0)
    (ht0_nz : memW s (globN s "ts" + (56 : BitVec 64).toNat) ≠ 0) :
    let t0 := memW s (globN s "ts" + (56 : BitVec 64).toNat)
    t0 ∈ S ∧
    (globN s "bs" ≠ 0 → memW s (globN s "bs" + 32) ≠ t0) ∧
    (globN s "ts" ≠ 0 → memW s (globN s "ts" + 32) ≠ t0) ∧
    globN s "bal_accounts" ≠ t0 ∧
    (∀ ad ∈ balRecords s, memW s ad ≠ t0) ∧
    (globN s "ws" ≠ 0 → memW s (globN s "ws" + 32) ≠ t0) := by
  have hc : (56 : BitVec 64).toNat = 56 := by decide
  rw [hc] at ht0_nz ⊢
  have ht0_S : memW s (globN s "ts" + 56) ∈ S := by
    rcases hT.2.2.2.2.2.1 56 (by simp [tsTableSlots]) hts_nz with h0 | hm
    · exact absurd h0 ht0_nz
    · exact hm
  have ht0_wrs : (memW s (globN s "ts" + 56), "ts+56") ∈ worldRoleSlots s := by
    apply mem_worldRoleSlots_recRole s "ts" 56 "ts+56" hts_nz ht0_nz
    apply List.mem_append.2; right
    unfold recRoles; simp [hts_nz]
  exact nonValueSlot_of_wrs s S _ "ts+56" hT ht0_nz ht0_S ht0_wrs
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-! ## 2. Read-only sub-contracts for `ws_get_code` (`nodedb_lookup` -> `ws_get_code`) -/

def wsGetCodeCallees (f : MlS) : Bool :=
  f == ofString "memeq" || f == ofString "nodedb_lookup" ||
  f == ofString "htab_get" || f == ofString "htab_find_leaf"

def LocFrameR16 {F : Type} (s t : PanSemStateFiniteExact 64 F) : Prop :=
  t = { s with locals := t.locals, clock := t.clock }

theorem LocFrameR16.refl {F : Type} (s : PanSemStateFiniteExact 64 F) : LocFrameR16 s s := by
  cases s; rfl

theorem LocFrameR16.trans {F : Type} {s t u : PanSemStateFiniteExact 64 F}
    (h1 : LocFrameR16 s t) (h2 : LocFrameR16 t u) : LocFrameR16 s u := by
  unfold LocFrameR16 at *; rw [h2]; rw [h1]

theorem LocFrameR16.with_locals_clock {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (h : LocFrameR16 s t) (L : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    LocFrameR16 s { t with locals := L, clock := k } := by
  unfold LocFrameR16 at h ⊢; rw [h]

def roProgR16 (good : MlS → Bool) : ProgHOL 64 → Bool
  | .dec _ _ _ body => roProgR16 good body
  | .seq a b => roProgR16 good a && roProgR16 good b
  | .ite _ a b => roProgR16 good a && roProgR16 good b
  | .while _ body => roProgR16 good body
  | .decCall _ _ f _ cont => good f && roProgR16 good cont
  | .call (some (none, none)) f _ => good f
  | .call (some (some (.local, _), none)) f _ => good f
  | .assign .local _ _ => true
  | .skip | .break | .continue | .annot _ _ | .raise _ _ | .return _ => true
  | _ => false

private theorem lex_ro16 {a1 a2 b1 b2 : Nat} (h : a1 < a2 ∨ a1 = a2 ∧ b1 < b2) :
    Prod.Lex (· < ·) (· < ·) (a1, b1) (a2, b2) := by
  rcases h with h | ⟨rfl, h⟩
  · exact Prod.Lex.left _ _ h
  · exact Prod.Lex.right _ h

theorem evaluate_roProgR16 {F : Type} (good : MlS → Bool)
    (hgood : ∀ f, good f = true → ∀ values body callee rs,
      lookupCodeHOLFinite originalRuntimeCode.lookup f values = some (body, callee, rs) →
      roProgR16 good body = true)
    (p : ProgHOL 64) (hp : roProgR16 good p = true)
    (s : PanSemStateFiniteExact 64 F) (hcode : s.code = originalRuntimeCode) :
    LocFrameR16 s (evaluateHOLFiniteState s p).2 := by
  cases shape : p with
  | skip => rw [evaluateHOLFiniteState_skip]; exact LocFrameR16.refl s
  | «break» => rw [evaluateHOLFiniteState_break]; exact LocFrameR16.refl s
  | «continue» => rw [evaluateHOLFiniteState_continue]; exact LocFrameR16.refl s
  | annot _ _ => rw [evaluateHOLFiniteState_annot]; exact LocFrameR16.refl s
  | «return» _ =>
    rw [evaluateHOLFiniteState_return]
    split
    · exact LocFrameR16.refl s
    · split <;> [rfl; exact LocFrameR16.refl s]
  | raise _ _ =>
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only
      split <;> [rfl; exact LocFrameR16.refl s]
    · exact LocFrameR16.refl s
  | assign kd x e =>
    cases kd with
    | global => simp [shape, roProgR16] at hp
    | «local» =>
      rw [evaluateHOLFiniteState_assign]
      split
      · exact LocFrameR16.refl s
      · split <;> [rfl; exact LocFrameR16.refl s]
  | dec nm _ _ body =>
    have hb : roProgR16 good body = true := by simpa [shape, roProgR16] using hp
    rw [evaluateHOLFiniteState_dec_total]; dsimp only
    split
    · exact LocFrameR16.refl s
    · rename_i val _
      split
      · have ih := evaluate_roProgR16 good hgood body hb (setVarHOLFinite nm val s) hcode
        unfold LocFrameR16 at ih ⊢; dsimp only; rw [ih]; rfl
      · exact LocFrameR16.refl s
  | seq a b =>
    have hab : roProgR16 good a = true ∧ roProgR16 good b = true := by
      simpa [shape, roProgR16, Bool.and_eq_true] using hp
    have ih1 := evaluate_roProgR16 good hgood a hab.1 s hcode
    have rem := evaluateHOLFiniteState_clock_le s a
    have meta' := PanRunBounded.evaluateHOLFiniteState_metadata s a
    rw [evaluateHOLFiniteState_seq_line780]
    rcases hr : evaluateHOLFiniteState s a with ⟨r1, mid⟩
    rw [hr] at ih1 rem meta'
    dsimp only at ih1 rem meta' ⊢
    cases r1 with
    | none =>
      have mclock : mid.clock ≤ s.clock := rem
      exact ih1.trans (evaluate_roProgR16 good hgood b hab.2 mid (meta'.1.trans hcode))
    | some _ => exact ih1
  | ite _ yes no =>
    have hy : roProgR16 good yes = true ∧ roProgR16 good no = true := by
      simpa [shape, roProgR16, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_roProgR16 good hgood no hy.2 s hcode
      · exact evaluate_roProgR16 good hgood yes hy.1 s hcode
    · exact LocFrameR16.refl s
  | «while» cond body =>
    have hb : roProgR16 good body = true := by simpa [shape, roProgR16] using hp
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · rfl
        · dsimp only
          rw [fixClockHOLFinite_evaluateState]
          have ih1 := evaluate_roProgR16 good hgood body hb (decClockHOLFinite s) hcode
          have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
          have meta' := PanRunBounded.evaluateHOLFiniteState_metadata (decClockHOLFinite s) body
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨r1, mid⟩
          rw [hbr] at ih1 rem meta'
          dsimp only at ih1 rem meta' ⊢
          have smaller : mid.clock < s.clock := by change mid.clock ≤ s.clock - 1 at rem; omega
          have ih1' : LocFrameR16 s mid := by unfold LocFrameR16 at ih1 ⊢; rw [ih1]; rfl
          cases r1 with
          | none =>
            exact ih1'.trans (evaluate_roProgR16 good hgood (.while cond body) (by simpa [roProgR16] using hb)
              mid (meta'.1.trans hcode))
          | some r =>
            cases r with
            | «continue» =>
              exact ih1'.trans (evaluate_roProgR16 good hgood (.while cond body) (by simpa [roProgR16] using hb)
                mid (meta'.1.trans hcode))
            | «break» | returned _ | exception _ _ | finalFfi _ | error | timeOut => exact ih1'
      · exact LocFrameR16.refl s
    · exact LocFrameR16.refl s
  | decCall nm _ fn args cont =>
    have hc : good fn = true ∧ roProgR16 good cont = true := by
      simpa [shape, roProgR16, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
    rcases evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
    · exact LocFrameR16.refl s
    · dsimp only
      rcases hl : lookupCodeHOLFinite s.code.lookup fn values with _ | ⟨body, callee, rs⟩
      · exact LocFrameR16.refl s
      · dsimp only
        have hl' : lookupCodeHOLFinite originalRuntimeCode.lookup fn values = some (body, callee, rs) := by
          rwa [← hcode]
        have bodyOk := hgood fn hc.1 values body callee rs hl'
        split
        · rfl
        · have ih1 := evaluate_roProgR16 good hgood body bodyOk (callEntryStateHOLFinite s callee) hcode
          have meta' := PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body
          have cl := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite s callee) body
          rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨res, st⟩
          rw [hrun] at ih1 meta' cl
          dsimp only at ih1 meta' cl ⊢
          change st.clock ≤ s.clock - 1 at cl
          have small : st.clock < s.clock := by omega
          have ih1' : LocFrameR16 s st := by unfold LocFrameR16 at ih1 ⊢; rw [ih1]; rfl
          cases res with
          | none => exact ih1'
          | some r =>
            cases r with
            | returned v =>
              dsimp only
              split
              · set resumed := setVarHOLFinite nm v { st with locals := s.locals }
                have smallR : resumed.clock < s.clock := small
                have ihR : LocFrameR16 s resumed := ih1'.with_locals_clock _ _
                have ih2 := evaluate_roProgR16 good hgood cont hc.2 resumed (meta'.1.trans hcode)
                exact (ihR.trans ih2).with_locals_clock _ _
              · exact ih1'
            | «break» | «continue» => exact ih1'
            | timeOut | error | exception _ _ | finalFfi _ => exact ih1'.with_locals_clock _ _
  | call tail fn args =>
    have htail_good : good fn = true ∧
        (tail = some (none, none) ∨ ∃ x, tail = some (some (.local, x), none)) := by
      rcases tail with _ | ⟨_ | ⟨kd, x⟩, _ | _⟩
      · simp [shape, roProgR16] at hp
      · exact ⟨by simpa [shape, roProgR16] using hp, Or.inl rfl⟩
      · simp [shape, roProgR16] at hp
      · cases kd
        · exact ⟨by simpa [shape, roProgR16] using hp, Or.inr ⟨x, rfl⟩⟩
        · simp [shape, roProgR16] at hp
      · simp [shape, roProgR16] at hp
    rw [evaluateHOLFiniteState_call]
    rcases evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
    · exact LocFrameR16.refl s
    · dsimp only
      rcases hl : lookupCodeHOLFinite s.code.lookup fn values with _ | ⟨body, callee, rs⟩
      · exact LocFrameR16.refl s
      · dsimp only
        have hl' : lookupCodeHOLFinite originalRuntimeCode.lookup fn values = some (body, callee, rs) := by
          rwa [← hcode]
        have bodyOk := hgood fn htail_good.1 values body callee rs hl'
        split
        · rfl
        · have ih1 := evaluate_roProgR16 good hgood body bodyOk (callEntryStateHOLFinite s callee) hcode
          have cl := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite s callee) body
          rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨res, st⟩
          rw [hrun] at ih1 cl
          dsimp only at ih1 cl ⊢
          change st.clock ≤ s.clock - 1 at cl
          have small : st.clock < s.clock := by omega
          have ih1' : LocFrameR16 s st := by unfold LocFrameR16 at ih1 ⊢; rw [ih1]; rfl
          rcases htail_good.2 with rfl | ⟨x, rfl⟩
          · cases res with
            | none => exact ih1'
            | some r =>
              cases r with
              | returned _ => dsimp only; split <;> [exact ih1'.with_locals_clock _ _; exact ih1']
              | «break» | «continue» => exact ih1'
              | timeOut | error | exception _ _ | finalFfi _ => exact ih1'.with_locals_clock _ _
          · cases res with
            | none => exact ih1'
            | some r =>
              cases r with
              | returned rv =>
                dsimp only
                split
                · by_cases hv : isValidValueHOLExact s.toExact .local x rv = true
                  · rw [if_pos hv]; exact ih1'.with_locals_clock _ _
                  · rw [if_neg hv]; exact ih1'
                · exact ih1'
              | «break» | «continue» => exact ih1'
              | timeOut | error | exception _ _ | finalFfi _ => exact ih1'.with_locals_clock _ _
  | _ => simp [shape, roProgR16] at hp
termination_by (s.clock, sizeOf p)
decreasing_by
  all_goals
    simp_wf
    apply lex_ro16
    try subst shape
    try simp only [setVarHOLFinite, decClockHOLFinite, callEntryStateHOLFinite, ProgHOL.seq.sizeOf_spec,
      ProgHOL.ite.sizeOf_spec, ProgHOL.dec.sizeOf_spec, ProgHOL.while.sizeOf_spec, ProgHOL.decCall.sizeOf_spec]
    first
      | exact Or.inl small
      | exact Or.inl smaller
      | exact Or.inl smallR
      | exact Or.inl (by omega)
      | (rcases Nat.lt_or_eq_of_le mclock with h | h
         · exact Or.inl h
         · right; refine ⟨h, ?_⟩; simp +arith)
      | (right; refine ⟨rfl, ?_⟩; simp +arith)
      | (right; refine ⟨trivial, ?_⟩; simp +arith)

theorem readOnlyFn_of_roProgR16 (idx : Nat) (hidx : idx < Guest.Software.guestAst.length)
    (decl : Decl (BitVec 64)) (hdecl : Guest.Software.guestAst[idx] = .function (extractFn decl))
    (good : MlS → Bool)
    (hgood : ∀ f, good f = true → ∀ values body callee rs,
      lookupCodeHOLFinite originalRuntimeCode.lookup f values = some (body, callee, rs) →
      roProgR16 good body = true)
    (hbody : roProgR16 good (FrontendCodecComputation.progToHOLStructural (extractFn decl).body) = true) :
    ReadOnlyFn (ofString (extractFn decl).name) := by
  refine ⟨_, _, _, lookup_of_guestAst_getElem idx hidx (extractFn decl) hdecl,
    fun s hcode _ _ _ _ => ?_⟩
  exact evaluate_roProgR16 good hgood _ hbody s hcode

theorem wsGetCodeCallees_good :
    ∀ f, wsGetCodeCallees f = true → ∀ values body callee rs,
      lookupCodeHOLFinite originalRuntimeCode.lookup f values = some (body, callee, rs) →
      roProgR16 wsGetCodeCallees body = true := by
  intro f hf values body callee rs hfound
  obtain ⟨params, rs', hinst⟩ := lookupCode_installed hfound
  simp only [wsGetCodeCallees, Bool.or_eq_true, beq_iff_eq] at hf
  rcases hf with ((rfl | rfl) | rfl) | rfl
  · have hl := lookup_of_guestAst_getElem 18 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_memeq) rfl
    change originalRuntimeCode.lookup (ofString "memeq") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; decide
  · have hl := lookup_of_guestAst_getElem 254 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_nodedb_lookup) rfl
    change originalRuntimeCode.lookup (ofString "nodedb_lookup") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; decide
  · have hl := lookup_of_guestAst_getElem 132 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_htab_get) rfl
    change originalRuntimeCode.lookup (ofString "htab_get") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; decide
  · have hl := lookup_of_guestAst_getElem 131 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_htab_find_leaf) rfl
    change originalRuntimeCode.lookup (ofString "htab_find_leaf") = _ at hl
    rw [hl] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; decide

theorem ro_ws_get_code : ReadOnlyFn (ofString "ws_get_code") :=
  readOnlyFn_of_roProgR16 370 (by rw [guestAst_len]; decide) Guest.Software.guestFn_ws_get_code rfl
    wsGetCodeCallees wsGetCodeCallees_good (by decide)

/-! ## 3. Lookups and `WorldKeepsSc` proofs -/

theorem lookup_record_pre_state_read :
    originalRuntimeCode.lookup (ofString "record_pre_state_read") =
      some ((sourceFunctionEntry Guest.Software.guestFn_record_pre_state_read).2) :=
  lookup_of_guestAst_getElem 364 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_record_pre_state_read) rfl

theorem lookup_mark_account_created :
    originalRuntimeCode.lookup (ofString "mark_account_created") =
      some ((sourceFunctionEntry Guest.Software.guestFn_mark_account_created).2) :=
  lookup_of_guestAst_getElem 393 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_mark_account_created) rfl

theorem lookup_get_code :
    originalRuntimeCode.lookup (ofString "get_code") =
      some ((sourceFunctionEntry Guest.Software.guestFn_get_code).2) :=
  lookup_of_guestAst_getElem 376 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_get_code) rfl

theorem wkSc_record_pre_state_read :
    WorldKeepsSc WorldOK (bufRegions []) ["heap_ptr"] stdKeep NoExtra
      (ofString "record_pre_state_read") := by
  have hB : ValidBufList [] := by intro p hp; cases hp
  have hgw : SafeStepGlobals ["heap_ptr"] := by intro g hg; simp at hg; subst hg; simp
  refine worldKeepsSc_of_progWStep lookup_record_pre_state_read ?_
  dsimp only [sourceFunctionEntry, Guest.Software.guestFn_record_pre_state_read,
    FrontendCodecComputation.declToHOLStructural, FrontendCodecComputation.funDeclToHOLStructural,
    FrontendCodecComputation.progToHOLStructural, FrontendCodecComputation.expToHOLStructural,
    FrontendCodecComputation.expListToHOLStructural, FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine progWStep_seq hB hgw ?_ (progWStep_return _ _ _)
  exact progWStep_call0_htab_set_recSlot "bs" "bs+72" 72 _ _ (by simp) (by decide)
    (fun s S hT hbs ht0 => nonValueSlot_bs72 s S hT hbs ht0)

theorem wkSc_mark_account_created :
    WorldKeepsSc WorldOK (bufRegions []) ["heap_ptr"] stdKeep NoExtra
      (ofString "mark_account_created") := by
  have hB : ValidBufList [] := by intro p hp; cases hp
  have hgw : SafeStepGlobals ["heap_ptr"] := by intro g hg; simp at hg; subst hg; simp
  refine worldKeepsSc_of_progWStep lookup_mark_account_created ?_
  dsimp only [sourceFunctionEntry, Guest.Software.guestFn_mark_account_created,
    FrontendCodecComputation.declToHOLStructural, FrontendCodecComputation.funDeclToHOLStructural,
    FrontendCodecComputation.progToHOLStructural, FrontendCodecComputation.expToHOLStructural,
    FrontendCodecComputation.expListToHOLStructural, FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine progWStep_seq hB hgw ?_ (progWStep_return _ _ _)
  exact progWStep_call0_htab_set_recSlot "ts" "ts+56" 56 _ _ (by simp) (by decide)
    (fun s S hT hts ht0 => nonValueSlot_ts56 s S hT hts ht0)

theorem wkSc_get_code :
    WorldKeepsSc WorldOK (bufRegions [("sk_buf", 52)]) ["heap_ptr"] stdKeep NoExtra
      (ofString "get_code") := by
  have hB : ValidBufList [("sk_buf", 52)] := by
    intro p hp; simp at hp; subst hp
    exact ⟨64, by decide, by decide, by decide⟩
  have hgw : SafeStepGlobals ["heap_ptr"] := by intro g hg; simp at hg; subst hg; simp
  refine worldKeepsSc_of_progWStep lookup_get_code ?_
  dsimp only [sourceFunctionEntry, Guest.Software.guestFn_get_code,
    FrontendCodecComputation.declToHOLStructural, FrontendCodecComputation.funDeclToHOLStructural,
    FrontendCodecComputation.progToHOLStructural, FrontendCodecComputation.expToHOLStructural,
    FrontendCodecComputation.expListToHOLStructural, FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  refine progWStep_decCall hB hgw (by intro p hp; cases hp) (by intro g hg; cases hg)
    (worldKeepsSc_of_readOnly EvmFrameSpecs.ro_memeq) ?_
  refine progWStep_seq hB hgw (progWStep_ite (progWStep_return _ _ _) (progWStep_skip _ _)) ?_
  refine progWStep_decCall hB hgw (by intro p hp; cases hp) (by intro g hg; cases hg)
    (worldKeepsSc_of_readOnly EvmFrameSpecs.ro_htab_get) ?_
  refine progWStep_seq hB hgw (progWStep_ite (progWStep_return _ _ _) (progWStep_skip _ _)) ?_
  refine progWStep_seq hB hgw
    (progWStep_call_local (by intro p hp; cases hp) (by intro g hg; cases hg)
      (worldKeepsSc_of_readOnly EvmFrameSpecs.ro_htab_get)) ?_
  refine progWStep_seq hB hgw (progWStep_ite (progWStep_return _ _ _) (progWStep_skip _ _)) ?_
  refine progWStep_decCall hB hgw (by intro p hp; exact hp) (by intro g hg; cases hg)
    worldKeepsSc_sk_make ?_
  refine progWStep_seq hB hgw
    (progWStep_call0_htab_set_recSlot "ts" "ts+40" 40 _ _ (by simp) (by decide)
      (fun s S hT hts ht0 => nonValueSlot_ts40 s S hT hts ht0)) ?_
  refine progWStep_decCall hB hgw (by intro p hp; cases hp) (by intro g hg; cases hg)
    (worldKeepsSc_of_readOnly ro_ws_get_code) ?_
  exact progWStep_return _ _ _

end InitECandidate.Solver.Wave8GuestInv.R16WkAcctWs

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards

open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R16WkAcctWs

theorem «wk_record_pre_state_read» :
    WorldKeeps WorldOK (fun _ => [])
    ["heap_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "record_pre_state_read") :=
  wkSc_record_pre_state_read.to_worldKeeps

theorem «wk_mark_account_created» :
    WorldKeeps WorldOK (fun _ => [])
    ["heap_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "mark_account_created") :=
  wkSc_mark_account_created.to_worldKeeps

theorem «wk_get_code» :
    WorldKeeps WorldOK (fun s => [(globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52)])
    ["heap_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    NoExtra (ofString "get_code") :=
  wkSc_get_code.to_worldKeeps

end InitECandidate.Solver.Wave8GuestInv.R16Shards
