import InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.Common
import InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.ReadOnly

/-! # `EvmPreservingSpec` for `u256_ws`-backed division/modulo helpers (`u256_div`, `u256_mod`, `u256_sdiv`, `u256_smod`, `u256_addmod`, `u256_mulmod`) -/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R11Shards
open InitECandidate.Solver.Wave8GuestInv.R11Shards.OpDispatchSpec
open InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA
open InitECandidate.Solver.Wave8Contracts.M23

/-! ## 1. Composable `WsSafe` judgment and `u256_ws` interval helper -/

def WsSafe {F : Type} (s : PanSemStateFiniteExact 64 F) (Rl : List Ivl)
    (out : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 F) : Prop :=
  (out.1 = none → ByteRegionEffect s out.2 Rl) ∧
  (Resumes out.1 → ByteRegionEffect s out.2 Rl)

theorem WsSafe.of_safeOrTrapped {F : Type} {s : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    {out : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 F}
    (hs : SafeOrTrapped s out) : WsSafe s Rl out := by
  rcases hs with hlf | ⟨hnn, _, _, hnr⟩
  · have heff : ByteRegionEffect s out.2 Rl := by
      have hr := (ByteRegionEffect.refl s Rl).with_locals_clock out.2.locals out.2.clock
      rwa [← hlf] at hr
    exact ⟨fun _ => heff, fun _ => heff⟩
  · exact ⟨fun h => absurd h hnn, fun hr => absurd hr hnr⟩

theorem WsSafe.of_readOnly {F : Type} {s : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    {prog : ProgHOL 64} (hcode : s.code = originalRuntimeCode)
    (hro : readOnlyProg opRoCallees prog = true) :
    WsSafe s Rl (evaluateHOLFiniteState s prog) :=
  WsSafe.of_safeOrTrapped (evaluate_readOnlyProg opRoCallees opRoCallees_good prog hro s hcode)

theorem WsSafe.skip {F : Type} (s : PanSemStateFiniteExact 64 F) (Rl : List Ivl) :
    WsSafe s Rl (evaluateHOLFiniteState s .skip) := by
  rw [evaluateHOLFiniteState_skip]
  exact ⟨fun _ => ByteRegionEffect.refl s Rl, fun _ => ByteRegionEffect.refl s Rl⟩

theorem WsSafe.return_exp {F : Type} (s : PanSemStateFiniteExact 64 F) (Rl : List Ivl)
    (e : ExpHOL 64) : WsSafe s Rl (evaluateHOLFiniteState s (.return e)) := by
  rw [evaluateHOLFiniteState_return]
  split
  · exact ⟨fun h => by simp at h, fun hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩
  · split
    · exact ⟨fun h => by simp at h,
        fun _ => (ByteRegionEffect.refl s Rl).with_locals_clock s.emptyLocalsHOLFinite.locals s.clock⟩
    · exact ⟨fun h => by simp at h, fun hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩

theorem WsSafe.assign_local {F : Type} (s : PanSemStateFiniteExact 64 F) (Rl : List Ivl)
    (nm : MlS) (e : ExpHOL 64) :
    WsSafe s Rl (evaluateHOLFiniteState s (.assign .local nm e)) := by
  rw [evaluateHOLFiniteState_assign]
  split
  · exact ⟨fun h => by simp at h, fun hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩
  · split
    · exact ⟨fun _ => (ByteRegionEffect.refl s Rl).with_locals_clock _ s.clock,
        fun hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩
    · exact ⟨fun h => by simp at h, fun hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩

theorem WsSafe.store_word {F : Type} {s : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    {dst val : ExpHOL 64}
    (hma_ord : s.memaddrs = ordinaryDomain)
    (hval_word : ∀ v : ValueHOL 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) val = some v →
      ∃ w : BitVec 64, v = .val (.word w))
    (hin : ∀ addr : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dst =
        some (.val (.word addr)) →
      s.memaddrs addr →
      ∃ i ∈ Rl, i.1 ≤ addr.toNat ∧ addr.toNat + 8 ≤ i.1 + i.2) :
    WsSafe s Rl (evaluateHOLFiniteState s (.store dst val)) := by
  rcases hrun : evaluateHOLFiniteState s (.store dst val) with ⟨r, post⟩
  refine ⟨fun hn => ?_, fun hr => ?_⟩
  · dsimp only at hn; subst hn
    exact (ByteRegionEffect.of_store_word hma_ord hrun hval_word hin).1
  · have hcf := (evaluate_store_control_frame s dst val).1
    rw [hrun] at hcf; dsimp only at hcf hr
    rcases hcf with h | h <;> (rw [h] at hr; rcases hr with ⟨_, h'⟩ | ⟨_, _, h', _⟩ <;> simp at h')

theorem WsSafe.seq {F : Type} {s : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    {p1 p2 : ProgHOL 64}
    (h1 : WsSafe s Rl (evaluateHOLFiniteState s p1))
    (h2 : (evaluateHOLFiniteState s p1).1 = none →
      ByteRegionEffect s (evaluateHOLFiniteState s p1).2 Rl →
      WsSafe (evaluateHOLFiniteState s p1).2 Rl
        (evaluateHOLFiniteState (evaluateHOLFiniteState s p1).2 p2)) :
    WsSafe s Rl (evaluateHOLFiniteState s (.seq p1 p2)) := by
  rw [evaluateHOLFiniteState_seq_line780]
  rcases hr1 : evaluateHOLFiniteState s p1 with ⟨r1, s1⟩
  rw [hr1] at h1 h2
  dsimp only at h1 h2 ⊢
  cases r1 with
  | none =>
    have he1 := h1.1 rfl
    have hs2 := h2 rfl he1
    exact ⟨fun hn => he1.trans (hs2.1 hn), fun hr => he1.trans (hs2.2 hr)⟩
  | some r0 =>
    exact ⟨fun h => by simp at h, h1.2⟩

theorem WsSafe.ite {F : Type} {s : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    {cond : ExpHOL 64} {yes no : ProgHOL 64}
    (hyes : ∀ w : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) cond =
        some (.val (.word w)) → w ≠ 0 → WsSafe s Rl (evaluateHOLFiniteState s yes))
    (hno : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) cond =
        some (.val (.word 0)) → WsSafe s Rl (evaluateHOLFiniteState s no)) :
    WsSafe s Rl (evaluateHOLFiniteState s (.ite cond yes no)) := by
  rw [evaluateHOLFiniteState_ite]
  split
  · rename_i w hw
    by_cases hw0 : w = 0
    · subst hw0; simp only [↓reduceIte]; exact hno hw
    · simp only [hw0, ↓reduceIte]; exact hyes w hw hw0
  · exact ⟨fun h => by simp at h, fun hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩

theorem WsSafe.dec {F : Type} {s : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    {nm : MlS} {sh : ShapeHOL} {init : ExpHOL 64} {body : ProgHOL 64}
    (hbody : ∀ v,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) init = some v →
      shapeEqHOL sh (shapeOfHOLExact v) = true →
      WsSafe (setVarHOLFinite nm v s) Rl (evaluateHOLFiniteState (setVarHOLFinite nm v s) body)) :
    WsSafe s Rl (evaluateHOLFiniteState s (.dec nm sh init body)) := by
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  split
  · exact ⟨fun h => by simp at h, fun hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩
  · rename_i v hv
    split
    · rename_i hsh
      have hb := hbody v hv hsh
      have he0 : ByteRegionEffect s (setVarHOLFinite nm v s) Rl :=
        (ByteRegionEffect.refl s Rl).with_locals_clock _ s.clock
      rcases hrun : evaluateHOLFiniteState (setVarHOLFinite nm v s) body with ⟨rb, sb⟩
      rw [hrun] at hb
      dsimp only at hb ⊢
      exact ⟨fun hn => (he0.trans (hb.1 hn)).with_locals_clock _ sb.clock,
             fun hr => (he0.trans (hb.2 hr)).with_locals_clock _ sb.clock⟩
    · exact ⟨fun h => by simp at h, fun hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩

theorem WsSafe.decCall {F : Type} {s : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    {nm : MlS} {sh : ShapeHOL} {fname : MlS} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (hcal : ∀ vals body callee rs,
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some vals →
      lookupCodeHOLFinite s.code.lookup fname vals = some (body, callee, rs) →
      s.clock ≠ 0 →
      WsSafe (callEntryStateHOLFinite s callee) Rl
        (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body))
    (hcont : ∀ vals body callee rs v cpost,
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some vals →
      lookupCodeHOLFinite s.code.lookup fname vals = some (body, callee, rs) →
      s.clock ≠ 0 →
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), cpost) →
      ByteRegionEffect s cpost Rl →
      shapeEqHOL (shapeOfHOLExact v) sh = true →
      shapeEqHOL (shapeOfHOLExact v) rs = true →
      WsSafe (setVarHOLFinite nm v { cpost with locals := s.locals }) Rl
        (evaluateHOLFiniteState (setVarHOLFinite nm v { cpost with locals := s.locals }) cont)) :
    WsSafe s Rl (evaluateHOLFiniteState s (.decCall nm sh fname args cont)) := by
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vals
  · exact ⟨fun h => by simp at h, fun hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩
  · dsimp only
    rcases hl : lookupCodeHOLFinite s.code.lookup fname vals with _ | ⟨body, callee, rs⟩
    · exact ⟨fun h => by simp at h, fun hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩
    · dsimp only
      by_cases hz : s.clock = 0
      · rw [if_pos hz]
        exact ⟨fun h => by simp at h, fun hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩
      · rw [if_neg hz]
        have hc := hcal vals body callee rs hargs hl hz
        have he_ce : ByteRegionEffect s (callEntryStateHOLFinite s callee) Rl :=
          (ByteRegionEffect.refl s Rl).with_locals_clock callee (s.clock - 1)
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨rb, cpost⟩
        rw [hrun] at hc
        dsimp only at hc ⊢
        cases rb with
        | none =>
          exact ⟨fun h => by simp at h, fun hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩
        | some r0 =>
          cases r0 with
          | returned v =>
            have he_cp : ByteRegionEffect s cpost Rl := he_ce.trans (hc.2 (Or.inl ⟨v, rfl⟩))
            dsimp only
            split
            · rename_i hsh
              obtain ⟨hsh1, hsh2⟩ := Bool.and_eq_true_iff.1 hsh
              have hco := hcont vals body callee rs v cpost hargs hl hz hrun he_cp hsh1 hsh2
              have he_res : ByteRegionEffect s (setVarHOLFinite nm v { cpost with locals := s.locals }) Rl :=
                he_cp.with_locals_clock _ cpost.clock
              rcases hrc : evaluateHOLFiniteState (setVarHOLFinite nm v { cpost with locals := s.locals }) cont with ⟨rc, sp⟩
              rw [hrc] at hco
              dsimp only at hco ⊢
              exact ⟨fun hn => (he_res.trans (hco.1 hn)).with_locals_clock _ sp.clock,
                     fun hr => (he_res.trans (hco.2 hr)).with_locals_clock _ sp.clock⟩
            · exact ⟨fun h => by simp at h, fun hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩
          | exception eid ev =>
            dsimp only
            exact ⟨fun h => by simp at h,
              fun hr => by
                rcases hr with ⟨_, h⟩ | ⟨e', v', h, hne⟩
                · simp at h
                · injection h with h'; injection h' with h1 h2; subst h1 h2
                  exact (he_ce.trans (hc.2 (Or.inr ⟨eid, ev, rfl, hne⟩))).with_locals_clock _ cpost.clock⟩
          | timeOut | error | «break» | «continue» | finalFfi _ =>
            exact ⟨fun h => by simp at h, fun hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩

theorem WsSafe.call_void {F : Type} {s : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    {fname : MlS} {args : List (ExpHOL 64)}
    (hcal : ∀ vals body callee rs,
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some vals →
      lookupCodeHOLFinite s.code.lookup fname vals = some (body, callee, rs) →
      s.clock ≠ 0 →
      WsSafe (callEntryStateHOLFinite s callee) Rl
        (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body)) :
    WsSafe s Rl (evaluateHOLFiniteState s (.call (some (none, none)) fname args)) := by
  rw [evaluateHOLFiniteState_call]
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vals
  · exact ⟨fun h => by simp at h, fun hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩
  · dsimp only
    rcases hl : lookupCodeHOLFinite s.code.lookup fname vals with _ | ⟨body, callee, rs⟩
    · exact ⟨fun h => by simp at h, fun hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩
    · dsimp only
      by_cases hz : s.clock = 0
      · rw [if_pos hz]
        exact ⟨fun h => by simp at h, fun hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩
      · rw [if_neg hz]
        have hc := hcal vals body callee rs hargs hl hz
        have he_ce : ByteRegionEffect s (callEntryStateHOLFinite s callee) Rl :=
          (ByteRegionEffect.refl s Rl).with_locals_clock callee (s.clock - 1)
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨rb, cpost⟩
        rw [hrun] at hc
        cases rb with
        | none =>
          exact ⟨fun h => by simp at h, fun hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩
        | some r0 =>
          cases r0 with
          | returned v =>
            have he_cp : ByteRegionEffect s cpost Rl := he_ce.trans (hc.2 (Or.inl ⟨v, rfl⟩))
            dsimp only
            split
            · exact ⟨fun _ => he_cp.with_locals_clock s.locals cpost.clock,
                fun hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩
            · exact ⟨fun h => by simp at h, fun hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩
          | exception eid ev =>
            exact ⟨fun h => by simp at h,
              fun hr => by
                rcases hr with ⟨_, h⟩ | ⟨e', v', h, hne⟩
                · simp at h
                · injection h with h'; injection h' with h1 h2; subst h1 h2
                  exact (he_ce.trans (hc.2 (Or.inr ⟨eid, ev, rfl, hne⟩))).with_locals_clock _ cpost.clock⟩
          | timeOut | error | «break» | «continue» | finalFfi _ =>
            exact ⟨fun h => by simp at h, fun hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩

theorem WsSafe.call_tail {F : Type} {s : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    {fname : MlS} {args : List (ExpHOL 64)}
    (hcal : ∀ vals body callee rs,
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some vals →
      lookupCodeHOLFinite s.code.lookup fname vals = some (body, callee, rs) →
      s.clock ≠ 0 →
      WsSafe (callEntryStateHOLFinite s callee) Rl
        (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body)) :
    WsSafe s Rl (evaluateHOLFiniteState s (.call none fname args)) := by
  rw [evaluateHOLFiniteState_call]
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vals
  · exact ⟨fun h => by simp at h, fun hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩
  · dsimp only
    rcases hl : lookupCodeHOLFinite s.code.lookup fname vals with _ | ⟨body, callee, rs⟩
    · exact ⟨fun h => by simp at h, fun hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩
    · dsimp only
      by_cases hz : s.clock = 0
      · rw [if_pos hz]
        exact ⟨fun h => by simp at h, fun hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩
      · rw [if_neg hz]
        have hc := hcal vals body callee rs hargs hl hz
        have he_ce : ByteRegionEffect s (callEntryStateHOLFinite s callee) Rl :=
          (ByteRegionEffect.refl s Rl).with_locals_clock callee (s.clock - 1)
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨rb, cpost⟩
        rw [hrun] at hc
        cases rb with
        | none =>
          exact ⟨fun h => by simp at h, fun hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩
        | some r0 =>
          cases r0 with
          | returned v =>
            have he_cp : ByteRegionEffect s cpost Rl := he_ce.trans (hc.2 (Or.inl ⟨v, rfl⟩))
            dsimp only
            split
            · exact ⟨fun h => by simp at h,
                fun _ => he_cp.with_locals_clock cpost.emptyLocalsHOLFinite.locals cpost.clock⟩
            · exact ⟨fun h => by simp at h, fun hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩
          | exception eid ev =>
            exact ⟨fun h => by simp at h,
              fun hr => by
                rcases hr with ⟨_, h⟩ | ⟨e', v', h, hne⟩
                · simp at h
                · injection h with h'; injection h' with h1 h2; subst h1 h2
                  exact (he_ce.trans (hc.2 (Or.inr ⟨eid, ev, rfl, hne⟩))).with_locals_clock _ cpost.clock⟩
          | timeOut | error | «break» | «continue» | finalFfi _ =>
            exact ⟨fun h => by simp at h, fun hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩

def noTopBreakContinue : ProgHOL 64 → Bool
  | .break | .continue => false
  | .seq a b => noTopBreakContinue a && noTopBreakContinue b
  | .ite _ a b => noTopBreakContinue a && noTopBreakContinue b
  | .dec _ _ _ b => noTopBreakContinue b
  | .decCall _ _ _ _ b => noTopBreakContinue b
  | .while _ _ | .assign .local _ _ | .store _ _ | .storeByte _ _ | .skip | .return _ | .raise _ _
  | .call none _ _ | .call (some (_, none)) _ _ => true
  | _ => false

theorem evaluate_noTopBreakContinue {F : Type} (p : ProgHOL 64)
    (hp : noTopBreakContinue p = true) (s : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState s p).1 ≠ some .break ∧
    (evaluateHOLFiniteState s p).1 ≠ some .continue := by
  cases shape : p with
  | «break» | «continue» => simp [shape, noTopBreakContinue] at hp
  | skip => simp [evaluateHOLFiniteState_skip]
  | «return» _ =>
    rw [evaluateHOLFiniteState_return]
    split
    · simp
    · split <;> simp
  | raise _ _ =>
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only; split <;> simp
    · simp
  | assign k _ _ =>
    cases k with
    | global => simp [shape, noTopBreakContinue] at hp
    | «local» =>
      rw [evaluateHOLFiniteState_assign]
      split
      · simp
      · split <;> simp
  | store _ _ =>
    rw [evaluateHOLFiniteState_store]
    split
    · split
      · split <;> simp
      · simp
    · simp
  | storeByte _ _ =>
    rw [evaluateHOLFiniteState_storeByte]
    split
    · split
      · split <;> simp
      · simp
    · simp
  | seq a b =>
    have hab : noTopBreakContinue a = true ∧ noTopBreakContinue b = true := by
      simpa [shape, noTopBreakContinue, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_seq_line780]
    have ha := evaluate_noTopBreakContinue a hab.1 s
    rcases hr : evaluateHOLFiniteState s a with ⟨r, m⟩
    rw [hr] at ha
    cases r with
    | none => exact evaluate_noTopBreakContinue b hab.2 m
    | some _ => exact ha
  | ite _ a b =>
    have hab : noTopBreakContinue a = true ∧ noTopBreakContinue b = true := by
      simpa [shape, noTopBreakContinue, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_noTopBreakContinue b hab.2 s
      · exact evaluate_noTopBreakContinue a hab.1 s
    · simp
  | dec nm _ _ b =>
    have hb : noTopBreakContinue b = true := by simpa [shape, noTopBreakContinue] using hp
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · simp
    · rename_i v _
      split
      · have h := evaluate_noTopBreakContinue b hb (setVarHOLFinite nm v s)
        rcases hrun : evaluateHOLFiniteState (setVarHOLFinite nm v s) b with ⟨rb, sb⟩
        rw [hrun] at h
        exact h
      · simp
  | decCall nm _ fn args b =>
    have hb : noTopBreakContinue b = true := by simpa [shape, noTopBreakContinue] using hp
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
    rcases evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vals
    · simp
    · dsimp only
      rcases lookupCodeHOLFinite s.code.lookup fn vals with _ | ⟨body, callee, rs⟩
      · simp
      · dsimp only
        split
        · simp
        · rcases evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨rb, cpost⟩
          cases rb with
          | none => simp
          | some r0 =>
            cases r0 with
            | returned v =>
              dsimp only
              split
              · have h := evaluate_noTopBreakContinue b hb (setVarHOLFinite nm v { cpost with locals := s.locals })
                rcases hrc : evaluateHOLFiniteState (setVarHOLFinite nm v { cpost with locals := s.locals }) b with ⟨rc, sp⟩
                rw [hrc] at h
                exact h
              · simp
            | exception _ _ | timeOut | error | «break» | «continue» | finalFfi _ => simp
  | «while» cond body =>
    suffices ∀ (k : Nat) (t : PanSemStateFiniteExact 64 F), t.clock = k →
        (evaluateHOLFiniteState t (.while cond body)).1 ≠ some .break ∧
        (evaluateHOLFiniteState t (.while cond body)).1 ≠ some .continue from
      this s.clock s rfl
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro t hclk
      rw [evaluateHOLFiniteState_while_fixClockRewrite]
      rcases evalHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) cond with _ | cv
      · simp
      · rcases cv with ⟨⟨w⟩⟩ | _ | _
        · dsimp only
          split
          · split
            · simp
            · rename_i hw hk0
              have hb_clk := Flapjack.evaluateHOLFiniteState_clock_le (decClockHOLFinite t) body
              have hd_lt : (decClockHOLFinite t).clock < k := by
                simp [decClockHOLFinite, hclk]; omega
              rcases hbo : evaluateHOLFiniteState (decClockHOLFinite t) body with ⟨rb, sb⟩
              rw [hbo] at hb_clk
              cases rb with
              | none => exact ih sb.clock (lt_of_le_of_lt hb_clk hd_lt) sb rfl
              | some r0 =>
                cases r0 with
                | «continue» => exact ih sb.clock (lt_of_le_of_lt hb_clk hd_lt) sb rfl
                | «break» | returned _ | exception _ _ | timeOut | error | finalFfi _ => simp
          · simp
        · simp
        · simp
  | call ret fn args =>
    cases hret : ret with
    | none =>
      rw [evaluateHOLFiniteState_call]
      rcases evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vals
      · simp
      · dsimp only
        rcases lookupCodeHOLFinite s.code.lookup fn vals with _ | ⟨body, callee, rs⟩
        · simp
        · dsimp only
          split
          · simp
          · rcases evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨rb, cpost⟩
            cases rb with
            | none => simp
            | some r0 =>
              cases r0 with
              | returned _ => dsimp only; split <;> simp
              | exception _ _ | timeOut | error | «break» | «continue» | finalFfi _ => simp
    | some rk =>
      rcases rk with ⟨rk1, rk2⟩
      cases rk2 with
      | some _ => simp [shape, hret, noTopBreakContinue] at hp
      | none =>
        rw [evaluateHOLFiniteState_call]
        rcases evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vals
        · simp
        · dsimp only
          rcases lookupCodeHOLFinite s.code.lookup fn vals with _ | ⟨body, callee, rs⟩
          · simp
          · dsimp only
            split
            · simp
            · rcases evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨rb, cpost⟩
              cases rb with
              | none => simp
              | some r0 =>
                cases r0 with
                | returned _ =>
                  cases rk1 with
                  | none => dsimp only; split <;> simp
                  | some kv =>
                    rcases kv with ⟨k, nm⟩
                    dsimp only
                    split
                    · split <;> simp
                    · simp
                | exception _ _ | timeOut | error | «break» | «continue» | finalFfi _ => simp
  | _ => simp [shape, noTopBreakContinue] at hp
termination_by sizeOf p
decreasing_by
  all_goals
    simp_wf
    subst shape
    simp +arith only [ProgHOL.seq.sizeOf_spec, ProgHOL.ite.sizeOf_spec,
      ProgHOL.dec.sizeOf_spec, ProgHOL.decCall.sizeOf_spec]

theorem WsSafe.while_loop {F : Type} {cond : ExpHOL 64} {body : ProgHOL 64} {Rl : List Ivl}
    (hnb : noTopBreakContinue body = true)
    (P : PanSemStateFiniteExact 64 F → Prop)
    (hdec : ∀ t, P t → P (decClockHOLFinite t))
    (hbody : ∀ t w, P (decClockHOLFinite t) →
      @evalHOLFinite 64 F _ t (fun a => Classical.propDecidable (t.memaddrs a)) cond =
        some (.val (.word w)) → w ≠ 0 →
      WsSafe (decClockHOLFinite t) Rl (evaluateHOLFiniteState (decClockHOLFinite t) body) ∧
      ((evaluateHOLFiniteState (decClockHOLFinite t) body).1 = none →
        P (evaluateHOLFiniteState (decClockHOLFinite t) body).2)) :
    ∀ s, P s → WsSafe s Rl (evaluateHOLFiniteState s (.while cond body)) := by
  have hmain : ∀ (k : Nat) (s : PanSemStateFiniteExact 64 F), s.clock = k → P s →
      WsSafe s Rl (evaluateHOLFiniteState s (.while cond body)) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro s hclk hPs
      rw [evaluateHOLFiniteState_while_fixClockRewrite]
      rcases hc : @evalHOLFinite 64 F _ s (fun a => Classical.propDecidable (s.memaddrs a)) cond with
        _ | cv
      · exact ⟨fun h => by simp at h, fun hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩
      · rcases cv with ⟨⟨w⟩⟩ | _ | _
        · dsimp only
          by_cases hw : w = 0
          · subst hw
            exact ⟨fun _ => ByteRegionEffect.refl s Rl, fun _ => ByteRegionEffect.refl s Rl⟩
          · rw [if_pos hw]
            by_cases hk0 : s.clock = 0
            · rw [if_pos hk0]
              exact ⟨fun h => by simp at h, fun hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩
            · rw [if_neg hk0]
              have ⟨hsb, hPb⟩ := hbody s w (hdec s hPs) hc hw
              have ⟨hnbr, hnco⟩ := evaluate_noTopBreakContinue body hnb (decClockHOLFinite s)
              have he_dec : ByteRegionEffect s (decClockHOLFinite s) Rl :=
                (ByteRegionEffect.refl s Rl).with_locals_clock s.locals (s.clock - 1)
              have hb_clk := Flapjack.evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
              have hd_lt : (decClockHOLFinite s).clock < k := by
                simp [decClockHOLFinite, hclk]; omega
              rcases hbo : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨rb, sb⟩
              rw [hbo] at hsb hPb hnbr hnco hb_clk
              dsimp only at hsb hPb hnbr hnco hb_clk ⊢
              cases rb with
              | none =>
                have he_b := hsb.1 rfl
                have jih := ih sb.clock (lt_of_le_of_lt hb_clk hd_lt) sb rfl (hPb rfl)
                exact ⟨fun hn => (he_dec.trans he_b).trans (jih.1 hn),
                       fun hr => (he_dec.trans he_b).trans (jih.2 hr)⟩
              | some r0 =>
                cases r0 with
                | «continue» => exact absurd rfl hnco
                | «break» => exact absurd rfl hnbr
                | returned v =>
                  exact ⟨fun h => by simp at h, fun _ => he_dec.trans (hsb.2 (Or.inl ⟨v, rfl⟩))⟩
                | exception eid ev =>
                  exact ⟨fun h => by simp at h,
                    fun hr => by
                      rcases hr with ⟨_, h⟩ | ⟨e', v', h, hne⟩
                      · simp at h
                      · injection h with h'; injection h' with h1 h2; subst h1 h2
                        exact he_dec.trans (hsb.2 (Or.inr ⟨eid, ev, rfl, hne⟩))⟩
                | timeOut | error | finalFfi _ =>
                  exact ⟨fun h => by simp at h, fun hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩
        · exact ⟨fun h => by simp at h, fun hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩
        · exact ⟨fun h => by simp at h, fun hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩
  intro s hPs; exact hmain s.clock s rfl hPs

/-! ## 2. `WsEnv` invariant and `u256_ws` interval helpers -/

structure WsEnv {F : Type} (s0 s : PanSemStateFiniteExact 64 F) : Prop where
  code    : s.code = originalRuntimeCode
  memaddrs : s.memaddrs = ordinaryDomain
  globals : s.globals = s0.globals
  ws_bnd  : globN s0 "u256_ws" = 0 ∨ globN s0 "u256_ws" + 640 ≤ 2 ^ 64

theorem WsEnv.of_evmInv {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    (hc : s0.code = originalRuntimeCode) (hInv : EvmInv s0) : WsEnv s0 s0 := by
  refine ⟨hc, hInv.1.1.2, rfl, ?_⟩
  obtain ⟨hAs, S, hW, _⟩ := hInv
  have hF := hW.2.2.1
  have hmem : (globN s0 "u256_ws", if globN s0 "u256_ws" = 0 then 0 else 640) ∈ fixedObjects s0 := by
    unfold fixedObjects
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    exact List.mem_map.2 ⟨("u256_ws", 640), by decide, rfl⟩
  rcases fixedObject_le_2pow64 hAs.2 hF hmem with h0 | hle
  · dsimp only at h0
    by_cases hz : globN s0 "u256_ws" = 0
    · exact Or.inl hz
    · rw [if_neg hz] at h0; omega
  · dsimp only at hle
    by_cases hz : globN s0 "u256_ws" = 0
    · exact Or.inl hz
    · rw [if_neg hz] at hle; exact Or.inr hle

theorem WsEnv.step {F : Type} {s0 s t : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (he : WsEnv s0 s) (heff : ByteRegionEffect s t Rl) : WsEnv s0 t :=
  ⟨heff.code.trans he.code, heff.memaddrs.trans he.memaddrs,
   heff.globals.trans he.globals, he.ws_bnd⟩

theorem WsEnv.with_locals_clock {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    (he : WsEnv s0 s) (L : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    WsEnv s0 { s with locals := L, clock := k } :=
  ⟨he.code, he.memaddrs, he.globals, he.ws_bnd⟩

theorem WsEnv.u256_ws_in_ivls {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    (he : WsEnv s0 s) {addr : BitVec 64} {off : Nat}
    (hdom : s.memaddrs addr)
    (hoff : off + 8 ≤ 640)
    (haddr : addr = BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 off) :
    ∃ i ∈ untypedGlobalBufIvls s0, i.1 ≤ addr.toNat ∧ addr.toNat + 8 ≤ i.1 + i.2 := by
  have hdom' : ordinaryDomain addr := he.memaddrs ▸ hdom
  have ha_lo : 2701131776 ≤ addr.toNat := ((ordinaryDomain_iff addr).1 hdom').1
  rcases he.ws_bnd with hz | hle
  · rw [hz] at haddr
    have ha_eq : addr.toNat = off := by
      rw [haddr]; simp only [BitVec.ofNat_eq_ofNat, BitVec.zero_add, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by omega)
    omega
  · have hnz : globN s0 "u256_ws" ≠ 0 := by
      intro hz; rw [hz] at haddr
      have ha_eq : addr.toNat = off := by
        rw [haddr]; simp only [BitVec.ofNat_eq_ofNat, BitVec.zero_add, BitVec.toNat_ofNat]
        exact Nat.mod_eq_of_lt (by omega)
      omega
    have ha_eq : addr.toNat = globN s0 "u256_ws" + off := by
      rw [haddr]
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show globN s0 "u256_ws" < 2 ^ 64 by omega),
        Nat.mod_eq_of_lt (show off < 2 ^ 64 by omega),
        Nat.mod_eq_of_lt (show globN s0 "u256_ws" + off < 2 ^ 64 by omega)]
    refine ⟨(globN s0 "u256_ws", if globN s0 "u256_ws" = 0 then 0 else 640), ?_, ?_, ?_⟩
    · simp [untypedGlobalBufIvls]
    · dsimp only; omega
    · dsimp only; rw [if_neg hnz]; omega

theorem eval_global_word_eq_ofNat {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    (hg : s.globals = s0.globals) {g : String} {w : BitVec 64}
    (hlk : s.globals.lookup (ofString g) = some (.val (.word w))) :
    w = BitVec.ofNat 64 (globN s0 g) := by
  unfold globN
  rw [← hg, hlk]
  simp

/-! ## 3. Word-expression totality helpers -/

theorem eval_word_of_op {F : Type} {s : PanSemStateFiniteExact 64 F}
    {bop : BinOp} {es : List (ExpHOL 64)} {v : ValueHOL 64}
    (h : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op bop es) = some v) :
    ∃ w : BitVec 64, v = .val (.word w) := by
  simp only [evalHOLExact, wordOpHOL] at h; revert h
  rcases @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) es with _ | vs
  · simp
  · dsimp only; split
    · simp only [Option.map]
      rcases wordOp bop (vs.map valueWord) with _ | w
      · simp
      · intro hv; injection hv with hv'; exact ⟨w, hv'.symm⟩
    · simp

theorem eval_word_of_shift {F : Type} {s : PanSemStateFiniteExact 64 F}
    {sh : Shift} {e1 e2 : ExpHOL 64} {v : ValueHOL 64}
    (h : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.shift sh e1 e2) = some v) :
    ∃ w : BitVec 64, v = .val (.word w) := by
  simp only [evalHOLExact, wordShiftHOL] at h; revert h
  rcases @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e1 with _ | v1
  · simp
  · rcases v1 with ⟨⟨w1⟩⟩ | _ | _ <;> simp
    rcases @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e2 with _ | v2
    · simp
    · rcases v2 with ⟨⟨w2⟩⟩ | _ | _ <;> simp
      intro w _ _ hv; exact ⟨w, hv.symm⟩

theorem eval_word_of_const {F : Type} {s : PanSemStateFiniteExact 64 F}
    {k : BitVec 64} {v : ValueHOL 64}
    (h : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.const k) = some v) :
    ∃ w : BitVec 64, v = .val (.word w) := by
  simp only [evalHOLExact, Option.some.injEq] at h
  exact ⟨k, h.symm⟩

theorem eval_word_of_shape_one {v : ValueHOL 64}
    (h : shapeEqHOL .one (shapeOfHOLExact v) = true ∨ shapeEqHOL (shapeOfHOLExact v) .one = true) :
    ∃ w : BitVec 64, v = .val (.word w) := by
  rcases v with ⟨⟨w⟩⟩ | _ | _
  · exact ⟨w, rfl⟩
  · rcases h with h1 | h1 <;> simp [shapeOfHOLExact, shapeEqHOL] at h1
  · rcases h with h1 | h1 <;> simp [shapeOfHOLExact, shapeEqHOL] at h1

theorem eval_comb4_of_shape {v : ValueHOL 64}
    (h : shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact v) = true ∨
         shapeEqHOL (shapeOfHOLExact v) (.comb [.one, .one, .one, .one]) = true) :
    ∃ w0 w1 w2 w3 : BitVec 64,
      v = .rStruct [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3)] := by
  have hsh : shapeOfHOLExact v = .comb [.one, .one, .one, .one] := by
    rcases h with hh | hh
    · exact ((shapeEqHOL_eq_true _ _).1 hh).symm
    · exact (shapeEqHOL_eq_true _ _).1 hh
  rcases v with _ | fs | _
  · simp [shapeOfHOLExact] at hsh
  · simp only [shapeOfHOLExact, ShapeHOL.comb.injEq] at hsh
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
  · simp [shapeOfHOLExact] at hsh

/-! ## 4. `u256_to_digits` and `digits_len` specifications -/

theorem lookup_u256_to_digits :
    originalRuntimeCode.lookup (ofString "u256_to_digits") =
      some ([(ofString "p", .one), (ofString "a", .comb [.one, .one, .one, .one])],
            InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
              (extractFn Guest.Software.guestFn_u256_to_digits).body, .one) :=
  lookup_of_guestAst_getElem 64 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_u256_to_digits) rfl

theorem lookup_digits_to_u256 :
    originalRuntimeCode.lookup (ofString "digits_to_u256") =
      some ([(ofString "p", .one)],
            InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
              (extractFn Guest.Software.guestFn_digits_to_u256).body,
            .comb [.one, .one, .one, .one]) :=
  lookup_of_guestAst_getElem 65 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_digits_to_u256) rfl

theorem lookup_digits_len :
    originalRuntimeCode.lookup (ofString "digits_len") =
      some ([(ofString "p", .one), (ofString "n", .one)],
            InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
              (extractFn Guest.Software.guestFn_digits_len).body, .one) :=
  lookup_of_guestAst_getElem 66 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_digits_len) rfl

theorem lookup_divmnu :
    originalRuntimeCode.lookup (ofString "divmnu") =
      some ([(ofString "q", .one), (ofString "r", .one), (ofString "u", .one),
             (ofString "m", .one), (ofString "v", .one), (ofString "n", .one)],
            InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
              (extractFn Guest.Software.guestFn_divmnu).body, .one) :=
  lookup_of_guestAst_getElem 67 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_divmnu) rfl

theorem lookup_digits_divmod :
    originalRuntimeCode.lookup (ofString "digits_divmod") =
      some ([(ofString "u", .one), (ofString "m", .one), (ofString "d", .comb [.one, .one, .one, .one])],
            InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
              (extractFn Guest.Software.guestFn_digits_divmod).body,
            .comb [.one, .one, .one, .one]) :=
  lookup_of_guestAst_getElem 68 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_digits_divmod) rfl

theorem lookup_u256_divmod :
    originalRuntimeCode.lookup (ofString "u256_divmod") =
      some ([(ofString "a", .comb [.one, .one, .one, .one]), (ofString "b", .comb [.one, .one, .one, .one])],
            InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
              (extractFn Guest.Software.guestFn_u256_divmod).body,
            .comb [.one, .one, .one, .one, .one, .one, .one, .one]) :=
  lookup_of_guestAst_getElem 69 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_u256_divmod) rfl

private theorem single_word_store_eff_mem {F : Type} {s0 s post : PanSemStateFiniteExact 64 F}
    (he : WsEnv s0 s) {dst val : ExpHOL 64} {off : Nat} {w : BitVec 64}
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dst =
      some (.val (.word (BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 off))))
    (hval : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) val =
      some (.val (.word w)))
    (hoff : off + 8 ≤ 640)
    (hrun : evaluateHOLFiniteState s (.store dst val) = (none, post)) :
    let addr := BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 off
    ByteRegionEffect s post (untypedGlobalBufIvls s0) ∧
    post.locals = s.locals ∧
    post.memory addr = .word w ∧
    (∀ x : BitVec 64, x ≠ addr → post.memory x = s.memory x) := by
  dsimp only
  let addr := BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 off
  obtain ⟨heff, hloc⟩ := ByteRegionEffect.of_store_word he.memaddrs hrun
    (fun v hv => by rw [hval] at hv; injection hv with hv'; exact ⟨w, hv'.symm⟩)
    (fun a ha hdom => by
      rw [hdst] at ha; injection ha with ha'; injection ha' with ha''; injection ha'' with ha3; subst ha3
      exact he.u256_ws_in_ivls hdom hoff rfl)
  rw [evaluateHOLFiniteState_store, hdst, hval] at hrun
  dsimp only at hrun
  revert hrun
  split
  · rename_i m' hst
    unfold flattenHOL panMemStoresHOL panMemStoreHOL at hst
    by_cases hdom : s.memaddrs addr
    · simp only [addr, hdom, ↓reduceIte, panMemStoresHOL, Option.some.injEq] at hst
      subst hst
      intro hrun; injection hrun with _ hpost; subst hpost
      exact ⟨heff, rfl, by simp, fun x hx => by simp [hx]⟩
    · simp [addr, hdom] at hst
  · simp

theorem u256_to_digits_wsSafe_and_post {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    (he : WsEnv s0 s) {off : Nat} {a0 a1 a2 a3 : BitVec 64}
    (hoff : off + 64 ≤ 640)
    (hp : s.locals.lookup (ofString "p") =
      some (.val (.word (BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 off))))
    (ha : s.locals.lookup (ofString "a") =
      some (.rStruct [.val (.word a0), .val (.word a1), .val (.word a2), .val (.word a3)])) :
    let body := InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
      (extractFn Guest.Software.guestFn_u256_to_digits).body
    WsSafe s (untypedGlobalBufIvls s0) (evaluateHOLFiniteState s body) ∧
    (∀ v cpost, evaluateHOLFiniteState s body = (some (.returned v), cpost) →
      (a0 ||| a1 ||| a2 ||| a3) ≠ 0 →
      ∃ k : Nat, k < 8 ∧
        ∃ wk : BitVec 64, wk ≠ 0 ∧
          cpost.memory (BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 off +
            BitVec.ofNat 64 (8 * k)) = .word wk) := by
  dsimp only [extractFn, Guest.Software.guestFn_u256_to_digits,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural, List.map]
  let pbase := BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 off
  have hadd_assoc : ∀ c : Nat, c < 64 →
      pbase + BitVec.ofNat 64 c = BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 (off + c) := by
    intro c hc
    dsimp only [pbase]
    rw [BitVec.add_assoc]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show off < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show c < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show off + c < 2 ^ 64 by omega)]
  have hstep_ws : ∀ {t : PanSemStateFiniteExact 64 F} (ht : WsEnv s0 t)
      (hpt : t.locals.lookup (ofString "p") = some (.val (.word pbase)))
      (c : Nat) (hc : c ≤ 56) (dstExp valExp : ExpHOL 64)
      (hdst : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) dstExp =
        some (.val (.word (pbase + BitVec.ofNat 64 c))))
      (hvw : ∀ vv, @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) valExp =
        some vv → ∃ w : BitVec 64, vv = .val (.word w)),
      WsSafe t (untypedGlobalBufIvls s0) (evaluateHOLFiniteState t (.store dstExp valExp)) ∧
      ((evaluateHOLFiniteState t (.store dstExp valExp)).1 = none →
        (evaluateHOLFiniteState t (.store dstExp valExp)).2.locals = t.locals) := by
    intro t ht _ c hc dstExp valExp hdst hvw
    refine ⟨WsSafe.store_word ht.memaddrs hvw (fun addr ha hdom => ?_), fun hn => ?_⟩
    · rw [hdst] at ha; injection ha with h1; injection h1 with h2; injection h2 with h3; subst h3
      exact ht.u256_ws_in_ivls hdom (off := off + c) (by omega) (hadd_assoc c (by omega))
    · rcases hr : evaluateHOLFiniteState t (.store dstExp valExp) with ⟨r, post⟩
      rw [hr] at hn; dsimp only at hn ⊢; subst hn
      exact (ByteRegionEffect.of_store_word ht.memaddrs hr hvw (fun addr ha hdom => by
        rw [hdst] at ha; injection ha with h1; injection h1 with h2; injection h2 with h3; subst h3
        exact ht.u256_ws_in_ivls hdom (off := off + c) (by omega) (hadd_assoc c (by omega)))).2
  have hws : WsSafe s (untypedGlobalBufIvls s0)
      (evaluateHOLFiniteState s (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_u256_to_digits).body)) := by
    dsimp only [extractFn, Guest.Software.guestFn_u256_to_digits,
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural, List.map]
    have hp_step1 : ∀ {t : PanSemStateFiniteExact 64 F} (ht : WsEnv s0 t)
        (hpt : t.locals.lookup (ofString "p") = some (.val (.word pbase)))
        (valExp : ExpHOL 64)
        (hvw : ∀ vv, @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) valExp =
          some vv → ∃ w : BitVec 64, vv = .val (.word w))
        {rest : ProgHOL 64}
        (hnext : ∀ {t' : PanSemStateFiniteExact 64 F}, WsEnv s0 t' →
          t'.locals.lookup (ofString "p") = some (.val (.word pbase)) →
          WsSafe t' (untypedGlobalBufIvls s0) (evaluateHOLFiniteState t' rest)),
        WsSafe t (untypedGlobalBufIvls s0)
          (evaluateHOLFiniteState t (.seq (.store (.var .local (ofString "p")) valExp) rest)) := by
      intro t ht hpt valExp hvw rest hnext
      have hs := hstep_ws ht hpt 0 (by omega) (.var .local (ofString "p")) valExp
        (by simp [evalHOLExact, hpt, pbase]) hvw
      exact WsSafe.seq hs.1 (fun hn heff => hnext (ht.step heff) (by rw [hs.2 hn]; exact hpt))
    have hp_stepc : ∀ {t : PanSemStateFiniteExact 64 F} (ht : WsEnv s0 t)
        (hpt : t.locals.lookup (ofString "p") = some (.val (.word pbase)))
        (c : Nat) (hc : c ≤ 56) (valExp : ExpHOL 64)
        (hvw : ∀ vv, @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) valExp =
          some vv → ∃ w : BitVec 64, vv = .val (.word w))
        {rest : ProgHOL 64}
        (hnext : ∀ {t' : PanSemStateFiniteExact 64 F}, WsEnv s0 t' →
          t'.locals.lookup (ofString "p") = some (.val (.word pbase)) →
          WsSafe t' (untypedGlobalBufIvls s0) (evaluateHOLFiniteState t' rest)),
        WsSafe t (untypedGlobalBufIvls s0)
          (evaluateHOLFiniteState t (.seq (.store (.op .add [.var .local (ofString "p"), .const (BitVec.ofNat 64 c)]) valExp) rest)) := by
      intro t ht hpt c hc valExp hvw rest hnext
      have hs := hstep_ws ht hpt c hc (.op .add [.var .local (ofString "p"), .const (BitVec.ofNat 64 c)]) valExp
        (by simp [evalHOLExact, evalListHOLExact, hpt, wordOpHOL, wordOp, valueIsWord, valueWord, pbase]) hvw
      exact WsSafe.seq hs.1 (fun hn heff => hnext (ht.step heff) (by rw [hs.2 hn]; exact hpt))
    exact hp_step1 he hp _ (fun _ hv => eval_word_of_op hv) fun ht1 hp1 =>
      hp_stepc ht1 hp1 8 (by omega) _ (fun _ hv => eval_word_of_shift hv) fun ht2 hp2 =>
      hp_stepc ht2 hp2 16 (by omega) _ (fun _ hv => eval_word_of_op hv) fun ht3 hp3 =>
      hp_stepc ht3 hp3 24 (by omega) _ (fun _ hv => eval_word_of_shift hv) fun ht4 hp4 =>
      hp_stepc ht4 hp4 32 (by omega) _ (fun _ hv => eval_word_of_op hv) fun ht5 hp5 =>
      hp_stepc ht5 hp5 40 (by omega) _ (fun _ hv => eval_word_of_shift hv) fun ht6 hp6 =>
      hp_stepc ht6 hp6 48 (by omega) _ (fun _ hv => eval_word_of_op hv) fun ht7 hp7 =>
      hp_stepc ht7 hp7 56 (by omega) _ (fun _ hv => eval_word_of_shift hv) fun _ _ =>
      WsSafe.return_exp _ _ _
  refine ⟨hws, ?_⟩
  intro v cpost hret hnz
  have hseq_ret : ∀ {p1 p2 : ProgHOL 64} {st : PanSemStateFiniteExact 64 F} {dst val : ExpHOL 64},
      p1 = .store dst val →
      evaluateHOLFiniteState st (.seq p1 p2) = (some (.returned v), cpost) →
      ∃ st1, evaluateHOLFiniteState st p1 = (none, st1) ∧
        evaluateHOLFiniteState st1 p2 = (some (.returned v), cpost) := by
    intro p1 p2 st dst val hp1 hr
    subst hp1
    rw [evaluateHOLFiniteState_seq_line780] at hr
    rcases hr1 : evaluateHOLFiniteState st (.store dst val) with ⟨r1, st1⟩
    rw [hr1] at hr
    cases r1 with
    | none => exact ⟨st1, rfl, hr⟩
    | some r0 =>
      have hcf := (evaluate_store_control_frame st dst val).1
      rw [hr1] at hcf; dsimp only at hcf hr
      rcases hcf with h | h
      · cases h
      · injection h with h'; subst h'; simp at hr
  obtain ⟨s1, hr1, hret⟩ := hseq_ret rfl hret
  obtain ⟨s2, hr2, hret⟩ := hseq_ret rfl hret
  obtain ⟨s3, hr3, hret⟩ := hseq_ret rfl hret
  obtain ⟨s4, hr4, hret⟩ := hseq_ret rfl hret
  obtain ⟨s5, hr5, hret⟩ := hseq_ret rfl hret
  obtain ⟨s6, hr6, hret⟩ := hseq_ret rfl hret
  obtain ⟨s7, hr7, hret⟩ := hseq_ret rfl hret
  obtain ⟨s8, hr8, hret⟩ := hseq_ret rfl hret
  have hm_ret : cpost.memory = s8.memory := by
    rw [evaluateHOLFiniteState_return] at hret
    dsimp only [evalHOLExact] at hret
    split at hret
    · injection hret with _ hpst; subst hpst; rfl
    · simp at hret
  have ⟨he1, hl1, hm1_same, hm1_ne⟩ := single_word_store_eff_mem he (off := off + 0)
    (w := a0 &&& 4294967295#64)
    (by rw [← hadd_assoc 0 (by omega)]; simp [evalHOLExact, hp, pbase])
    (by simp [evalHOLExact, evalListHOLExact, ha, wordOpHOL, wordOp, valueIsWord, valueWord,
          show (4294967295#64 &&& 18446744073709551615#64) = 4294967295#64 by decide]; rfl)
    (by omega) hr1
  have hp1 : s1.locals.lookup (ofString "p") = some (.val (.word pbase)) := by rw [hl1]; exact hp
  have ha1 : s1.locals.lookup (ofString "a") = some (.rStruct [.val (.word a0), .val (.word a1), .val (.word a2), .val (.word a3)]) := by rw [hl1]; exact ha
  have ⟨he2, hl2, hm2_same, hm2_ne⟩ := single_word_store_eff_mem (he.step he1) (off := off + 8)
    (w := a0 >>> 32)
    (by rw [← hadd_assoc 8 (by omega)]; simp [evalHOLExact, evalListHOLExact, hp1, pbase, wordOpHOL, wordOp, valueIsWord, valueWord])
    (by simp [evalHOLExact, ha1, wordShiftHOL])
    (by omega) hr2
  have hp2 : s2.locals.lookup (ofString "p") = some (.val (.word pbase)) := by rw [hl2]; exact hp1
  have ha2 : s2.locals.lookup (ofString "a") = some (.rStruct [.val (.word a0), .val (.word a1), .val (.word a2), .val (.word a3)]) := by rw [hl2]; exact ha1
  have ⟨he3, hl3, hm3_same, hm3_ne⟩ := single_word_store_eff_mem ((he.step he1).step he2) (off := off + 16)
    (w := a1 &&& 4294967295#64)
    (by rw [← hadd_assoc 16 (by omega)]; simp [evalHOLExact, evalListHOLExact, hp2, pbase, wordOpHOL, wordOp, valueIsWord, valueWord])
    (by simp [evalHOLExact, evalListHOLExact, ha2, wordOpHOL, wordOp, valueIsWord, valueWord,
          show (4294967295#64 &&& 18446744073709551615#64) = 4294967295#64 by decide]; rfl)
    (by omega) hr3
  have hp3 : s3.locals.lookup (ofString "p") = some (.val (.word pbase)) := by rw [hl3]; exact hp2
  have ha3 : s3.locals.lookup (ofString "a") = some (.rStruct [.val (.word a0), .val (.word a1), .val (.word a2), .val (.word a3)]) := by rw [hl3]; exact ha2
  have ⟨he4, hl4, hm4_same, hm4_ne⟩ := single_word_store_eff_mem (((he.step he1).step he2).step he3) (off := off + 24)
    (w := a1 >>> 32)
    (by rw [← hadd_assoc 24 (by omega)]; simp [evalHOLExact, evalListHOLExact, hp3, pbase, wordOpHOL, wordOp, valueIsWord, valueWord])
    (by simp [evalHOLExact, ha3, wordShiftHOL])
    (by omega) hr4
  have hp4 : s4.locals.lookup (ofString "p") = some (.val (.word pbase)) := by rw [hl4]; exact hp3
  have ha4 : s4.locals.lookup (ofString "a") = some (.rStruct [.val (.word a0), .val (.word a1), .val (.word a2), .val (.word a3)]) := by rw [hl4]; exact ha3
  have ⟨he5, hl5, hm5_same, hm5_ne⟩ := single_word_store_eff_mem ((((he.step he1).step he2).step he3).step he4) (off := off + 32)
    (w := a2 &&& 4294967295#64)
    (by rw [← hadd_assoc 32 (by omega)]; simp [evalHOLExact, evalListHOLExact, hp4, pbase, wordOpHOL, wordOp, valueIsWord, valueWord])
    (by simp [evalHOLExact, evalListHOLExact, ha4, wordOpHOL, wordOp, valueIsWord, valueWord,
          show (4294967295#64 &&& 18446744073709551615#64) = 4294967295#64 by decide]; rfl)
    (by omega) hr5
  have hp5 : s5.locals.lookup (ofString "p") = some (.val (.word pbase)) := by rw [hl5]; exact hp4
  have ha5 : s5.locals.lookup (ofString "a") = some (.rStruct [.val (.word a0), .val (.word a1), .val (.word a2), .val (.word a3)]) := by rw [hl5]; exact ha4
  have ⟨he6, hl6, hm6_same, hm6_ne⟩ := single_word_store_eff_mem (((((he.step he1).step he2).step he3).step he4).step he5) (off := off + 40)
    (w := a2 >>> 32)
    (by rw [← hadd_assoc 40 (by omega)]; simp [evalHOLExact, evalListHOLExact, hp5, pbase, wordOpHOL, wordOp, valueIsWord, valueWord])
    (by simp [evalHOLExact, ha5, wordShiftHOL])
    (by omega) hr6
  have hp6 : s6.locals.lookup (ofString "p") = some (.val (.word pbase)) := by rw [hl6]; exact hp5
  have ha6 : s6.locals.lookup (ofString "a") = some (.rStruct [.val (.word a0), .val (.word a1), .val (.word a2), .val (.word a3)]) := by rw [hl6]; exact ha5
  have ⟨he7, hl7, hm7_same, hm7_ne⟩ := single_word_store_eff_mem ((((((he.step he1).step he2).step he3).step he4).step he5).step he6) (off := off + 48)
    (w := a3 &&& 4294967295#64)
    (by rw [← hadd_assoc 48 (by omega)]; simp [evalHOLExact, evalListHOLExact, hp6, pbase, wordOpHOL, wordOp, valueIsWord, valueWord])
    (by simp [evalHOLExact, evalListHOLExact, ha6, wordOpHOL, wordOp, valueIsWord, valueWord,
          show (4294967295#64 &&& 18446744073709551615#64) = 4294967295#64 by decide]; rfl)
    (by omega) hr7
  have hp7 : s7.locals.lookup (ofString "p") = some (.val (.word pbase)) := by rw [hl7]; exact hp6
  have ha7 : s7.locals.lookup (ofString "a") = some (.rStruct [.val (.word a0), .val (.word a1), .val (.word a2), .val (.word a3)]) := by rw [hl7]; exact ha6
  have ⟨_, _, hm8_same, hm8_ne⟩ := single_word_store_eff_mem (((((((he.step he1).step he2).step he3).step he4).step he5).step he6).step he7) (off := off + 56)
    (w := a3 >>> 32)
    (by rw [← hadd_assoc 56 (by omega)]; simp [evalHOLExact, evalListHOLExact, hp7, pbase, wordOpHOL, wordOp, valueIsWord, valueWord])
    (by simp [evalHOLExact, ha7, wordShiftHOL])
    (by omega) hr8
  have hne_off : ∀ c1 c2 : Nat, c1 < 64 → c2 < 64 → c1 ≠ c2 →
      BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 (off + c1) ≠
      BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 (off + c2) := by
    intro c1 c2 hc1 hc2 hne heq
    have := congrArg BitVec.toNat heq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show off + c1 < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show off + c2 < 2 ^ 64 by omega)] at this
    have hb := he.ws_bnd
    have hlt1 : (globN s0 "u256_ws") % 2 ^ 64 = globN s0 "u256_ws" := Nat.mod_eq_of_lt (by omega)
    rw [hlt1] at this
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    omega
  have hlimb_nz : ∀ w : BitVec 64, w ≠ 0 → (w &&& 4294967295#64) ≠ 0 ∨ (w >>> 32) ≠ 0 := by
    intro w hw
    by_cases h1 : (w &&& 4294967295#64) = 0
    · right
      intro h2
      apply hw
      apply BitVec.eq_of_toNat_eq
      have hlo : (w &&& 4294967295#64).toNat = 0 := by rw [h1]; rfl
      have hhi : (w >>> (32 : Nat)).toNat = 0 := by exact congrArg BitVec.toNat h2
      rw [BitVec.toNat_and] at hlo
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at hhi
      have h42 : (4294967295#64).toNat = 2 ^ 32 - 1 := rfl
      rw [h42, Nat.and_two_pow_sub_one_eq_mod] at hlo
      have := w.isLt
      change w.toNat = 0
      omega
    · exact Or.inl h1
  have hor_nz : a0 ≠ 0 ∨ a1 ≠ 0 ∨ a2 ≠ 0 ∨ a3 ≠ 0 := by
    by_cases h0 : a0 = 0
    · by_cases h1 : a1 = 0
      · by_cases h2 : a2 = 0
        · by_cases h3 : a3 = 0
          · subst h0 h1 h2 h3; exact False.elim (hnz (by decide))
          · exact Or.inr (Or.inr (Or.inr h3))
        · exact Or.inr (Or.inr (Or.inl h2))
      · exact Or.inr (Or.inl h1)
    · exact Or.inl h0
  rw [hm_ret]
  rcases hor_nz with hz0 | hz1 | hz2 | hz3
  · rcases hlimb_nz a0 hz0 with h0 | h1
    · refine ⟨0, by omega, a0 &&& 4294967295#64, h0, ?_⟩
      change s8.memory (pbase + BitVec.ofNat 64 0) = _
      rw [hadd_assoc 0 (by omega),
          hm8_ne _ (hne_off 0 56 (by omega) (by omega) (by omega)),
          hm7_ne _ (hne_off 0 48 (by omega) (by omega) (by omega)),
          hm6_ne _ (hne_off 0 40 (by omega) (by omega) (by omega)),
          hm5_ne _ (hne_off 0 32 (by omega) (by omega) (by omega)),
          hm4_ne _ (hne_off 0 24 (by omega) (by omega) (by omega)),
          hm3_ne _ (hne_off 0 16 (by omega) (by omega) (by omega)),
          hm2_ne _ (hne_off 0 8 (by omega) (by omega) (by omega)),
          hm1_same]
    · refine ⟨1, by omega, a0 >>> 32, h1, ?_⟩
      change s8.memory (pbase + BitVec.ofNat 64 8) = _
      rw [hadd_assoc 8 (by omega),
          hm8_ne _ (hne_off 8 56 (by omega) (by omega) (by omega)),
          hm7_ne _ (hne_off 8 48 (by omega) (by omega) (by omega)),
          hm6_ne _ (hne_off 8 40 (by omega) (by omega) (by omega)),
          hm5_ne _ (hne_off 8 32 (by omega) (by omega) (by omega)),
          hm4_ne _ (hne_off 8 24 (by omega) (by omega) (by omega)),
          hm3_ne _ (hne_off 8 16 (by omega) (by omega) (by omega)),
          hm2_same]
  · rcases hlimb_nz a1 hz1 with h0 | h1
    · refine ⟨2, by omega, a1 &&& 4294967295#64, h0, ?_⟩
      change s8.memory (pbase + BitVec.ofNat 64 16) = _
      rw [hadd_assoc 16 (by omega),
          hm8_ne _ (hne_off 16 56 (by omega) (by omega) (by omega)),
          hm7_ne _ (hne_off 16 48 (by omega) (by omega) (by omega)),
          hm6_ne _ (hne_off 16 40 (by omega) (by omega) (by omega)),
          hm5_ne _ (hne_off 16 32 (by omega) (by omega) (by omega)),
          hm4_ne _ (hne_off 16 24 (by omega) (by omega) (by omega)),
          hm3_same]
    · refine ⟨3, by omega, a1 >>> 32, h1, ?_⟩
      change s8.memory (pbase + BitVec.ofNat 64 24) = _
      rw [hadd_assoc 24 (by omega),
          hm8_ne _ (hne_off 24 56 (by omega) (by omega) (by omega)),
          hm7_ne _ (hne_off 24 48 (by omega) (by omega) (by omega)),
          hm6_ne _ (hne_off 24 40 (by omega) (by omega) (by omega)),
          hm5_ne _ (hne_off 24 32 (by omega) (by omega) (by omega)),
          hm4_same]
  · rcases hlimb_nz a2 hz2 with h0 | h1
    · refine ⟨4, by omega, a2 &&& 4294967295#64, h0, ?_⟩
      change s8.memory (pbase + BitVec.ofNat 64 32) = _
      rw [hadd_assoc 32 (by omega),
          hm8_ne _ (hne_off 32 56 (by omega) (by omega) (by omega)),
          hm7_ne _ (hne_off 32 48 (by omega) (by omega) (by omega)),
          hm6_ne _ (hne_off 32 40 (by omega) (by omega) (by omega)),
          hm5_same]
    · refine ⟨5, by omega, a2 >>> 32, h1, ?_⟩
      change s8.memory (pbase + BitVec.ofNat 64 40) = _
      rw [hadd_assoc 40 (by omega),
          hm8_ne _ (hne_off 40 56 (by omega) (by omega) (by omega)),
          hm7_ne _ (hne_off 40 48 (by omega) (by omega) (by omega)),
          hm6_same]
  · rcases hlimb_nz a3 hz3 with h0 | h1
    · refine ⟨6, by omega, a3 &&& 4294967295#64, h0, ?_⟩
      change s8.memory (pbase + BitVec.ofNat 64 48) = _
      rw [hadd_assoc 48 (by omega),
          hm8_ne _ (hne_off 48 56 (by omega) (by omega) (by omega)),
          hm7_same]
    · refine ⟨7, by omega, a3 >>> 32, h1, ?_⟩
      change s8.memory (pbase + BitVec.ofNat 64 56) = _
      rw [hadd_assoc 56 (by omega), hm8_same]

private def digitsLenBody : ProgHOL 64 :=
  InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
    (extractFn Guest.Software.guestFn_digits_len).body

private def digitsLenLoop : ProgHOL 64 :=
  match digitsLenBody with
  | .seq loop _ => loop
  | _ => .skip

private def digitsLenStep : ProgHOL 64 :=
  match digitsLenLoop with
  | .while _ step => step
  | _ => .skip

private theorem locN_setVar_self_eq {F : Type} (s : PanSemStateFiniteExact 64 F) (x : String) (w : BitVec 64) :
    locN (setVarHOLFinite (ofString x) (.val (.word w)) s) x = w.toNat := by
  simp [locN, setVarHOLFinite, FUPDATE]

private theorem digitsLenStep_cases {F : Type} (s : PanSemStateFiniteExact 64 F) (w p : BitVec 64)
    (hn : s.locals.lookup (ofString "n") = some (.val (.word w)))
    (hp : s.locals.lookup (ofString "p") = some (.val (.word p))) :
    (s.memory (p + (w - 1#64) * 8#64) = .word 0#64 ∧
      evaluateHOLFiniteState s digitsLenStep = (none, setVarHOLFinite (ofString "n") (.val (.word (w - 1#64))) s)) ∨
    (∃ post, evaluateHOLFiniteState s digitsLenStep = (some (.returned (.val (.word w))), post)) ∨
    (∃ post, evaluateHOLFiniteState s digitsLenStep = (some .error, post)) := by
  have hstep : digitsLenStep = (ProgHOL.ite (.cmp .notEqual (.load .one (.op .add [.var .local (ofString "p"),
      .panop .mul [.op .sub [.var .local (ofString "n"), .const 1#64], .const 8#64]])) (.const 0#64))
      (.return (.var .local (ofString "n"))) .skip).seq
      (.assign .local (ofString "n") (.op .sub [.var .local (ofString "n"), .const 1#64])) := rfl
  rw [hstep, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
  let addrExp : ExpHOL 64 := .op .add [.var .local (ofString "p"),
    .panop .mul [.op .sub [.var .local (ofString "n"), .const 1#64], .const 8#64]]
  let addr := p + (w - 1#64) * 8#64
  have haddr_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      addrExp = some (.val (.word addr)) := by
    simp [addrExp, evalHOLExact, evalListHOLExact, hp, hn, wordOpHOL, wordOp, panOpHOL,
      valueIsWord, valueWord, addr]
  by_cases hdom : s.memaddrs addr
  · cases hmem : s.memory addr with
    | word mw =>
      by_cases hmw0 : mw = 0#64
      · subst hmw0
        have hcnd : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
            (.cmp .notEqual (.load .one addrExp) (.const 0#64)) = some (.val (.word 0#64)) := by
          simp [evalHOLExact, haddr_ev, memLoadHOLExact, hdom, hmem, wordCmpHOL]
        rw [show @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
          (.cmp .notEqual (.load .one addrExp) (.const 0#64)) = some (.val (.word 0#64)) from hcnd]
        dsimp only
        rw [if_pos (show (0#64 : BitVec 64) = 0 by decide), evaluateHOLFiniteState_skip]; dsimp only
        left
        refine ⟨rfl, ?_⟩
        simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hn,
          wordOpHOL, wordOp, valueIsWord, valueWord, lookupKvarHOLExact, isValidValueHOLExact,
          setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL]
      · have hcnd : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
            (.cmp .notEqual (.load .one addrExp) (.const 0#64)) = some (.val (.word 1#64)) := by
          simp [evalHOLExact, haddr_ev, memLoadHOLExact, hdom, hmem, wordCmpHOL, hmw0]
        rw [show @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
          (.cmp .notEqual (.load .one addrExp) (.const 0#64)) = some (.val (.word 1#64)) from hcnd]
        dsimp only
        rw [if_neg (show (1#64 : BitVec 64) ≠ 0 by decide), evaluateHOLFiniteState_return]
        simp only [evalHOLExact, hn, shapeOfHOLExact, sizeOfShapeWithContextHOL,
          show (1 : Nat) ≤ 32 by decide, ↓reduceIte]
        exact Or.inr (Or.inl ⟨_, rfl⟩)
  · have hcnd : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .notEqual (.load .one addrExp) (.const 0#64)) = none := by
      dsimp only [evalHOLExact]; rw [haddr_ev]; simp [memLoadHOLExact, hdom]
    rw [show @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .notEqual (.load .one addrExp) (.const 0#64)) = none from hcnd]
    exact Or.inr (Or.inr ⟨_, rfl⟩)

private theorem digitsLenLoop_post :
    ∀ (fuel : Nat) {F : Type} (s post : PanSemStateFiniteExact 64 F) (p : BitVec 64) (N : Nat)
      (res : Option (PanSemResultExact 64)),
      fuel = locN s "n" →
      locN s "n" ≤ N →
      s.locals.lookup (ofString "p") = some (.val (.word p)) →
      evaluateHOLFiniteState s digitsLenLoop = (res, post) →
      (res = none → post.memory = s.memory ∧ ∀ j : Nat, j < locN s "n" →
        s.memory (p + BitVec.ofNat 64 j * 8#64) = .word 0#64) ∧
      (∀ v, res = some (.returned v) →
        ∃ w : BitVec 64, v = .val (.word w) ∧ 1 ≤ w.toNat ∧ w.toNat ≤ N ∧
          (∀ j : Nat, w.toNat ≤ j → j < locN s "n" →
            s.memory (p + BitVec.ofNat 64 j * 8#64) = .word 0#64)) := by
  intro fuel
  induction fuel with
  | zero =>
    intro F s post p N res hfuel _ hp hrun
    have hloop : digitsLenLoop = .while (.cmp .lower (.const 0#64) (.var .local (ofString "n"))) digitsLenStep := rfl
    rw [hloop, evaluateHOLFiniteState_while_fixClockRewrite] at hrun
    cases hn : s.locals.lookup (ofString "n") with
    | none =>
      simp [evalHOLFinite, evalHOLExact, hn] at hrun
      rcases hrun with ⟨rfl, rfl⟩
      constructor
      · intro h; cases h
      · intro _ h; cases h
    | some val =>
      cases val with
      | rStruct _ =>
        simp [evalHOLFinite, evalHOLExact, hn] at hrun
        rcases hrun with ⟨rfl, rfl⟩
        constructor
        · intro h; cases h
        · intro _ h; cases h
      | nStruct _ _ =>
        simp [evalHOLFinite, evalHOLExact, hn] at hrun
        rcases hrun with ⟨rfl, rfl⟩
        constructor
        · intro h; cases h
        · intro _ h; cases h
      | val wv =>
        cases wv with
        | word w =>
          have hw0 : w = 0#64 := by
            simp [locN, hn] at hfuel
            exact BitVec.eq_of_toNat_eq (by simpa using hfuel.symm)
          subst hw0
          simp [evalHOLFinite, evalHOLExact, hn, Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hrun
          rcases hrun with ⟨rfl, rfl⟩
          constructor
          · intro _; exact ⟨rfl, fun j hj => by simp [locN, hn] at hj⟩
          · intro _ h; cases h
  | succ k ih =>
    intro F s post p N res hfuel hle hp hrun
    have hloop : digitsLenLoop = .while (.cmp .lower (.const 0#64) (.var .local (ofString "n"))) digitsLenStep := rfl
    rw [hloop, evaluateHOLFiniteState_while_fixClockRewrite] at hrun
    cases hn : s.locals.lookup (ofString "n") with
    | none => simp [locN, hn] at hfuel
    | some val =>
      cases val with
      | rStruct _ => simp [locN, hn] at hfuel
      | nStruct _ _ => simp [locN, hn] at hfuel
      | val wv =>
        cases wv with
        | word w =>
          have hw_eq : w.toNat = k + 1 := by simpa [locN, hn] using hfuel.symm
          have hcmp : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
              (.cmp .lower (.const 0#64) (.var .local (ofString "n"))) = some (.val (.word 1#64)) := by
            simp only [evalHOLFinite, evalHOLExact, hn, Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
              BitVec.lt_def, BitVec.toNat_ofNat, Nat.zero_mod, decide_eq_true_eq]
            rw [if_pos (by omega)]
            rfl
          rw [hcmp] at hrun; dsimp only at hrun
          rw [if_pos (show (1#64 : BitVec 64) ≠ 0 by decide)] at hrun
          by_cases hclk : s.clock = 0
          · rw [if_pos hclk] at hrun
            injection hrun with hres _; subst hres
            constructor
            · intro h; cases h
            · intro _ h; cases h
          · rw [if_neg hclk] at hrun
            have hn_dec : (decClockHOLFinite s).locals.lookup (ofString "n") = some (.val (.word w)) := hn
            have hp_dec : (decClockHOLFinite s).locals.lookup (ofString "p") = some (.val (.word p)) := hp
            rcases digitsLenStep_cases (decClockHOLFinite s) w p hn_dec hp_dec with
              ⟨hmemk, hnext⟩ | ⟨_, hret⟩ | ⟨_, herr⟩
            · rw [hnext] at hrun; dsimp only at hrun
              rw [← hloop] at hrun
              let s' := setVarHOLFinite (ofString "n") (.val (.word (w - 1#64))) (decClockHOLFinite s)
              have hw1 : w - 1#64 = BitVec.ofNat 64 k := by
                apply BitVec.eq_of_toNat_eq
                rw [BitVec.toNat_sub, BitVec.toNat_ofNat]
                have := w.isLt
                change (18446744073709551615 + w.toNat) % 18446744073709551616 = k % 18446744073709551616
                omega
              have hloc' : locN s' "n" = k := by
                dsimp only [s']
                rw [locN_setVar_self_eq, hw1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := w.isLt; omega)]
              have hp' : s'.locals.lookup (ofString "p") = some (.val (.word p)) := by
                dsimp only [s']
                have hnp : ofString "n" ≠ ofString "p" := by decide
                simp [setVarHOLFinite, FUPDATE, hnp, hp_dec]
              have hmem_s' : s'.memory = s.memory := rfl
              have hmemk_s : s.memory (p + BitVec.ofNat 64 k * 8#64) = .word 0#64 := by
                rw [← hw1]; exact hmemk
              obtain ⟨ih_none, ih_ret⟩ := ih s' post p N res hloc'.symm (by omega) hp' hrun
              refine ⟨fun hres => ?_, fun v hv => ?_⟩
              · obtain ⟨hm_eq, hall⟩ := ih_none hres
                refine ⟨hm_eq.trans hmem_s', fun j hj => ?_⟩
                rw [← hfuel] at hj
                by_cases hjk : j = k
                · subst hjk; exact hmemk_s
                · have hlt : j < locN s' "n" := by omega
                  rw [← hmem_s']; exact hall j hlt
              · obtain ⟨wr, hvr, h1, h2, hall⟩ := ih_ret v hv
                refine ⟨wr, hvr, h1, h2, fun j hj1 hj2 => ?_⟩
                rw [← hfuel] at hj2
                by_cases hjk : j = k
                · subst hjk; exact hmemk_s
                · have hlt : j < locN s' "n" := by omega
                  rw [← hmem_s']; exact hall j hj1 hlt
            · rw [hret] at hrun; dsimp only at hrun
              injection hrun with hres hpost; subst hres hpost
              constructor
              · intro h; cases h
              · intro v hv
                injection hv with hv'; injection hv' with hv''
                exact ⟨w, hv''.symm, by omega, by omega, fun j hj1 hj2 => by rw [← hfuel] at hj2; omega⟩
            · rw [herr] at hrun; dsimp only at hrun
              injection hrun with hres _; subst hres
              constructor
              · intro h; cases h
              · intro _ hv; cases hv

theorem digits_len_wsSafe_and_post {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    (he : WsEnv s0 s) {p : BitVec 64} {n : BitVec 64} {N : Nat}
    (hp : s.locals.lookup (ofString "p") = some (.val (.word p)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (hle : n.toNat ≤ N) :
    WsSafe s (untypedGlobalBufIvls s0) (evaluateHOLFiniteState s digitsLenBody) ∧
    (∀ v cpost, evaluateHOLFiniteState s digitsLenBody = (some (.returned v), cpost) →
      ∃ w : BitVec 64, v = .val (.word w) ∧ w.toNat ≤ N ∧
        ((∃ k : Nat, k < n.toNat ∧ ∃ wk : BitVec 64, wk ≠ 0 ∧
            s.memory (p + BitVec.ofNat 64 (8 * k)) = .word wk) →
          1 ≤ w.toNat)) := by
  have hro : readOnlyProg opRoCallees digitsLenBody = true := by decide
  have hws : WsSafe s (untypedGlobalBufIvls s0) (evaluateHOLFiniteState s digitsLenBody) :=
    WsSafe.of_readOnly he.code hro
  refine ⟨hws, ?_⟩
  intro v cpost hrun
  have hseq : digitsLenBody = .seq digitsLenLoop (.return (.const 0#64)) := rfl
  rw [hseq, evaluateHOLFiniteState_seq_line780] at hrun
  rcases hw : evaluateHOLFiniteState s digitsLenLoop with ⟨res, mid⟩
  rw [hw] at hrun
  have hloc_n : locN s "n" = n.toNat := by simp [locN, hn]
  obtain ⟨hnone, hret⟩ := digitsLenLoop_post (locN s "n") s mid p N res rfl (by omega) hp hw
  have hmul8 : ∀ k : Nat, BitVec.ofNat 64 k * 8#64 = BitVec.ofNat 64 (8 * k) := by
    intro k
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mul_comm]
  cases res with
  | none =>
    dsimp only at hrun
    rw [evaluateHOLFiniteState_return] at hrun
    simp only [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL,
      show (1 : Nat) ≤ 32 by decide, ↓reduceIte, Prod.mk.injEq, Option.some.injEq,
      PanSemResultExact.returned.injEq] at hrun
    rcases hrun with ⟨hv, _⟩
    refine ⟨0#64, hv.symm, Nat.zero_le _, ?_⟩
    rintro ⟨k, hk, wk, hwk, hmemk⟩
    have hz := (hnone rfl).2 k (by omega)
    rw [hmul8 k, hmemk] at hz
    injection hz with hz'
    exact False.elim (hwk hz')
  | some r =>
    dsimp only at hrun
    injection hrun with hr hmid; subst hmid
    injection hr with hr'; subst hr'
    obtain ⟨w, hvw, h1, h2, _⟩ := hret v rfl
    exact ⟨w, hvw, h2, fun _ => h1⟩

/-! ## 5. Reusable loop/store/call lemmas and `divmnu_wsSafe` -/

def isWordValExp : ExpHOL 64 → Bool
  | .const _ => true
  | .load .one _ => true
  | .op _ _ => true
  | .panop _ _ => true
  | .shift _ _ _ => true
  | .cmp _ _ _ => true
  | _ => false

theorem eval_word_of_isWordValExp {F : Type} {s : PanSemStateFiniteExact 64 F}
    {e : ExpHOL 64} (hw : isWordValExp e = true) {v : ValueHOL 64}
    (hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e = some v) :
    ∃ w : BitVec 64, v = .val (.word w) := by
  cases e <;> simp [isWordValExp] at hw
  case const k =>
    exact eval_word_of_const hev
  case load sh addr =>
    cases sh <;> simp [isWordValExp] at hw
    simp only [evalHOLExact] at hev
    split at hev
    · split at hev
      · rename_i aw _
        simp only [memLoadHOLExact] at hev
        split at hev
        · injection hev with hv
          cases hmem : s.memory aw with
          | word w => rw [hmem] at hv; exact ⟨w, hv.symm⟩
        · simp at hev
      · simp at hev
    · simp at hev
  case op bop es =>
    exact eval_word_of_op hev
  case panop pop es =>
    simp only [evalHOLExact, panOpHOL] at hev
    split at hev
    · split at hev
      · simp only [Option.map] at hev
        split at hev
        · rename_i w _; injection hev with hv'; exact ⟨w, hv'.symm⟩
        · simp at hev
      · simp at hev
    · simp at hev
  case shift sh e1 e2 =>
    exact eval_word_of_shift hev
  case cmp c e1 e2 =>
    simp only [evalHOLExact] at hev
    split at hev
    · injection hev with hv; exact ⟨_, hv.symm⟩
    · simp at hev

theorem eval_word_of_local {F : Type} {s : PanSemStateFiniteExact 64 F}
    {nm : MlS} {w : BitVec 64}
    (hl : s.locals.lookup nm = some (.val (.word w)))
    {v : ValueHOL 64}
    (hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.var .local nm) = some v) :
    v = .val (.word w) := by
  simp [evalHOLExact, hl] at hev
  exact hev.symm

theorem eval_word_of_rfield_comb2 {F : Type} {s : PanSemStateFiniteExact 64 F}
    {idx : Nat} {nm : MlS} {w0 w1 : BitVec 64}
    (hl : s.locals.lookup nm = some (.rStruct [.val (.word w0), .val (.word w1)]))
    {v : ValueHOL 64}
    (hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.rfield idx (.var .local nm)) = some v) :
    ∃ w : BitVec 64, v = .val (.word w) := by
  simp only [evalHOLExact, hl] at hev
  rcases idx with _ | _ | _
  · simp at hev; exact ⟨w0, hev.symm⟩
  · simp at hev; exact ⟨w1, hev.symm⟩
  · simp at hev

theorem eval_comb2_of_shape {v : ValueHOL 64}
    (h : shapeEqHOL (.comb [.one, .one]) (shapeOfHOLExact v) = true ∨
         shapeEqHOL (shapeOfHOLExact v) (.comb [.one, .one]) = true) :
    ∃ w0 w1 : BitVec 64, v = .rStruct [.val (.word w0), .val (.word w1)] := by
  have hsh : shapeOfHOLExact v = .comb [.one, .one] := by
    rcases h with hh | hh
    · exact ((shapeEqHOL_eq_true _ _).1 hh).symm
    · exact (shapeEqHOL_eq_true _ _).1 hh
  rcases v with _ | fs | _
  · simp [shapeOfHOLExact] at hsh
  · simp only [shapeOfHOLExact, ShapeHOL.comb.injEq] at hsh
    rcases fs with _ | ⟨f0, _ | ⟨f1, _ | _⟩⟩
    · simp at hsh
    · simp at hsh
    · simp only [List.map, List.cons.injEq] at hsh
      obtain ⟨h0, h1, _⟩ := hsh
      rcases f0 with ⟨⟨w0⟩⟩ | _ | _ <;> simp [shapeOfHOLExact] at h0
      rcases f1 with ⟨⟨w1⟩⟩ | _ | _ <;> simp [shapeOfHOLExact] at h1
      exact ⟨w0, w1, rfl⟩
    · simp at hsh
  · simp [shapeOfHOLExact] at hsh

theorem eval_comb5_of_shape {v : ValueHOL 64}
    (h : shapeEqHOL (.comb [.one, .one, .one, .one, .one]) (shapeOfHOLExact v) = true ∨
         shapeEqHOL (shapeOfHOLExact v) (.comb [.one, .one, .one, .one, .one]) = true) :
    ∃ w0 w1 w2 w3 w4 : BitVec 64,
      v = .rStruct [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3), .val (.word w4)] := by
  have hsh : shapeOfHOLExact v = .comb [.one, .one, .one, .one, .one] := by
    rcases h with hh | hh
    · exact ((shapeEqHOL_eq_true _ _).1 hh).symm
    · exact (shapeEqHOL_eq_true _ _).1 hh
  rcases v with _ | fs | _
  · simp [shapeOfHOLExact] at hsh
  · simp only [shapeOfHOLExact, ShapeHOL.comb.injEq] at hsh
    rcases fs with _ | ⟨f0, _ | ⟨f1, _ | ⟨f2, _ | ⟨f3, _ | ⟨f4, _ | _⟩⟩⟩⟩⟩
    · simp at hsh
    · simp at hsh
    · simp at hsh
    · simp at hsh
    · simp at hsh
    · simp only [List.map, List.cons.injEq] at hsh
      obtain ⟨h0, h1, h2, h3, h4, _⟩ := hsh
      rcases f0 with ⟨⟨w0⟩⟩ | _ | _ <;> simp [shapeOfHOLExact] at h0
      rcases f1 with ⟨⟨w1⟩⟩ | _ | _ <;> simp [shapeOfHOLExact] at h1
      rcases f2 with ⟨⟨w2⟩⟩ | _ | _ <;> simp [shapeOfHOLExact] at h2
      rcases f3 with ⟨⟨w3⟩⟩ | _ | _ <;> simp [shapeOfHOLExact] at h3
      rcases f4 with ⟨⟨w4⟩⟩ | _ | _ <;> simp [shapeOfHOLExact] at h4
      exact ⟨w0, w1, w2, w3, w4, rfl⟩
    · simp at hsh
  · simp [shapeOfHOLExact] at hsh

theorem eval_comb8_of_shape {v : ValueHOL 64}
    (h : shapeEqHOL (.comb [.one, .one, .one, .one, .one, .one, .one, .one]) (shapeOfHOLExact v) = true ∨
         shapeEqHOL (shapeOfHOLExact v) (.comb [.one, .one, .one, .one, .one, .one, .one, .one]) = true) :
    ∃ w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 64,
      v = .rStruct [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3),
                    .val (.word w4), .val (.word w5), .val (.word w6), .val (.word w7)] := by
  have hsh : shapeOfHOLExact v = .comb [.one, .one, .one, .one, .one, .one, .one, .one] := by
    rcases h with hh | hh
    · exact ((shapeEqHOL_eq_true _ _).1 hh).symm
    · exact (shapeEqHOL_eq_true _ _).1 hh
  rcases v with _ | fs | _
  · simp [shapeOfHOLExact] at hsh
  · simp only [shapeOfHOLExact, ShapeHOL.comb.injEq] at hsh
    rcases fs with _ | ⟨f0, _ | ⟨f1, _ | ⟨f2, _ | ⟨f3, _ | ⟨f4, _ | ⟨f5, _ | ⟨f6, _ | ⟨f7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩
    · simp at hsh
    · simp at hsh
    · simp at hsh
    · simp at hsh
    · simp at hsh
    · simp at hsh
    · simp at hsh
    · simp at hsh
    · simp only [List.map, List.cons.injEq] at hsh
      obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, _⟩ := hsh
      rcases f0 with ⟨⟨w0⟩⟩ | _ | _ <;> simp [shapeOfHOLExact] at h0
      rcases f1 with ⟨⟨w1⟩⟩ | _ | _ <;> simp [shapeOfHOLExact] at h1
      rcases f2 with ⟨⟨w2⟩⟩ | _ | _ <;> simp [shapeOfHOLExact] at h2
      rcases f3 with ⟨⟨w3⟩⟩ | _ | _ <;> simp [shapeOfHOLExact] at h3
      rcases f4 with ⟨⟨w4⟩⟩ | _ | _ <;> simp [shapeOfHOLExact] at h4
      rcases f5 with ⟨⟨w5⟩⟩ | _ | _ <;> simp [shapeOfHOLExact] at h5
      rcases f6 with ⟨⟨w6⟩⟩ | _ | _ <;> simp [shapeOfHOLExact] at h6
      rcases f7 with ⟨⟨w7⟩⟩ | _ | _ <;> simp [shapeOfHOLExact] at h7
      exact ⟨w0, w1, w2, w3, w4, w5, w6, w7, rfl⟩
    · simp at hsh
  · simp [shapeOfHOLExact] at hsh

theorem WsSafe.decCall_ro {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    (he : WsEnv s0 s) {nm : MlS} {sh : ShapeHOL} {fname : MlS}
    {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (hfn : opRoCallees fname = true)
    (hcont : ∀ (v : ValueHOL 64) (cpost : PanSemStateFiniteExact 64 F),
      WsEnv s0 (setVarHOLFinite nm v { cpost with locals := s.locals }) →
      shapeEqHOL (shapeOfHOLExact v) sh = true →
      (setVarHOLFinite nm v { cpost with locals := s.locals }).locals =
        (setVarHOLFinite nm v s).locals →
      WsSafe (setVarHOLFinite nm v { cpost with locals := s.locals }) (untypedGlobalBufIvls s0)
        (evaluateHOLFiniteState (setVarHOLFinite nm v { cpost with locals := s.locals }) cont)) :
    WsSafe s (untypedGlobalBufIvls s0)
      (evaluateHOLFiniteState s (.decCall nm sh fname args cont)) := by
  refine WsSafe.decCall ?_ ?_
  · intro vals body callee rs _ hl _
    have hl' : lookupCodeHOLFinite originalRuntimeCode.lookup fname vals = some (body, callee, rs) := by
      rwa [← he.code]
    have hbody := opRoCallees_good fname hfn vals body callee rs hl'
    exact WsSafe.of_readOnly he.code hbody
  · intro vals body callee rs v cpost _ _ _ _ he_cp hsh1 _
    let nextSt : PanSemStateFiniteExact 64 F :=
      setVarHOLFinite nm v { cpost with locals := s.locals }
    have he_next : WsEnv s0 nextSt :=
      ⟨he_cp.code.trans he.code, he_cp.memaddrs.trans he.memaddrs,
       he_cp.globals.trans he.globals, he.ws_bnd⟩
    exact hcont v cpost he_next hsh1 rfl

theorem WsSafe.store_ws_scaled {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    (he : WsEnv s0 s) {baseExp idxExp valExp : ExpHOL 64} {off idx : Nat}
    (hbase : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) baseExp =
      some (.val (.word (BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 off))))
    (hidx : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) idxExp =
      some (.val (.word (BitVec.ofNat 64 idx))))
    (hoff : off + idx * 8 + 8 ≤ 640)
    (hval : ∀ v : ValueHOL 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) valExp = some v →
      ∃ w : BitVec 64, v = .val (.word w)) :
    WsSafe s (untypedGlobalBufIvls s0)
      (evaluateHOLFiniteState s
        (.store (.op .add [baseExp, .panop .mul [idxExp, .const 8#64]]) valExp)) := by
  refine WsSafe.store_word he.memaddrs hval ?_
  intro addr haddr hdom
  have hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [baseExp, .panop .mul [idxExp, .const 8#64]]) =
      some (.val (.word (BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 (off + idx * 8)))) := by
    simp only [evalHOLExact, evalListHOLExact, hbase, hidx, panOpHOL, wordOpHOL, wordOp,
      valueIsWord, valueWord, List.all, List.map, Bool.and_self, ↓reduceIte, Option.map, List.foldr]
    congr 3
    rw [show BitVec.ofNat 64 idx * 8#64 + 0 = BitVec.ofNat 64 idx * 8#64 from BitVec.add_zero _,
        BitVec.add_assoc]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
    omega
  rw [hdst] at haddr
  injection haddr with h1; injection h1 with h2; injection h2 with h3
  exact he.u256_ws_in_ivls hdom hoff h3.symm

theorem WsSafe.store_ws_const_off {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    (he : WsEnv s0 s) {dst valExp : ExpHOL 64} {off : Nat}
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dst =
      some (.val (.word (BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 off))))
    (hoff : off + 8 ≤ 640)
    (hval : ∀ v : ValueHOL 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) valExp = some v →
      ∃ w : BitVec 64, v = .val (.word w)) :
    WsSafe s (untypedGlobalBufIvls s0) (evaluateHOLFiniteState s (.store dst valExp)) := by
  refine WsSafe.store_word he.memaddrs hval ?_
  intro addr haddr hdom
  rw [hdst] at haddr
  injection haddr with h1; injection h1 with h2; injection h2 with h3
  exact he.u256_ws_in_ivls hdom hoff h3.symm

abbrev restoreLocal {F : Type} (nm : MlS) (old : Option (ValueHOL 64))
    (sp : PanSemStateFiniteExact 64 F) : PanSemStateFiniteExact 64 F :=
  { sp with locals := sp.locals.resVarEq (nm, old) }

theorem WsSafe.decCall_ro_post {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    {Q : PanSemStateFiniteExact 64 F → Prop}
    (he : WsEnv s0 s) {nm : MlS} {sh : ShapeHOL} {fname : MlS}
    {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (hfn : opRoCallees fname = true)
    (hcont : ∀ (v : ValueHOL 64) (cpost : PanSemStateFiniteExact 64 F),
      WsEnv s0 (setVarHOLFinite nm v { cpost with locals := s.locals }) →
      shapeEqHOL (shapeOfHOLExact v) sh = true →
      WsSafe (setVarHOLFinite nm v { cpost with locals := s.locals }) (untypedGlobalBufIvls s0)
        (evaluateHOLFiniteState (setVarHOLFinite nm v { cpost with locals := s.locals }) cont) ∧
      ((evaluateHOLFiniteState (setVarHOLFinite nm v { cpost with locals := s.locals }) cont).1 = none →
        Q (restoreLocal nm (s.locals.lookup nm)
            (evaluateHOLFiniteState (setVarHOLFinite nm v { cpost with locals := s.locals }) cont).2))) :
    WsSafe s (untypedGlobalBufIvls s0)
      (evaluateHOLFiniteState s (.decCall nm sh fname args cont)) ∧
    ((evaluateHOLFiniteState s (.decCall nm sh fname args cont)).1 = none →
      Q (evaluateHOLFiniteState s (.decCall nm sh fname args cont)).2) := by
  refine ⟨WsSafe.decCall_ro he hfn (fun v cpost he_nx hsh _ => (hcont v cpost he_nx hsh).1), ?_⟩
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vals
  · intro h; simp at h
  · dsimp only
    rcases hl : lookupCodeHOLFinite s.code.lookup fname vals with _ | ⟨body, callee, rs⟩
    · intro h; simp at h
    · dsimp only
      by_cases hz : s.clock = 0
      · rw [if_pos hz]; intro h; simp at h
      · rw [if_neg hz]
        have hl' : lookupCodeHOLFinite originalRuntimeCode.lookup fname vals = some (body, callee, rs) := by
          rwa [← he.code]
        have hc_ro : WsSafe (callEntryStateHOLFinite s callee) (untypedGlobalBufIvls s0)
            (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body) :=
          WsSafe.of_readOnly he.code (opRoCallees_good fname hfn vals body callee rs hl')
        have he_ce : ByteRegionEffect s (callEntryStateHOLFinite s callee) (untypedGlobalBufIvls s0) :=
          (ByteRegionEffect.refl s _).with_locals_clock callee (s.clock - 1)
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨rb, cpost⟩
        rw [hrun] at hc_ro
        dsimp only at hc_ro ⊢
        cases rb with
        | none => intro h; simp at h
        | some r0 =>
          cases r0 with
          | returned v =>
            dsimp only
            split
            · rename_i hsh
              obtain ⟨hsh1, _⟩ := Bool.and_eq_true_iff.1 hsh
              have he_cp := he_ce.trans (hc_ro.2 (Or.inl ⟨v, rfl⟩))
              have he_nx : WsEnv s0 (setVarHOLFinite nm v { cpost with locals := s.locals }) :=
                ⟨he_cp.code.trans he.code, he_cp.memaddrs.trans he.memaddrs,
                 he_cp.globals.trans he.globals, he.ws_bnd⟩
              have hco := (hcont v cpost he_nx hsh1).2
              rcases hrc : evaluateHOLFiniteState (setVarHOLFinite nm v { cpost with locals := s.locals }) cont with ⟨rc, sp⟩
              rw [hrc] at hco
              dsimp only at hco ⊢
              exact hco
            · intro h; simp at h
          | exception _ _ | timeOut | error | «break» | «continue» | finalFfi _ =>
            intro h; simp at h

theorem WsSafe.while_loop_post {F : Type} {cond : ExpHOL 64} {body : ProgHOL 64} {Rl : List Ivl}
    (hnb : noTopBreakContinue body = true)
    (P : PanSemStateFiniteExact 64 F → Prop)
    (hdec : ∀ t, P t → P (decClockHOLFinite t))
    (hbody : ∀ t w, P (decClockHOLFinite t) →
      @evalHOLFinite 64 F _ t (fun a => Classical.propDecidable (t.memaddrs a)) cond =
        some (.val (.word w)) → w ≠ 0 →
      WsSafe (decClockHOLFinite t) Rl (evaluateHOLFiniteState (decClockHOLFinite t) body) ∧
      ((evaluateHOLFiniteState (decClockHOLFinite t) body).1 = none →
        P (evaluateHOLFiniteState (decClockHOLFinite t) body).2))
    (s : PanSemStateFiniteExact 64 F) (hPs : P s) :
    WsSafe s Rl (evaluateHOLFiniteState s (.while cond body)) ∧
    ((evaluateHOLFiniteState s (.while cond body)).1 = none →
      P (evaluateHOLFiniteState s (.while cond body)).2) := by
  refine ⟨WsSafe.while_loop hnb P hdec hbody s hPs, ?_⟩
  have hmain : ∀ (k : Nat) (t : PanSemStateFiniteExact 64 F), t.clock = k → P t →
      (evaluateHOLFiniteState t (.while cond body)).1 = none →
      P (evaluateHOLFiniteState t (.while cond body)).2 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro t hclk hPt
      rw [evaluateHOLFiniteState_while_fixClockRewrite]
      rcases hc : @evalHOLFinite 64 F _ t (fun a => Classical.propDecidable (t.memaddrs a)) cond with
        _ | cv
      · intro h; simp at h
      · rcases cv with ⟨⟨w⟩⟩ | _ | _
        · dsimp only
          by_cases hw : w = 0
          · subst hw; intro _; exact hPt
          · rw [if_pos hw]
            by_cases hk0 : t.clock = 0
            · rw [if_pos hk0]; intro h; simp at h
            · rw [if_neg hk0]
              have ⟨_, hPb⟩ := hbody t w (hdec t hPt) hc hw
              have ⟨hnbr, hnco⟩ := evaluate_noTopBreakContinue body hnb (decClockHOLFinite t)
              have hb_clk := Flapjack.evaluateHOLFiniteState_clock_le (decClockHOLFinite t) body
              have hd_lt : (decClockHOLFinite t).clock < k := by
                simp [decClockHOLFinite, hclk]; omega
              rcases hbo : evaluateHOLFiniteState (decClockHOLFinite t) body with ⟨rb, sb⟩
              rw [hbo] at hPb hnbr hnco hb_clk
              dsimp only at hPb hnbr hnco hb_clk ⊢
              cases rb with
              | none =>
                exact ih sb.clock (lt_of_le_of_lt hb_clk hd_lt) sb rfl (hPb rfl)
              | some r0 =>
                cases r0 with
                | «continue» => exact absurd rfl hnco
                | «break» => exact absurd rfl hnbr
                | returned _ | exception _ _ | timeOut | error | finalFfi _ =>
                  intro h; simp at h
        · intro h; simp at h
        · intro h; simp at h
  exact hmain s.clock s rfl hPs

theorem assign_local_step_eq {F : Type} {s : PanSemStateFiniteExact 64 F}
    {nm : MlS} {e : ExpHOL 64} {w : BitVec 64}
    (hcur : ∃ w0 : BitVec 64, s.locals.lookup nm = some (.val (.word w0)))
    (hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e =
      some (.val (.word w))) :
    evaluateHOLFiniteState s (.assign .local nm e) =
      (none, setVarHOLFinite nm (.val (.word w)) s) := by
  obtain ⟨w0, hw0⟩ := hcur
  simp [evaluateHOLFiniteState_assign, hev, lookupKvarHOLExact, hw0,
    isValidValueHOLExact, setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL]

theorem store_none_locals {F : Type} {s : PanSemStateFiniteExact 64 F}
    {dst val : ExpHOL 64}
    (hn : (evaluateHOLFiniteState s (.store dst val)).1 = none) :
    (evaluateHOLFiniteState s (.store dst val)).2.locals = s.locals :=
  (evaluate_store_control_frame s dst val).2.1

theorem WsSafe.seq_assign_word {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    (he : WsEnv s0 s) {nm : MlS} {e : ExpHOL 64} {w : BitVec 64} {rest : ProgHOL 64}
    (hcur : ∃ w0 : BitVec 64, s.locals.lookup nm = some (.val (.word w0)))
    (hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e =
      some (.val (.word w)))
    (hnext : WsEnv s0 (setVarHOLFinite nm (.val (.word w)) s) →
      WsSafe (setVarHOLFinite nm (.val (.word w)) s) (untypedGlobalBufIvls s0)
        (evaluateHOLFiniteState (setVarHOLFinite nm (.val (.word w)) s) rest)) :
    WsSafe s (untypedGlobalBufIvls s0)
      (evaluateHOLFiniteState s (.seq (.assign .local nm e) rest)) := by
  refine WsSafe.seq (WsSafe.assign_local s _ nm e) ?_
  intro hn heff
  have hstep := assign_local_step_eq hcur hev
  have h2 : (evaluateHOLFiniteState s (.assign .local nm e)).2 =
      setVarHOLFinite nm (.val (.word w)) s := congrArg Prod.snd hstep
  rw [h2] at heff ⊢
  exact hnext ⟨heff.code.trans he.code, heff.memaddrs.trans he.memaddrs,
    heff.globals.trans he.globals, he.ws_bnd⟩

theorem WsSafe.seq_store_ws_scaled {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    (he : WsEnv s0 s) {baseExp idxExp valExp : ExpHOL 64} {off idx : Nat} {rest : ProgHOL 64}
    (hbase : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) baseExp =
      some (.val (.word (BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 off))))
    (hidx : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) idxExp =
      some (.val (.word (BitVec.ofNat 64 idx))))
    (hoff : off + idx * 8 + 8 ≤ 640)
    (hval : ∀ v : ValueHOL 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) valExp = some v →
      ∃ w : BitVec 64, v = .val (.word w))
    (hnext : ∀ t, WsEnv s0 t → t.locals = s.locals →
      WsSafe t (untypedGlobalBufIvls s0) (evaluateHOLFiniteState t rest)) :
    WsSafe s (untypedGlobalBufIvls s0)
      (evaluateHOLFiniteState s
        (.seq (.store (.op .add [baseExp, .panop .mul [idxExp, .const 8#64]]) valExp) rest)) := by
  refine WsSafe.seq (WsSafe.store_ws_scaled he hbase hidx hoff hval) ?_
  intro hn heff
  exact hnext _ (he.step heff) (store_none_locals hn)

theorem WsSafe.seq_store_ws_const_off {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    (he : WsEnv s0 s) {dst valExp : ExpHOL 64} {off : Nat} {rest : ProgHOL 64}
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dst =
      some (.val (.word (BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 off))))
    (hoff : off + 8 ≤ 640)
    (hval : ∀ v : ValueHOL 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) valExp = some v →
      ∃ w : BitVec 64, v = .val (.word w))
    (hnext : ∀ t, WsEnv s0 t → t.locals = s.locals →
      WsSafe t (untypedGlobalBufIvls s0) (evaluateHOLFiniteState t rest)) :
    WsSafe s (untypedGlobalBufIvls s0)
      (evaluateHOLFiniteState s (.seq (.store dst valExp) rest)) := by
  refine WsSafe.seq (WsSafe.store_ws_const_off he hdst hoff hval) ?_
  intro hn heff
  exact hnext _ (he.step heff) (store_none_locals hn)

theorem WsSafe.while_up_store {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    (he : WsEnv s0 s)
    {cnt base : MlS} {limExp valExp : ExpHOL 64}
    {off lim idx0 : Nat}
    (hne : cnt ≠ base)
    (hlim_inv : ∀ t : PanSemStateFiniteExact 64 F,
      (∀ x, x ≠ cnt → t.locals.lookup x = s.locals.lookup x) →
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) limExp =
        some (.val (.word (BitVec.ofNat 64 lim))))
    (hbase : s.locals.lookup base =
      some (.val (.word (BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 off))))
    (hcnt0 : s.locals.lookup cnt = some (.val (.word (BitVec.ofNat 64 idx0))))
    (hlim_lt : lim < 2 ^ 64)
    (hidx_lt : idx0 < 2 ^ 64)
    (hoff : ∀ k, k < lim → off + k * 8 + 8 ≤ 640)
    (hval : isWordValExp valExp = true) :
    let body := ProgHOL.seq
      (.store (.op .add [.var .local base, .panop .mul [.var .local cnt, .const 8#64]]) valExp)
      (.assign .local cnt (.op .add [.var .local cnt, .const 1#64]))
    let prog := ProgHOL.while (.cmp .lower (.var .local cnt) limExp) body
    WsSafe s (untypedGlobalBufIvls s0) (evaluateHOLFiniteState s prog) ∧
    ((evaluateHOLFiniteState s prog).1 = none →
      WsEnv s0 (evaluateHOLFiniteState s prog).2 ∧
      (∃ k : Nat, k < 2 ^ 64 ∧
        (evaluateHOLFiniteState s prog).2.locals.lookup cnt = some (.val (.word (BitVec.ofNat 64 k)))) ∧
      (∀ x, x ≠ cnt → (evaluateHOLFiniteState s prog).2.locals.lookup x = s.locals.lookup x)) := by
  dsimp only
  let body := ProgHOL.seq
    (.store (.op .add [.var .local base, .panop .mul [.var .local cnt, .const 8#64]]) valExp)
    (.assign .local cnt (.op .add [.var .local cnt, .const 1#64]))
  let P : PanSemStateFiniteExact 64 F → Prop := fun t =>
    WsEnv s0 t ∧
    (∃ k : Nat, k < 2 ^ 64 ∧ t.locals.lookup cnt = some (.val (.word (BitVec.ofNat 64 k)))) ∧
    (∀ x, x ≠ cnt → t.locals.lookup x = s.locals.lookup x)
  have hP0 : P s := ⟨he, ⟨idx0, hidx_lt, hcnt0⟩, fun _ _ => rfl⟩
  have hnb : noTopBreakContinue body = true := rfl
  have hstep : ∀ t w, P (decClockHOLFinite t) →
      @evalHOLFinite 64 F _ t (fun a => Classical.propDecidable (t.memaddrs a))
        (.cmp .lower (.var .local cnt) limExp) = some (.val (.word w)) → w ≠ 0 →
      WsSafe (decClockHOLFinite t) (untypedGlobalBufIvls s0)
        (evaluateHOLFiniteState (decClockHOLFinite t) body) ∧
      ((evaluateHOLFiniteState (decClockHOLFinite t) body).1 = none →
        P (evaluateHOLFiniteState (decClockHOLFinite t) body).2) := by
    intro t w ⟨ht_env, ⟨k, hk2, hcnt_t⟩, hother_t⟩ hcnd hw0
    have hcnt_t0 : t.locals.lookup cnt = some (.val (.word (BitVec.ofNat 64 k))) := hcnt_t
    have hlim_t : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) limExp =
        some (.val (.word (BitVec.ofNat 64 lim))) := hlim_inv t hother_t
    have hk_lt_lim : k < lim := by
      simp only [evalHOLFinite, evalHOLExact, hcnt_t0, hlim_t, wordCmpHOL, BitVec.lt_def,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk2, Nat.mod_eq_of_lt hlim_lt] at hcnd
      by_cases hlt : k < lim
      · exact hlt
      · simp [hlt] at hcnd; exact absurd hcnd.symm hw0
    have hbase_d : (decClockHOLFinite t).locals.lookup base =
        some (.val (.word (BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 off))) := by
      rw [hother_t base (Ne.symm hne)]; exact hbase
    have hst_safe : WsSafe (decClockHOLFinite t) (untypedGlobalBufIvls s0)
        (evaluateHOLFiniteState (decClockHOLFinite t)
          (.store (.op .add [.var .local base, .panop .mul [.var .local cnt, .const 8#64]]) valExp)) :=
      WsSafe.store_ws_scaled ht_env
        (by simp [evalHOLExact, hbase_d])
        (by simp [evalHOLExact, hcnt_t])
        (hoff k hk_lt_lim)
        (fun _ hv => eval_word_of_isWordValExp hval hv)
    refine ⟨WsSafe.seq hst_safe (fun _ _ => WsSafe.assign_local _ _ _ _), fun hbn => ?_⟩
    dsimp only [body] at hbn ⊢
    rw [evaluateHOLFiniteState_seq_line780] at hbn ⊢
    have hmid_loc_gen := store_none_locals (s := decClockHOLFinite t)
      (dst := .op .add [.var .local base, .panop .mul [.var .local cnt, .const 8#64]])
      (val := valExp)
    rcases hr1 : evaluateHOLFiniteState (decClockHOLFinite t)
      (.store (.op .add [.var .local base, .panop .mul [.var .local cnt, .const 8#64]]) valExp) with ⟨r1, mid⟩
    rw [hr1] at hbn hst_safe hmid_loc_gen
    dsimp only at hbn hst_safe hmid_loc_gen ⊢
    cases r1 with
    | some _ => simp at hbn
    | none =>
      have heff1 := hst_safe.1 rfl
      have hmid_loc : mid.locals = (decClockHOLFinite t).locals := hmid_loc_gen rfl
      have hcnt_mid : mid.locals.lookup cnt = some (.val (.word (BitVec.ofNat 64 k))) := by
        rw [hmid_loc]; exact hcnt_t
      have hev_inc : @evalHOLExact 64 F _ mid.toExact (fun a => Classical.propDecidable (mid.memaddrs a))
          (.op .add [.var .local cnt, .const 1#64]) =
          some (.val (.word (BitVec.ofNat 64 (k + 1)))) := by
        simp only [evalHOLExact, evalListHOLExact, hcnt_mid, wordOpHOL, wordOp,
          valueIsWord, valueWord, List.all, List.map, Bool.and_self, ↓reduceIte, Option.map, List.foldr]
        congr 3
        rw [show (1#64 + 0 : BitVec 64) = 1#64 from BitVec.add_zero _]
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
        omega
      have hasg := assign_local_step_eq ⟨_, hcnt_mid⟩ hev_inc
      rw [hasg]; dsimp only
      refine ⟨⟨(ht_env.step heff1).code, (ht_env.step heff1).memaddrs,
               (ht_env.step heff1).globals, ht_env.ws_bnd⟩,
             ⟨k + 1, by omega, by simp [setVarHOLFinite, FUPDATE]⟩, ?_⟩
      intro x hx
      simp [setVarHOLFinite, FUPDATE, Ne.symm hx, hmid_loc, hother_t x hx]
  have hpost := WsSafe.while_loop_post hnb P
    (fun t ⟨h1, h2, h3⟩ => ⟨⟨h1.code, h1.memaddrs, h1.globals, h1.ws_bnd⟩, h2, h3⟩) hstep s hP0
  exact hpost

theorem WsSafe.while_down_post_store {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    (he : WsEnv s0 s)
    {cnt base : MlS} {valExp : ExpHOL 64}
    {off idx0 : Nat}
    (hne : cnt ≠ base)
    (hbase : s.locals.lookup base =
      some (.val (.word (BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 off))))
    (hcnt0 : s.locals.lookup cnt = some (.val (.word (BitVec.ofNat 64 idx0))))
    (hidx_lt : idx0 < 2 ^ 64)
    (hoff : ∀ k, 1 ≤ k → k ≤ idx0 → off + k * 8 + 8 ≤ 640)
    (hval : isWordValExp valExp = true) :
    let body := ProgHOL.seq
      (.store (.op .add [.var .local base, .panop .mul [.var .local cnt, .const 8#64]]) valExp)
      (.assign .local cnt (.op .sub [.var .local cnt, .const 1#64]))
    let prog := ProgHOL.while (.cmp .lower (.const 0#64) (.var .local cnt)) body
    WsSafe s (untypedGlobalBufIvls s0) (evaluateHOLFiniteState s prog) ∧
    ((evaluateHOLFiniteState s prog).1 = none →
      WsEnv s0 (evaluateHOLFiniteState s prog).2 ∧
      (∃ k : Nat, k ≤ idx0 ∧
        (evaluateHOLFiniteState s prog).2.locals.lookup cnt = some (.val (.word (BitVec.ofNat 64 k)))) ∧
      (∀ x, x ≠ cnt → (evaluateHOLFiniteState s prog).2.locals.lookup x = s.locals.lookup x)) := by
  dsimp only
  let body := ProgHOL.seq
    (.store (.op .add [.var .local base, .panop .mul [.var .local cnt, .const 8#64]]) valExp)
    (.assign .local cnt (.op .sub [.var .local cnt, .const 1#64]))
  let P : PanSemStateFiniteExact 64 F → Prop := fun t =>
    WsEnv s0 t ∧
    (∃ k : Nat, k ≤ idx0 ∧ t.locals.lookup cnt = some (.val (.word (BitVec.ofNat 64 k)))) ∧
    (∀ x, x ≠ cnt → t.locals.lookup x = s.locals.lookup x)
  have hP0 : P s := ⟨he, ⟨idx0, le_refl _, hcnt0⟩, fun _ _ => rfl⟩
  have hnb : noTopBreakContinue body = true := rfl
  have hstep : ∀ t w, P (decClockHOLFinite t) →
      @evalHOLFinite 64 F _ t (fun a => Classical.propDecidable (t.memaddrs a))
        (.cmp .lower (.const 0#64) (.var .local cnt)) = some (.val (.word w)) → w ≠ 0 →
      WsSafe (decClockHOLFinite t) (untypedGlobalBufIvls s0)
        (evaluateHOLFiniteState (decClockHOLFinite t) body) ∧
      ((evaluateHOLFiniteState (decClockHOLFinite t) body).1 = none →
        P (evaluateHOLFiniteState (decClockHOLFinite t) body).2) := by
    intro t w ⟨ht_env, ⟨k, hk_le, hcnt_t⟩, hother_t⟩ hcnd hw0
    have hcnt_t0 : t.locals.lookup cnt = some (.val (.word (BitVec.ofNat 64 k))) := hcnt_t
    have hk_pos : 1 ≤ k := by
      simp only [evalHOLFinite, evalHOLExact, hcnt_t0, wordCmpHOL, BitVec.lt_def,
        BitVec.toNat_ofNat, Nat.zero_mod, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega)] at hcnd
      by_cases hpos : 0 < k
      · omega
      · simp [hpos] at hcnd; exact absurd hcnd.symm hw0
    have hbase_d : (decClockHOLFinite t).locals.lookup base =
        some (.val (.word (BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 off))) := by
      rw [hother_t base (Ne.symm hne)]; exact hbase
    have hst_safe : WsSafe (decClockHOLFinite t) (untypedGlobalBufIvls s0)
        (evaluateHOLFiniteState (decClockHOLFinite t)
          (.store (.op .add [.var .local base, .panop .mul [.var .local cnt, .const 8#64]]) valExp)) :=
      WsSafe.store_ws_scaled ht_env
        (by simp [evalHOLExact, hbase_d])
        (by simp [evalHOLExact, hcnt_t])
        (hoff k hk_pos hk_le)
        (fun _ hv => eval_word_of_isWordValExp hval hv)
    refine ⟨WsSafe.seq hst_safe (fun _ _ => WsSafe.assign_local _ _ _ _), fun hbn => ?_⟩
    dsimp only [body] at hbn ⊢
    rw [evaluateHOLFiniteState_seq_line780] at hbn ⊢
    have hmid_loc_gen := store_none_locals (s := decClockHOLFinite t)
      (dst := .op .add [.var .local base, .panop .mul [.var .local cnt, .const 8#64]])
      (val := valExp)
    rcases hr1 : evaluateHOLFiniteState (decClockHOLFinite t)
      (.store (.op .add [.var .local base, .panop .mul [.var .local cnt, .const 8#64]]) valExp) with ⟨r1, mid⟩
    rw [hr1] at hbn hst_safe hmid_loc_gen
    dsimp only at hbn hst_safe hmid_loc_gen ⊢
    cases r1 with
    | some _ => simp at hbn
    | none =>
      have heff1 := hst_safe.1 rfl
      have hmid_loc : mid.locals = (decClockHOLFinite t).locals := hmid_loc_gen rfl
      have hcnt_mid : mid.locals.lookup cnt = some (.val (.word (BitVec.ofNat 64 k))) := by
        rw [hmid_loc]; exact hcnt_t
      have hev_dec : @evalHOLExact 64 F _ mid.toExact (fun a => Classical.propDecidable (mid.memaddrs a))
          (.op .sub [.var .local cnt, .const 1#64]) =
          some (.val (.word (BitVec.ofNat 64 (k - 1)))) := by
        simp only [evalHOLExact, evalListHOLExact, hcnt_mid, wordOpHOL, wordOp,
          valueIsWord, valueWord, List.all, List.map, Bool.and_self, ↓reduceIte, Option.map]
        congr 3
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
        omega
      have hasg := assign_local_step_eq ⟨_, hcnt_mid⟩ hev_dec
      rw [hasg]; dsimp only
      refine ⟨⟨(ht_env.step heff1).code, (ht_env.step heff1).memaddrs,
               (ht_env.step heff1).globals, ht_env.ws_bnd⟩,
             ⟨k - 1, by omega, by simp [setVarHOLFinite, FUPDATE]⟩, ?_⟩
      intro x hx
      simp [setVarHOLFinite, FUPDATE, Ne.symm hx, hmid_loc, hother_t x hx]
  exact WsSafe.while_loop_post hnb P
    (fun t ⟨h1, h2, h3⟩ => ⟨⟨h1.code, h1.memaddrs, h1.globals, h1.ws_bnd⟩, h2, h3⟩) hstep s hP0

theorem WsSafe.dec_post {F : Type} {s : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    {Q : PanSemStateFiniteExact 64 F → Prop}
    {nm : MlS} {sh : ShapeHOL} {init : ExpHOL 64} {body : ProgHOL 64}
    (hbody : ∀ v,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) init = some v →
      shapeEqHOL sh (shapeOfHOLExact v) = true →
      WsSafe (setVarHOLFinite nm v s) Rl (evaluateHOLFiniteState (setVarHOLFinite nm v s) body) ∧
      ((evaluateHOLFiniteState (setVarHOLFinite nm v s) body).1 = none →
        Q (restoreLocal nm (s.locals.lookup nm)
            (evaluateHOLFiniteState (setVarHOLFinite nm v s) body).2))) :
    WsSafe s Rl (evaluateHOLFiniteState s (.dec nm sh init body)) ∧
    ((evaluateHOLFiniteState s (.dec nm sh init body)).1 = none →
      Q (evaluateHOLFiniteState s (.dec nm sh init body)).2) := by
  refine ⟨WsSafe.dec (fun v hv hsh => (hbody v hv hsh).1), ?_⟩
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  split
  · intro h; simp at h
  · rename_i v hv
    split
    · rename_i hsh
      have hq := (hbody v hv hsh).2
      rcases hrun : evaluateHOLFiniteState (setVarHOLFinite nm v s) body with ⟨rb, sb⟩
      rw [hrun] at hq
      dsimp only at hq ⊢
      exact hq
    · intro h; simp at h

theorem WsSafe.seq_post {F : Type} {s : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    {P1 Q : PanSemStateFiniteExact 64 F → Prop}
    {p1 p2 : ProgHOL 64}
    (h1 : WsSafe s Rl (evaluateHOLFiniteState s p1) ∧
          ((evaluateHOLFiniteState s p1).1 = none → P1 (evaluateHOLFiniteState s p1).2))
    (h2 : ∀ s1, P1 s1 →
      WsSafe s1 Rl (evaluateHOLFiniteState s1 p2) ∧
      ((evaluateHOLFiniteState s1 p2).1 = none → Q (evaluateHOLFiniteState s1 p2).2)) :
    WsSafe s Rl (evaluateHOLFiniteState s (.seq p1 p2)) ∧
    ((evaluateHOLFiniteState s (.seq p1 p2)).1 = none →
      Q (evaluateHOLFiniteState s (.seq p1 p2)).2) := by
  refine ⟨WsSafe.seq h1.1 (fun hn _ => (h2 _ (h1.2 hn)).1), ?_⟩
  rw [evaluateHOLFiniteState_seq_line780]
  rcases hr1 : evaluateHOLFiniteState s p1 with ⟨r1, s1⟩
  have hp1 := h1.2
  rw [hr1] at hp1
  dsimp only at hp1 ⊢
  cases r1 with
  | some _ => intro h; simp at h
  | none => exact (h2 s1 (hp1 rfl)).2

theorem WsSafe.ite_post {F : Type} {s : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    {Q : PanSemStateFiniteExact 64 F → Prop}
    {cond : ExpHOL 64} {yes no : ProgHOL 64}
    (hyes : ∀ w : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) cond =
        some (.val (.word w)) → w ≠ 0 →
      WsSafe s Rl (evaluateHOLFiniteState s yes) ∧
      ((evaluateHOLFiniteState s yes).1 = none → Q (evaluateHOLFiniteState s yes).2))
    (hno : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) cond =
        some (.val (.word 0)) →
      WsSafe s Rl (evaluateHOLFiniteState s no) ∧
      ((evaluateHOLFiniteState s no).1 = none → Q (evaluateHOLFiniteState s no).2)) :
    WsSafe s Rl (evaluateHOLFiniteState s (.ite cond yes no)) ∧
    ((evaluateHOLFiniteState s (.ite cond yes no)).1 = none →
      Q (evaluateHOLFiniteState s (.ite cond yes no)).2) := by
  refine ⟨WsSafe.ite (fun w hw hw0 => (hyes w hw hw0).1) (fun hw => (hno hw).1), ?_⟩
  rw [evaluateHOLFiniteState_ite]
  split
  · rename_i w hw
    by_cases hw0 : w = 0
    · subst hw0; simp only [↓reduceIte]; exact (hno hw).2
    · simp only [hw0, ↓reduceIte]; exact (hyes w hw hw0).2
  · intro h; simp at h

theorem WsSafe.assign_word_post {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    {Q : PanSemStateFiniteExact 64 F → Prop}
    (he : WsEnv s0 s) {nm : MlS} {e : ExpHOL 64}
    (hcur : ∃ w0 : BitVec 64, s.locals.lookup nm = some (.val (.word w0)))
    (hq : ∀ w : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e =
        some (.val (.word w)) →
      Q (setVarHOLFinite nm (.val (.word w)) s))
    (hew : ∀ v, @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e = some v →
      ∃ w : BitVec 64, v = .val (.word w)) :
    WsSafe s (untypedGlobalBufIvls s0) (evaluateHOLFiniteState s (.assign .local nm e)) ∧
    ((evaluateHOLFiniteState s (.assign .local nm e)).1 = none →
      Q (evaluateHOLFiniteState s (.assign .local nm e)).2) := by
  refine ⟨WsSafe.assign_local s _ nm e, ?_⟩
  rcases hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e with _ | v
  · simp [evaluateHOLFiniteState_assign, hev]
  · obtain ⟨w, rfl⟩ := hew v hev
    rw [assign_local_step_eq hcur hev]
    intro _; exact hq w hev

/-- Syntactic check that `p` never writes to local `x`. -/
def notAssignedLocal (x : MlS) : ProgHOL 64 → Bool
  | .dec nm _ _ body => (nm == x) || notAssignedLocal x body
  | .seq p1 p2 => notAssignedLocal x p1 && notAssignedLocal x p2
  | .ite _ p1 p2 => notAssignedLocal x p1 && notAssignedLocal x p2
  | .while _ body => notAssignedLocal x body
  | .decCall nm _ _ _ cont => (nm == x) || notAssignedLocal x cont
  | .call (some (some (.local, nm), none)) _ _ => nm != x
  | .call (some (none, none)) _ _ => true
  | .call none _ _ => true
  | .assign .local nm _ => nm != x
  | .primitive nm _ _ => nm != x
  | .skip | .break | .continue | .annot _ _ | .raise _ _ | .return _
  | .store _ _ | .assign .global _ _ => true
  | _ => false

private def isNormalCtrl : Option (PanSemResultExact 64) → Bool
  | none | some .break | some .continue => true
  | _ => false

theorem evaluate_notAssignedLocal {F : Type} {x : MlS}
    (p : ProgHOL 64) (hna : notAssignedLocal x p = true)
    (s : PanSemStateFiniteExact 64 F) :
    isNormalCtrl (evaluateHOLFiniteState s p).1 = true →
    (evaluateHOLFiniteState s p).2.locals.lookup x = s.locals.lookup x := by
  cases shape : p with
  | skip => rw [evaluateHOLFiniteState_skip]; intro _; rfl
  | «break» => rw [evaluateHOLFiniteState_break]; intro _; rfl
  | «continue» => rw [evaluateHOLFiniteState_continue]; intro _; rfl
  | annot _ _ => rw [evaluateHOLFiniteState_annot]; intro _; rfl
  | raise _ _ =>
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only; split <;> (intro h; simp [isNormalCtrl] at h)
    · intro h; simp [isNormalCtrl] at h
  | «return» _ =>
    rw [evaluateHOLFiniteState_return]
    split
    · intro h; simp [isNormalCtrl] at h
    · split <;> (intro h; simp [isNormalCtrl] at h)
  | store _ _ =>
    rw [evaluateHOLFiniteState_store]; intro _
    split
    · split
      · split <;> rfl
      · rfl
    · rfl
  | assign vk nm val =>
    cases vk with
    | global =>
      rw [evaluateHOLFiniteState_assign]; intro _
      split
      · rfl
      · split <;> rfl
    | «local» =>
      have hne : nm ≠ x := by simpa [shape, notAssignedLocal, bne_iff_ne] using hna
      rw [evaluateHOLFiniteState_assign]; intro _
      split
      · rfl
      · split
        · simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne]
        · rfl
  | primitive nm op args =>
    have hne : nm ≠ x := by simpa [shape, notAssignedLocal, bne_iff_ne] using hna
    rw [evaluateHOLFiniteState_primitive]; intro _
    split
    · rfl
    · split
      · rfl
      · split
        · simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne]
        · rfl
  | dec nm sh init body =>
    have hch : nm = x ∨ notAssignedLocal x body = true := by
      simpa [shape, notAssignedLocal, Bool.or_eq_true, beq_iff_eq] using hna
    rw [evaluateHOLFiniteState_dec_total]; dsimp only
    split
    · intro h; simp [isNormalCtrl] at h
    · rename_i v _
      split
      · intro hout
        by_cases hxn : x = nm
        · subst hxn; rw [PanRunBounded.resVarEq_lookup, if_pos rfl]
        · have hb := hch.resolve_left (Ne.symm hxn)
          rw [PanRunBounded.resVarEq_lookup, if_neg hxn]
          have ih := evaluate_notAssignedLocal body hb (setVarHOLFinite nm v s) hout
          rw [ih]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hxn]
      · intro h; simp [isNormalCtrl] at h
  | seq p1 p2 =>
    have hch : notAssignedLocal x p1 = true ∧ notAssignedLocal x p2 = true := by
      simpa [shape, notAssignedLocal, Bool.and_eq_true] using hna
    have rem := evaluateHOLFiniteState_clock_le s p1
    rw [evaluateHOLFiniteState_seq_line780]
    rcases hr1 : evaluateHOLFiniteState s p1 with ⟨r1, s1⟩
    have ih1 := evaluate_notAssignedLocal p1 hch.1 s
    rw [hr1] at rem ih1
    dsimp only at rem ih1 ⊢
    cases r1 with
    | none =>
      have mclock : s1.clock ≤ s.clock := rem
      intro hout
      have ih2 := evaluate_notAssignedLocal p2 hch.2 s1 hout
      exact ih2.trans (ih1 rfl)
    | some r =>
      cases r with
      | «break» => intro _; exact ih1 rfl
      | «continue» => intro _; exact ih1 rfl
      | _ => intro h; simp [isNormalCtrl] at h
  | ite cond p1 p2 =>
    have hch : notAssignedLocal x p1 = true ∧ notAssignedLocal x p2 = true := by
      simpa [shape, notAssignedLocal, Bool.and_eq_true] using hna
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_notAssignedLocal p2 hch.2 s
      · exact evaluate_notAssignedLocal p1 hch.1 s
    · intro h; simp [isNormalCtrl] at h
  | «while» cond body =>
    have hb : notAssignedLocal x body = true := by simpa [shape, notAssignedLocal] using hna
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · intro h; simp [isNormalCtrl] at h
        · dsimp only
          rw [fixClockHOLFinite_evaluateState]
          have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
          rcases hrb : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨rb, mid⟩
          have ih1 := evaluate_notAssignedLocal body hb (decClockHOLFinite s)
          rw [hrb] at rem ih1
          dsimp only at rem ih1 ⊢
          have smaller : mid.clock < s.clock := by
            change mid.clock ≤ s.clock - 1 at rem; omega
          cases rb with
          | none =>
            intro hout
            have ih2 := evaluate_notAssignedLocal (.while cond body) (by simpa [notAssignedLocal] using hb) mid hout
            exact ih2.trans (ih1 rfl)
          | some r =>
            cases r with
            | «continue» =>
              intro hout
              have ih2 := evaluate_notAssignedLocal (.while cond body) (by simpa [notAssignedLocal] using hb) mid hout
              exact ih2.trans (ih1 rfl)
            | «break» => intro _; exact ih1 rfl
            | _ => intro h; simp [isNormalCtrl] at h
      · intro _; rfl
    · intro h; simp [isNormalCtrl] at h
  | decCall nm sh fname args cont =>
    have hch : nm = x ∨ notAssignedLocal x cont = true := by
      simpa [shape, notAssignedLocal, Bool.or_eq_true, beq_iff_eq] using hna
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
    rcases evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vals
    · intro h; simp [isNormalCtrl] at h
    · dsimp only
      rcases lookupCodeHOLFinite s.code.lookup fname vals with _ | ⟨body, callee, rs⟩
      · intro h; simp [isNormalCtrl] at h
      · dsimp only
        split
        · intro h; simp [isNormalCtrl] at h
        · have cl := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite s callee) body
          rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨res, st⟩
          rw [hrun] at cl
          dsimp only at cl ⊢
          change st.clock ≤ s.clock - 1 at cl
          have small : st.clock < s.clock := by omega
          cases res with
          | none => intro h; simp [isNormalCtrl] at h
          | some r =>
            cases r with
            | returned v =>
              dsimp only
              split
              · intro hout
                by_cases hxn : x = nm
                · subst hxn; rw [PanRunBounded.resVarEq_lookup, if_pos rfl]
                · have hc := hch.resolve_left (Ne.symm hxn)
                  rw [PanRunBounded.resVarEq_lookup, if_neg hxn]
                  set resumed := setVarHOLFinite nm v { st with locals := s.locals }
                  have smallR : resumed.clock < s.clock := small
                  have ih2 := evaluate_notAssignedLocal cont hc resumed hout
                  rw [ih2]; simp [resumed, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hxn]
              · intro h; simp [isNormalCtrl] at h
            | _ => intro h; simp [isNormalCtrl] at h
  | call rt fname args =>
    rcases rt with _ | ⟨dest, hdl⟩
    · rw [evaluateHOLFiniteState_call]
      rcases evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vals
      · intro h; simp [isNormalCtrl] at h
      · dsimp only
        rcases lookupCodeHOLFinite s.code.lookup fname vals with _ | ⟨body, callee, rs⟩
        · intro h; simp [isNormalCtrl] at h
        · dsimp only
          split
          · intro h; simp [isNormalCtrl] at h
          · rcases evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨res, st⟩
            cases res with
            | none => intro h; simp [isNormalCtrl] at h
            | some r =>
              cases r with
              | returned _ =>
                simp only []
                split <;> (intro h; simp [isNormalCtrl] at h)
              | _ => intro h; simp [isNormalCtrl] at h
    · rcases hdl with _ | _
      · rcases dest with _ | ⟨vk, nm⟩
        · rw [evaluateHOLFiniteState_call]
          rcases evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vals
          · intro _; rfl
          · dsimp only
            rcases lookupCodeHOLFinite s.code.lookup fname vals with _ | ⟨body, callee, rs⟩
            · intro _; rfl
            · dsimp only
              split
              · intro h; simp [isNormalCtrl] at h
              · rcases evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨res, st⟩
                cases res with
                | none => intro h; simp [isNormalCtrl] at h
                | some r =>
                  cases r with
                  | returned _ =>
                    simp only []
                    split
                    · intro _; rfl
                    · intro h; simp [isNormalCtrl] at h
                  | _ => intro h; simp [isNormalCtrl] at h
        · cases vk with
          | global => simp [shape, notAssignedLocal] at hna
          | «local» =>
            have hne : nm ≠ x := by simpa [shape, notAssignedLocal, bne_iff_ne] using hna
            rw [evaluateHOLFiniteState_call]
            rcases evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vals
            · intro _; rfl
            · dsimp only
              rcases lookupCodeHOLFinite s.code.lookup fname vals with _ | ⟨body, callee, rs⟩
              · intro _; rfl
              · dsimp only
                split
                · intro h; simp [isNormalCtrl] at h
                · rcases evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨res, st⟩
                  cases res with
                  | none => intro h; simp [isNormalCtrl] at h
                  | some r =>
                    cases r with
                    | returned _ =>
                      simp only []
                      split
                      · split
                        · intro _; simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne]
                        · intro h; simp [isNormalCtrl] at h
                      · intro h; simp [isNormalCtrl] at h
                    | _ => intro h; simp [isNormalCtrl] at h
      · simp [shape, notAssignedLocal] at hna
  | _ => simp [shape, notAssignedLocal] at hna
termination_by (s.clock, sizeOf p)
decreasing_by
  all_goals
    simp_wf
    apply GuestGlobalKeep.lex_of
    try subst shape
    try simp only [setVarHOLFinite, decClockHOLFinite, callEntryStateHOLFinite,
      ProgHOL.seq.sizeOf_spec, ProgHOL.ite.sizeOf_spec, ProgHOL.dec.sizeOf_spec,
      ProgHOL.while.sizeOf_spec, ProgHOL.decCall.sizeOf_spec, ProgHOL.call.sizeOf_spec, true_and]
    first
      | exact Or.inl smallR
      | exact Or.inl smaller
      | exact Or.inl small
      | omega
      | (rcases Nat.lt_or_eq_of_le mclock with h | h
         · exact Or.inl h
         · exact Or.inr ⟨h, by simp +arith⟩)
      | exact Or.inr ⟨rfl, by simp +arith⟩

/-- Syntactic check that `p` contains no calls with exception handlers or `primitive` statements
(holds for all arithmetic programs in `Guest/SoftwareAst.lean`). -/
def noPrimitiveOrHandledCall : ProgHOL 64 → Bool
  | .seq p1 p2 | .ite _ p1 p2 => noPrimitiveOrHandledCall p1 && noPrimitiveOrHandledCall p2
  | .while _ body | .dec _ _ _ body | .decCall _ _ _ _ body => noPrimitiveOrHandledCall body
  | .call (some (_, some _)) _ _ | .primitive _ _ _
  | .store32 _ _ | .storeByte _ _ | .extCall _ _ _ _ _
  | .shMemLoad _ _ _ _ | .shMemStore _ _ _ | .tick => false
  | _ => true

private theorem word_of_isValid_local {F : Type} {s : PanSemStateFiniteExact 64 F}
    {x : MlS} {w0 : BitVec 64} {v : ValueHOL 64}
    (hx : s.locals.lookup x = some (.val (.word w0)))
    (hv : isValidValueHOLExact s.toExact .local x v = true) :
    ∃ w : BitVec 64, v = .val (.word w) := by
  simp only [isValidValueHOLExact, lookupKvarHOLExact, toExact, hx, shapeOfHOLExact] at hv
  exact eval_word_of_shape_one (Or.inr hv)

/-- Any `noPrimitiveOrHandledCall` program preserves the word-ness of an existing word local `x`. -/
theorem evaluate_preserves_word_local {F : Type} {x : MlS}
    (p : ProgHOL 64) (hnp : noPrimitiveOrHandledCall p = true)
    (s : PanSemStateFiniteExact 64 F)
    (hx : ∃ w0 : BitVec 64, s.locals.lookup x = some (.val (.word w0))) :
    isNormalCtrl (evaluateHOLFiniteState s p).1 = true →
    ∃ w : BitVec 64, (evaluateHOLFiniteState s p).2.locals.lookup x = some (.val (.word w)) := by
  cases shape : p with
  | skip => rw [evaluateHOLFiniteState_skip]; intro _; exact hx
  | «break» => rw [evaluateHOLFiniteState_break]; intro _; exact hx
  | «continue» => rw [evaluateHOLFiniteState_continue]; intro _; exact hx
  | annot _ _ => rw [evaluateHOLFiniteState_annot]; intro _; exact hx
  | raise _ _ =>
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only; split <;> (intro h; simp [isNormalCtrl] at h)
    · intro h; simp [isNormalCtrl] at h
  | «return» _ =>
    rw [evaluateHOLFiniteState_return]
    split
    · intro h; simp [isNormalCtrl] at h
    · split <;> (intro h; simp [isNormalCtrl] at h)
  | store _ _ =>
    rw [evaluateHOLFiniteState_store]; intro _
    split
    · split
      · split <;> exact hx
      · exact hx
    · exact hx
  | assign vk nm val =>
    cases vk with
    | global =>
      rw [evaluateHOLFiniteState_assign]; intro _
      split
      · exact hx
      · split <;> exact hx
    | «local» =>
      rw [evaluateHOLFiniteState_assign]; intro _
      split
      · exact hx
      · rename_i v _
        split
        · rename_i hvld
          by_cases hnx : nm = x
          · subst hnx
            obtain ⟨w0, hw0⟩ := hx
            obtain ⟨w, rfl⟩ := word_of_isValid_local hw0 hvld
            exact ⟨w, by simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩
          · simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hnx, hx]
        · exact hx
  | store32 _ _ | storeByte _ _ | extCall _ _ _ _ _ | shMemLoad _ _ _ _ | shMemStore _ _ _ | tick =>
    simp [shape, noPrimitiveOrHandledCall] at hnp
  | primitive _ _ _ => simp [shape, noPrimitiveOrHandledCall] at hnp
  | dec nm sh init body =>
    have hb : noPrimitiveOrHandledCall body = true := by simpa [shape, noPrimitiveOrHandledCall] using hnp
    rw [evaluateHOLFiniteState_dec_total]; dsimp only
    split
    · intro h; simp [isNormalCtrl] at h
    · rename_i v _
      split
      · intro hout
        by_cases hxn : x = nm
        · subst hxn; rw [PanRunBounded.resVarEq_lookup, if_pos rfl]; exact hx
        · rw [PanRunBounded.resVarEq_lookup, if_neg hxn]
          have hx' : ∃ w0 : BitVec 64, (setVarHOLFinite nm v s).locals.lookup x = some (.val (.word w0)) := by
            simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hxn, hx]
          exact evaluate_preserves_word_local body hb (setVarHOLFinite nm v s) hx' hout
      · intro h; simp [isNormalCtrl] at h
  | seq p1 p2 =>
    have hch : noPrimitiveOrHandledCall p1 = true ∧ noPrimitiveOrHandledCall p2 = true := by
      simpa [shape, noPrimitiveOrHandledCall, Bool.and_eq_true] using hnp
    have rem := evaluateHOLFiniteState_clock_le s p1
    rw [evaluateHOLFiniteState_seq_line780]
    rcases hr1 : evaluateHOLFiniteState s p1 with ⟨r1, s1⟩
    have ih1 := evaluate_preserves_word_local p1 hch.1 s hx
    rw [hr1] at rem ih1
    dsimp only at rem ih1 ⊢
    cases r1 with
    | none =>
      have mclock : s1.clock ≤ s.clock := rem
      intro hout
      exact evaluate_preserves_word_local p2 hch.2 s1 (ih1 rfl) hout
    | some r =>
      cases r with
      | «break» => intro _; exact ih1 rfl
      | «continue» => intro _; exact ih1 rfl
      | _ => intro h; simp [isNormalCtrl] at h
  | ite cond p1 p2 =>
    have hch : noPrimitiveOrHandledCall p1 = true ∧ noPrimitiveOrHandledCall p2 = true := by
      simpa [shape, noPrimitiveOrHandledCall, Bool.and_eq_true] using hnp
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_preserves_word_local p2 hch.2 s hx
      · exact evaluate_preserves_word_local p1 hch.1 s hx
    · intro h; simp [isNormalCtrl] at h
  | «while» cond body =>
    have hb : noPrimitiveOrHandledCall body = true := by simpa [shape, noPrimitiveOrHandledCall] using hnp
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · intro h; simp [isNormalCtrl] at h
        · dsimp only
          rw [fixClockHOLFinite_evaluateState]
          have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
          rcases hrb : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨rb, mid⟩
          have ih1 := evaluate_preserves_word_local body hb (decClockHOLFinite s) hx
          rw [hrb] at rem ih1
          dsimp only at rem ih1 ⊢
          have smaller : mid.clock < s.clock := by
            change mid.clock ≤ s.clock - 1 at rem; omega
          cases rb with
          | none =>
            intro hout
            exact evaluate_preserves_word_local (.while cond body) (by simpa [noPrimitiveOrHandledCall] using hb) mid (ih1 rfl) hout
          | some r =>
            cases r with
            | «continue» =>
              intro hout
              exact evaluate_preserves_word_local (.while cond body) (by simpa [noPrimitiveOrHandledCall] using hb) mid (ih1 rfl) hout
            | «break» => intro _; exact ih1 rfl
            | _ => intro h; simp [isNormalCtrl] at h
      · intro _; exact hx
    · intro h; simp [isNormalCtrl] at h
  | decCall nm sh fname args cont =>
    have hc : noPrimitiveOrHandledCall cont = true := by simpa [shape, noPrimitiveOrHandledCall] using hnp
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
    rcases evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vals
    · intro h; simp [isNormalCtrl] at h
    · dsimp only
      rcases lookupCodeHOLFinite s.code.lookup fname vals with _ | ⟨body, callee, rs⟩
      · intro h; simp [isNormalCtrl] at h
      · dsimp only
        split
        · intro h; simp [isNormalCtrl] at h
        · have cl := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite s callee) body
          rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨res, st⟩
          rw [hrun] at cl
          dsimp only at cl ⊢
          change st.clock ≤ s.clock - 1 at cl
          have small : st.clock < s.clock := by omega
          cases res with
          | none => intro h; simp [isNormalCtrl] at h
          | some r =>
            cases r with
            | returned v =>
              dsimp only
              split
              · intro hout
                by_cases hxn : x = nm
                · subst hxn; rw [PanRunBounded.resVarEq_lookup, if_pos rfl]; exact hx
                · rw [PanRunBounded.resVarEq_lookup, if_neg hxn]
                  set resumed := setVarHOLFinite nm v { st with locals := s.locals }
                  have smallR : resumed.clock < s.clock := small
                  have hx' : ∃ w0 : BitVec 64, resumed.locals.lookup x = some (.val (.word w0)) := by
                    simp [resumed, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hxn, hx]
                  exact evaluate_preserves_word_local cont hc resumed hx' hout
              · intro h; simp [isNormalCtrl] at h
            | _ => intro h; simp [isNormalCtrl] at h
  | call rt fname args =>
    rcases rt with _ | ⟨dest, hdl⟩
    · rw [evaluateHOLFiniteState_call]
      rcases evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vals
      · intro h; simp [isNormalCtrl] at h
      · dsimp only
        rcases lookupCodeHOLFinite s.code.lookup fname vals with _ | ⟨body, callee, rs⟩
        · intro h; simp [isNormalCtrl] at h
        · dsimp only
          split
          · intro h; simp [isNormalCtrl] at h
          · rcases evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨res, st⟩
            cases res with
            | none => intro h; simp [isNormalCtrl] at h
            | some r =>
              cases r with
              | returned _ =>
                simp only []
                split <;> (intro h; simp [isNormalCtrl] at h)
              | _ => intro h; simp [isNormalCtrl] at h
    · rcases hdl with _ | _
      · rcases dest with _ | ⟨vk, nm⟩
        · rw [evaluateHOLFiniteState_call]
          rcases evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vals
          · intro _; exact hx
          · dsimp only
            rcases lookupCodeHOLFinite s.code.lookup fname vals with _ | ⟨body, callee, rs⟩
            · intro _; exact hx
            · dsimp only
              split
              · intro h; simp [isNormalCtrl] at h
              · rcases evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨res, st⟩
                cases res with
                | none => intro h; simp [isNormalCtrl] at h
                | some r =>
                  cases r with
                  | returned _ =>
                    simp only []
                    split
                    · intro _; exact hx
                    · intro h; simp [isNormalCtrl] at h
                  | _ => intro h; simp [isNormalCtrl] at h
        · cases vk with
          | global =>
            rw [evaluateHOLFiniteState_call]
            rcases evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vals
            · intro _; exact hx
            · dsimp only
              rcases lookupCodeHOLFinite s.code.lookup fname vals with _ | ⟨body, callee, rs⟩
              · intro _; exact hx
              · dsimp only
                split
                · intro h; simp [isNormalCtrl] at h
                · rcases evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨res, st⟩
                  cases res with
                  | none => intro h; simp [isNormalCtrl] at h
                  | some r =>
                    cases r with
                    | returned _ =>
                      simp only []
                      split
                      · split
                        · intro _; exact hx
                        · intro h; simp [isNormalCtrl] at h
                      · intro h; simp [isNormalCtrl] at h
                    | _ => intro h; simp [isNormalCtrl] at h
          | «local» =>
            rw [evaluateHOLFiniteState_call]
            rcases evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vals
            · intro _; exact hx
            · dsimp only
              rcases lookupCodeHOLFinite s.code.lookup fname vals with _ | ⟨body, callee, rs⟩
              · intro _; exact hx
              · dsimp only
                split
                · intro h; simp [isNormalCtrl] at h
                · rcases evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨res, st⟩
                  cases res with
                  | none => intro h; simp [isNormalCtrl] at h
                  | some r =>
                    cases r with
                    | returned v =>
                      simp only []
                      split
                      · split
                        · rename_i hvld
                          intro _
                          by_cases hnx : nm = x
                          · subst hnx
                            obtain ⟨w0, hw0⟩ := hx
                            obtain ⟨w, rfl⟩ := word_of_isValid_local hw0 hvld
                            exact ⟨w, by simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩
                          · simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hnx, hx]
                        · intro h; simp [isNormalCtrl] at h
                      · intro h; simp [isNormalCtrl] at h
                    | _ => intro h; simp [isNormalCtrl] at h
      · simp [shape, noPrimitiveOrHandledCall] at hnp
termination_by (s.clock, sizeOf p)
decreasing_by
  all_goals
    simp_wf
    apply GuestGlobalKeep.lex_of
    try subst shape
    try simp only [setVarHOLFinite, decClockHOLFinite, callEntryStateHOLFinite,
      ProgHOL.seq.sizeOf_spec, ProgHOL.ite.sizeOf_spec, ProgHOL.dec.sizeOf_spec,
      ProgHOL.while.sizeOf_spec, ProgHOL.decCall.sizeOf_spec, ProgHOL.call.sizeOf_spec, true_and]
    first
      | exact Or.inl smallR
      | exact Or.inl smaller
      | exact Or.inl small
      | omega
      | (rcases Nat.lt_or_eq_of_le mclock with h | h
         · exact Or.inl h
         · exact Or.inr ⟨h, by simp +arith⟩)
      | exact Or.inr ⟨rfl, by simp +arith⟩

theorem WsSafe.ro_preserving_locals {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    (he : WsEnv s0 s) {p : ProgHOL 64} {protectedVars : List MlS}
    (hro : readOnlyProg opRoCallees p = true)
    (hna : ∀ x ∈ protectedVars, notAssignedLocal x p = true) :
    WsSafe s (untypedGlobalBufIvls s0) (evaluateHOLFiniteState s p) ∧
    ((evaluateHOLFiniteState s p).1 = none →
      WsEnv s0 (evaluateHOLFiniteState s p).2 ∧
      ∀ x ∈ protectedVars, (evaluateHOLFiniteState s p).2.locals.lookup x = s.locals.lookup x) := by
  have hs := WsSafe.of_readOnly (s := s) (Rl := untypedGlobalBufIvls s0) he.code hro
  refine ⟨hs, fun hn => ⟨he.step (hs.1 hn), fun x hx => ?_⟩⟩
  exact evaluate_notAssignedLocal p (hna x hx) s (by simp [isNormalCtrl, hn])

theorem WsSafe.ro_preserving_word_and_locals {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    (he : WsEnv s0 s) {p : ProgHOL 64} {wVar : MlS}
    (hro : readOnlyProg opRoCallees p = true)
    (hnp : noPrimitiveOrHandledCall p = true)
    (hw : ∃ w0 : BitVec 64, s.locals.lookup wVar = some (.val (.word w0)))
    {keep : MlS → Prop}
    (hna : ∀ x, keep x → notAssignedLocal x p = true) :
    WsSafe s (untypedGlobalBufIvls s0) (evaluateHOLFiniteState s p) ∧
    ((evaluateHOLFiniteState s p).1 = none →
      WsEnv s0 (evaluateHOLFiniteState s p).2 ∧
      (∃ w : BitVec 64, (evaluateHOLFiniteState s p).2.locals.lookup wVar = some (.val (.word w))) ∧
      (∀ x, keep x → (evaluateHOLFiniteState s p).2.locals.lookup x = s.locals.lookup x)) := by
  have hs := WsSafe.of_readOnly (s := s) (Rl := untypedGlobalBufIvls s0) he.code hro
  refine ⟨hs, fun hn => ⟨he.step (hs.1 hn),
    evaluate_preserves_word_local p hnp s hw (by simp [isNormalCtrl, hn]),
    fun x hx => evaluate_notAssignedLocal p (hna x hx) s (by simp [isNormalCtrl, hn])⟩⟩

theorem divmnu_n1_loop_wsSafe {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    (he : WsEnv s0 s) {q_off m0 : Nat} {kw : BitVec 64}
    (hm_le : m0 ≤ 16) (hq_off : q_off + 16 * 8 ≤ 640)
    (hq : s.locals.lookup (ofString "q") = some (.val (.word (BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 q_off))))
    (hk : s.locals.lookup (ofString "k") = some (.val (.word kw)))
    (hj : s.locals.lookup (ofString "j") = some (.val (.word (BitVec.ofNat 64 m0)))) :
    let body := ProgHOL.seq
      (.assign .local (ofString "j") (.op .sub [.var .local (ofString "j"), .const 1#64]))
      (.decCall (ofString "qr") (.comb [.one, .one]) (ofString "div64by32")
        [.var .local (ofString "k"),
         .load .one (.op .add [.var .local (ofString "u"), .panop .mul [.var .local (ofString "j"), .const 8#64]]),
         .var .local (ofString "d")]
        (.seq
          (.store (.op .add [.var .local (ofString "q"), .panop .mul [.var .local (ofString "j"), .const 8#64]])
            (.rfield 0 (.var .local (ofString "qr"))))
          (.assign .local (ofString "k") (.rfield 1 (.var .local (ofString "qr"))))))
    let prog := ProgHOL.while (.cmp .lower (.const 0#64) (.var .local (ofString "j"))) body
    WsSafe s (untypedGlobalBufIvls s0) (evaluateHOLFiniteState s prog) ∧
    ((evaluateHOLFiniteState s prog).1 = none →
      WsEnv s0 (evaluateHOLFiniteState s prog).2 ∧
      (∃ kw' : BitVec 64, (evaluateHOLFiniteState s prog).2.locals.lookup (ofString "k") = some (.val (.word kw'))) ∧
      (∀ x, x ≠ ofString "j" → x ≠ ofString "k" →
        (evaluateHOLFiniteState s prog).2.locals.lookup x = s.locals.lookup x)) := by
  dsimp only
  let body := ProgHOL.seq
    (.assign .local (ofString "j") (.op .sub [.var .local (ofString "j"), .const 1#64]))
    (.decCall (ofString "qr") (.comb [.one, .one]) (ofString "div64by32")
      [.var .local (ofString "k"),
       .load .one (.op .add [.var .local (ofString "u"), .panop .mul [.var .local (ofString "j"), .const 8#64]]),
       .var .local (ofString "d")]
      (.seq
        (.store (.op .add [.var .local (ofString "q"), .panop .mul [.var .local (ofString "j"), .const 8#64]])
          (.rfield 0 (.var .local (ofString "qr"))))
        (.assign .local (ofString "k") (.rfield 1 (.var .local (ofString "qr"))))))
  let P : PanSemStateFiniteExact 64 F → Prop := fun t =>
    WsEnv s0 t ∧
    (∃ jv : Nat, jv ≤ m0 ∧ t.locals.lookup (ofString "j") = some (.val (.word (BitVec.ofNat 64 jv)))) ∧
    (∃ kv : BitVec 64, t.locals.lookup (ofString "k") = some (.val (.word kv))) ∧
    (∀ x, x ≠ ofString "j" → x ≠ ofString "k" → t.locals.lookup x = s.locals.lookup x)
  have hP0 : P s := ⟨he, ⟨m0, le_refl _, hj⟩, ⟨kw, hk⟩, fun _ _ _ => rfl⟩
  have hnb : noTopBreakContinue body = true := rfl
  have hstep : ∀ t w, P (decClockHOLFinite t) →
      @evalHOLFinite 64 F _ t (fun a => Classical.propDecidable (t.memaddrs a))
        (.cmp .lower (.const 0#64) (.var .local (ofString "j"))) = some (.val (.word w)) → w ≠ 0 →
      WsSafe (decClockHOLFinite t) (untypedGlobalBufIvls s0)
        (evaluateHOLFiniteState (decClockHOLFinite t) body) ∧
      ((evaluateHOLFiniteState (decClockHOLFinite t) body).1 = none →
        P (evaluateHOLFiniteState (decClockHOLFinite t) body).2) := by
    intro t w ⟨ht_env, ⟨jv, hj_le, hj_t⟩, ⟨kv, hk_t⟩, hother_t⟩ hcnd hw0
    have hj_t0 : t.locals.lookup (ofString "j") = some (.val (.word (BitVec.ofNat 64 jv))) := hj_t
    have hj_pos : 1 ≤ jv := by
      simp only [evalHOLFinite, evalHOLExact, hj_t0, wordCmpHOL, BitVec.lt_def,
        BitVec.toNat_ofNat, Nat.zero_mod, Nat.mod_eq_of_lt (show jv < 2 ^ 64 by omega)] at hcnd
      by_cases hp : 0 < jv
      · omega
      · simp [hp] at hcnd; exact absurd hcnd.symm hw0
    have hev_dec : @evalHOLExact 64 F _ (decClockHOLFinite t).toExact
        (fun a => Classical.propDecidable ((decClockHOLFinite t).memaddrs a))
        (.op .sub [.var .local (ofString "j"), .const 1#64]) =
        some (.val (.word (BitVec.ofNat 64 (jv - 1)))) := by
      simp only [evalHOLExact, evalListHOLExact, hj_t, wordOpHOL, wordOp,
        valueIsWord, valueWord, List.all, List.map, Bool.and_self, ↓reduceIte, Option.map]
      congr 3; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    have hasg1 := assign_local_step_eq ⟨_, hj_t⟩ hev_dec
    let s1 := setVarHOLFinite (ofString "j") (.val (.word (BitVec.ofNat 64 (jv - 1)))) (decClockHOLFinite t)
    have hs1_env : WsEnv s0 s1 := ht_env.with_locals_clock _ _
    have hdc_post : WsSafe s1 (untypedGlobalBufIvls s0)
        (evaluateHOLFiniteState s1
          (.decCall (ofString "qr") (.comb [.one, .one]) (ofString "div64by32")
            [.var .local (ofString "k"),
             .load .one (.op .add [.var .local (ofString "u"), .panop .mul [.var .local (ofString "j"), .const 8#64]]),
             .var .local (ofString "d")]
            (.seq
              (.store (.op .add [.var .local (ofString "q"), .panop .mul [.var .local (ofString "j"), .const 8#64]])
                (.rfield 0 (.var .local (ofString "qr"))))
              (.assign .local (ofString "k") (.rfield 1 (.var .local (ofString "qr"))))))) ∧
        ((evaluateHOLFiniteState s1
          (.decCall (ofString "qr") (.comb [.one, .one]) (ofString "div64by32")
            [.var .local (ofString "k"),
             .load .one (.op .add [.var .local (ofString "u"), .panop .mul [.var .local (ofString "j"), .const 8#64]]),
             .var .local (ofString "d")]
            (.seq
              (.store (.op .add [.var .local (ofString "q"), .panop .mul [.var .local (ofString "j"), .const 8#64]])
                (.rfield 0 (.var .local (ofString "qr"))))
              (.assign .local (ofString "k") (.rfield 1 (.var .local (ofString "qr"))))))).1 = none →
          P (evaluateHOLFiniteState s1
            (.decCall (ofString "qr") (.comb [.one, .one]) (ofString "div64by32")
              [.var .local (ofString "k"),
               .load .one (.op .add [.var .local (ofString "u"), .panop .mul [.var .local (ofString "j"), .const 8#64]]),
               .var .local (ofString "d")]
              (.seq
                (.store (.op .add [.var .local (ofString "q"), .panop .mul [.var .local (ofString "j"), .const 8#64]])
                  (.rfield 0 (.var .local (ofString "qr"))))
                (.assign .local (ofString "k") (.rfield 1 (.var .local (ofString "qr"))))))).2) := by
      refine WsSafe.decCall_ro_post hs1_env (by decide) ?_
      intro vqr cpost he_qr hsh_qr
      obtain ⟨q0, q1, rfl⟩ := eval_comb2_of_shape (Or.inr hsh_qr)
      let s2 := setVarHOLFinite (ofString "qr") (.rStruct [.val (.word q0), .val (.word q1)])
        { cpost with locals := s1.locals }
      have hq_s2 : s2.locals.lookup (ofString "q") =
          some (.val (.word (BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 q_off))) := by
        simp [s2, setVarHOLFinite, s1, FUPDATE, show ofString "qr" ≠ ofString "q" by decide,
          show ofString "j" ≠ ofString "q" by decide, hother_t (ofString "q") (by decide) (by decide), hq]
      have hj_s2 : s2.locals.lookup (ofString "j") = some (.val (.word (BitVec.ofNat 64 (jv - 1)))) := by
        simp [s2, setVarHOLFinite, s1, FUPDATE, show ofString "qr" ≠ ofString "j" by decide]
      have hqr_s2 : s2.locals.lookup (ofString "qr") = some (.rStruct [.val (.word q0), .val (.word q1)]) := by
        simp [s2, setVarHOLFinite, FUPDATE]
      have hst_s2 := WsSafe.store_ws_scaled he_qr
        (baseExp := .var .local (ofString "q"))
        (idxExp := .var .local (ofString "j"))
        (valExp := .rfield 0 (.var .local (ofString "qr")))
        (off := q_off) (idx := jv - 1)
        (by simp only [evalHOLExact]; exact hq_s2)
        (by simp only [evalHOLExact]; exact hj_s2)
        (by omega)
        (fun _ hv => eval_word_of_rfield_comb2 (idx := 0) hqr_s2 hv)
      refine ⟨WsSafe.seq hst_s2 (fun _ _ => WsSafe.assign_local _ _ _ _), fun hcn => ?_⟩
      have hloc_s2 := store_none_locals (s := s2)
        (dst := .op .add [.var .local (ofString "q"), .panop .mul [.var .local (ofString "j"), .const 8#64]])
        (val := .rfield 0 (.var .local (ofString "qr")))
      rw [evaluateHOLFiniteState_seq_line780] at hcn ⊢
      rcases hr_st : evaluateHOLFiniteState s2
        (.store (.op .add [.var .local (ofString "q"), .panop .mul [.var .local (ofString "j"), .const 8#64]])
          (.rfield 0 (.var .local (ofString "qr")))) with ⟨rst, s3⟩
      rw [hr_st] at hcn hst_s2 hloc_s2
      dsimp only at hcn hst_s2 hloc_s2 ⊢
      cases rst with
      | some _ => simp at hcn
      | none =>
        have hs3_env : WsEnv s0 s3 := he_qr.step (hst_s2.1 rfl)
        have hs3_loc : s3.locals = s2.locals := hloc_s2 rfl
        have hk_s3 : s3.locals.lookup (ofString "k") = some (.val (.word kv)) := by
          rw [hs3_loc]; simp [s2, setVarHOLFinite, s1, FUPDATE,
            show ofString "qr" ≠ ofString "k" by decide, show ofString "j" ≠ ofString "k" by decide, hk_t]
        have hqr_s3 : s3.locals.lookup (ofString "qr") = some (.rStruct [.val (.word q0), .val (.word q1)]) := by
          rw [hs3_loc]; exact hqr_s2
        have hev_q1 : @evalHOLExact 64 F _ s3.toExact
            (fun a => Classical.propDecidable (s3.memaddrs a))
            (.rfield 1 (.var .local (ofString "qr"))) = some (.val (.word q1)) := by
          simp [evalHOLExact, hqr_s3]
        have hasg_k := assign_local_step_eq ⟨_, hk_s3⟩ hev_q1
        rw [hasg_k]; dsimp only
        let s4 := setVarHOLFinite (ofString "k") (.val (.word q1)) s3
        refine ⟨hs3_env.with_locals_clock _ _,
          ⟨jv - 1, by omega, ?_⟩, ⟨q1, ?_⟩, ?_⟩
        · rw [PanRunBounded.resVarEq_lookup, if_neg (show ofString "j" ≠ ofString "qr" by decide)]
          simp [s4, setVarHOLFinite, hs3_loc, s2, s1, FUPDATE,
            show ofString "k" ≠ ofString "j" by decide,
            show ofString "qr" ≠ ofString "j" by decide]
        · rw [PanRunBounded.resVarEq_lookup, if_neg (show ofString "k" ≠ ofString "qr" by decide)]
          simp [s4, setVarHOLFinite, FUPDATE]
        · intro x hxj hxk
          rw [PanRunBounded.resVarEq_lookup]
          by_cases hxq : x = ofString "qr"
          · subst hxq; simp only [↓reduceIte, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "j" ≠ ofString "qr" by decide]
            exact hother_t (ofString "qr") (by decide) (by decide)
          · simp [hxq, Ne.symm hxq, s4, setVarHOLFinite, hs3_loc, s2, s1, FUPDATE,
              Ne.symm hxk, Ne.symm hxj, hother_t x hxj hxk]
    refine ⟨?_, ?_⟩
    · refine WsSafe.seq (WsSafe.assign_local _ _ _ _) ?_
      intro _ _; rw [congrArg Prod.snd hasg1]; exact hdc_post.1
    · intro hbn
      dsimp only [body] at hbn ⊢
      rw [evaluateHOLFiniteState_seq_line780, hasg1] at hbn ⊢
      exact hdc_post.2 hbn
  have hpost := WsSafe.while_loop_post hnb P
    (fun t ⟨h1, h2, h3, h4⟩ => ⟨⟨h1.code, h1.memaddrs, h1.globals, h1.ws_bnd⟩, h2, h3, h4⟩)
    hstep s hP0
  exact ⟨hpost.1, fun hn => ⟨(hpost.2 hn).1, (hpost.2 hn).2.2.1, (hpost.2 hn).2.2.2⟩⟩

theorem WsSafe.seq_post' {F : Type} {s : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (Q : PanSemStateFiniteExact 64 F → Prop)
    (P1 : PanSemStateFiniteExact 64 F → Prop)
    {p1 p2 : ProgHOL 64}
    (h1 : WsSafe s Rl (evaluateHOLFiniteState s p1) ∧
          ((evaluateHOLFiniteState s p1).1 = none → P1 (evaluateHOLFiniteState s p1).2))
    (h2 : ∀ s1, P1 s1 →
      WsSafe s1 Rl (evaluateHOLFiniteState s1 p2) ∧
      ((evaluateHOLFiniteState s1 p2).1 = none → Q (evaluateHOLFiniteState s1 p2).2)) :
    WsSafe s Rl (evaluateHOLFiniteState s (.seq p1 p2)) ∧
    ((evaluateHOLFiniteState s (.seq p1 p2)).1 = none →
      Q (evaluateHOLFiniteState s (.seq p1 p2)).2) :=
  WsSafe.seq_post h1 h2

/-- Store to `baseExp + idxExp * 8` within `u256_ws` with postcondition propagation. -/
theorem WsSafe.store_ws_scaled_post {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    (he : WsEnv s0 s) {baseExp idxExp valExp : ExpHOL 64} {off idx : Nat}
    (hbase : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) baseExp =
      some (.val (.word (BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 off))))
    (hidx : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) idxExp =
      some (.val (.word (BitVec.ofNat 64 idx))))
    (hoff : off + idx * 8 + 8 ≤ 640)
    (hval : isWordValExp valExp = true) :
    WsSafe s (untypedGlobalBufIvls s0)
      (evaluateHOLFiniteState s (.store (.op .add [baseExp, .panop .mul [idxExp, .const 8#64]]) valExp)) ∧
    ((evaluateHOLFiniteState s (.store (.op .add [baseExp, .panop .mul [idxExp, .const 8#64]]) valExp)).1 = none →
      WsEnv s0 (evaluateHOLFiniteState s (.store (.op .add [baseExp, .panop .mul [idxExp, .const 8#64]]) valExp)).2 ∧
      (evaluateHOLFiniteState s (.store (.op .add [baseExp, .panop .mul [idxExp, .const 8#64]]) valExp)).2.locals = s.locals) := by
  have hs := WsSafe.store_ws_scaled he hbase hidx hoff (fun _ hv => eval_word_of_isWordValExp hval hv)
  exact ⟨hs, fun hn => ⟨he.step (hs.1 hn), store_none_locals hn⟩⟩

/-- Store to `dst` at constant offset within `u256_ws` with postcondition propagation. -/
theorem WsSafe.store_ws_const_off_post {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    (he : WsEnv s0 s) {dst valExp : ExpHOL 64} {off : Nat}
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dst =
      some (.val (.word (BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 off))))
    (hoff : off + 8 ≤ 640)
    (hval : isWordValExp valExp = true) :
    WsSafe s (untypedGlobalBufIvls s0) (evaluateHOLFiniteState s (.store dst valExp)) ∧
    ((evaluateHOLFiniteState s (.store dst valExp)).1 = none →
      WsEnv s0 (evaluateHOLFiniteState s (.store dst valExp)).2 ∧
      (evaluateHOLFiniteState s (.store dst valExp)).2.locals = s.locals) := by
  have hs := WsSafe.store_ws_const_off he hdst hoff (fun _ hv => eval_word_of_isWordValExp hval hv)
  exact ⟨hs, fun hn => ⟨he.step (hs.1 hn), store_none_locals hn⟩⟩

/-- Helper for `while (i < n)` loops in `divmnu` that wrap the `un + (i+j)*8` store in
`dec` locals (`p`,`t` or `t2`) and update `k` and `i := i + 1`. -/
theorem divmnu_submul_loop_wsSafe {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    (he : WsEnv s0 s) {jv nv : Nat}
    (hun : s.locals.lookup (ofString "un") =
      some (.val (.word (BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 0))))
    (hj : s.locals.lookup (ofString "j") = some (.val (.word (BitVec.ofNat 64 jv))))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 nv))))
    (hi0 : s.locals.lookup (ofString "i") = some (.val (.word 0#64)))
    (hk0 : ∃ kv : BitVec 64, s.locals.lookup (ofString "k") = some (.val (.word kv)))
    (hn_le : nv ≤ 8) (hjn_le : jv + nv ≤ 16) :
    let body := ProgHOL.dec (ofString "p") .one
      (.panop .mul [.var .local (ofString "qhat"),
        .load .one (.op .add [.var .local (ofString "vn"),
          .panop .mul [.var .local (ofString "i"), .const 8#64]])])
      (.dec (ofString "t") .one
        (.op .sub [.op .sub [
          .load .one (.op .add [.var .local (ofString "un"),
            .panop .mul [.op .add [.var .local (ofString "i"), .var .local (ofString "j")], .const 8#64]]),
          .var .local (ofString "k")],
          .op .and [.var .local (ofString "p"), .const 4294967295#64]])
        (.seq
          (.store (.op .add [.var .local (ofString "un"),
              .panop .mul [.op .add [.var .local (ofString "i"), .var .local (ofString "j")], .const 8#64]])
            (.op .and [.var .local (ofString "t"), .const 4294967295#64]))
          (.seq
            (.assign .local (ofString "k")
              (.op .sub [.shift .lsr (.var .local (ofString "p")) (.const 32#64),
                         .shift .asr (.var .local (ofString "t")) (.const 32#64)]))
            (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1#64])))))
    let prog := ProgHOL.while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) body
    WsSafe s (untypedGlobalBufIvls s0) (evaluateHOLFiniteState s prog) ∧
    ((evaluateHOLFiniteState s prog).1 = none →
      WsEnv s0 (evaluateHOLFiniteState s prog).2 ∧
      (∃ iv : Nat, (evaluateHOLFiniteState s prog).2.locals.lookup (ofString "i") =
        some (.val (.word (BitVec.ofNat 64 iv)))) ∧
      (∃ kv : BitVec 64, (evaluateHOLFiniteState s prog).2.locals.lookup (ofString "k") =
        some (.val (.word kv))) ∧
      (∀ x, x ≠ ofString "i" → x ≠ ofString "k" →
        (evaluateHOLFiniteState s prog).2.locals.lookup x = s.locals.lookup x)) := by
  dsimp only
  let body := ProgHOL.dec (ofString "p") .one
    (.panop .mul [.var .local (ofString "qhat"),
      .load .one (.op .add [.var .local (ofString "vn"),
        .panop .mul [.var .local (ofString "i"), .const 8#64]])])
    (.dec (ofString "t") .one
      (.op .sub [.op .sub [
        .load .one (.op .add [.var .local (ofString "un"),
          .panop .mul [.op .add [.var .local (ofString "i"), .var .local (ofString "j")], .const 8#64]]),
        .var .local (ofString "k")],
        .op .and [.var .local (ofString "p"), .const 4294967295#64]])
      (.seq
        (.store (.op .add [.var .local (ofString "un"),
            .panop .mul [.op .add [.var .local (ofString "i"), .var .local (ofString "j")], .const 8#64]])
          (.op .and [.var .local (ofString "t"), .const 4294967295#64]))
        (.seq
          (.assign .local (ofString "k")
            (.op .sub [.shift .lsr (.var .local (ofString "p")) (.const 32#64),
                       .shift .asr (.var .local (ofString "t")) (.const 32#64)]))
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1#64])))))
  let P : PanSemStateFiniteExact 64 F → Prop := fun st =>
    WsEnv s0 st ∧
    (∃ iv : Nat, iv ≤ nv ∧ st.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 iv)))) ∧
    (∃ kv : BitVec 64, st.locals.lookup (ofString "k") = some (.val (.word kv))) ∧
    (∀ x, x ≠ ofString "i" → x ≠ ofString "k" → st.locals.lookup x = s.locals.lookup x)
  have hP0 : P s := ⟨he, ⟨0, by omega, hi0⟩, hk0, fun _ _ _ => rfl⟩
  have hnb : noTopBreakContinue body = true := rfl
  have hstep : ∀ st w, P (decClockHOLFinite st) →
      @evalHOLFinite 64 F _ st (fun a => Classical.propDecidable (st.memaddrs a))
        (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) =
        some (.val (.word w)) → w ≠ 0 →
      WsSafe (decClockHOLFinite st) (untypedGlobalBufIvls s0)
        (evaluateHOLFiniteState (decClockHOLFinite st) body) ∧
      ((evaluateHOLFiniteState (decClockHOLFinite st) body).1 = none →
        P (evaluateHOLFiniteState (decClockHOLFinite st) body).2) := by
    intro st w ⟨hst_env, ⟨iv, hiv_le, hi_st⟩, ⟨kv, hk_st⟩, hother_st⟩ hcnd hw0
    have hi_st0 : st.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 iv))) := hi_st
    have hn_st0 : st.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 nv))) := by
      change (decClockHOLFinite st).locals.lookup (ofString "n") = _
      rw [hother_st (ofString "n") (by decide) (by decide)]; exact hn
    have hiv_lt : iv < nv := by
      simp only [evalHOLFinite, evalHOLExact, hi_st0, hn_st0, wordCmpHOL, BitVec.lt_def,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show iv < 2 ^ 64 by omega),
        Nat.mod_eq_of_lt (show nv < 2 ^ 64 by omega)] at hcnd
      by_cases hlt : iv < nv
      · exact hlt
      · simp [hlt] at hcnd; exact absurd hcnd.symm hw0
    refine WsSafe.dec_post (Q := P) fun vp hvp hshp => ?_
    obtain ⟨wp, rfl⟩ := eval_word_of_isWordValExp (s := decClockHOLFinite st) rfl hvp
    set s1 := setVarHOLFinite (ofString "p") (.val (.word wp)) (decClockHOLFinite st)
    have hs1_env : WsEnv s0 s1 := hst_env.with_locals_clock _ _
    refine WsSafe.dec_post
      (Q := fun sp => P (restoreLocal (ofString "p") ((decClockHOLFinite st).locals.lookup (ofString "p")) sp))
      fun vt hvt hsht => ?_
    obtain ⟨wt, rfl⟩ := eval_word_of_isWordValExp (s := s1) rfl hvt
    set s2 := setVarHOLFinite (ofString "t") (.val (.word wt)) s1
    have hs2_env : WsEnv s0 s2 := hs1_env.with_locals_clock _ _
    have hun_s2 : s2.locals.lookup (ofString "un") =
        some (.val (.word (BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 0))) := by
      simp [s2, s1, setVarHOLFinite, FUPDATE,
        show ofString "t" ≠ ofString "un" by decide,
        show ofString "p" ≠ ofString "un" by decide,
        hother_st (ofString "un") (by decide) (by decide), hun]
    have hi_s2 : s2.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 iv))) := by
      simp [s2, s1, setVarHOLFinite, FUPDATE,
        show ofString "t" ≠ ofString "i" by decide,
        show ofString "p" ≠ ofString "i" by decide, hi_st]
    have hj_s2 : s2.locals.lookup (ofString "j") = some (.val (.word (BitVec.ofNat 64 jv))) := by
      simp [s2, s1, setVarHOLFinite, FUPDATE,
        show ofString "t" ≠ ofString "j" by decide,
        show ofString "p" ≠ ofString "j" by decide,
        hother_st (ofString "j") (by decide) (by decide), hj]
    have hev_ij : @evalHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a))
        (.op .add [.var .local (ofString "i"), .var .local (ofString "j")]) =
        some (.val (.word (BitVec.ofNat 64 (iv + jv)))) := by
      simp only [evalHOLExact, evalListHOLExact, hi_s2, hj_s2, wordOpHOL, wordOp,
        valueIsWord, valueWord, List.all, List.map, Bool.and_self, ↓reduceIte, Option.map, List.foldr]
      congr 3
      rw [show (BitVec.ofNat 64 jv + 0 : BitVec 64) = BitVec.ofNat 64 jv from BitVec.add_zero _]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    apply WsSafe.seq_post'
      (fun sp2 => P (restoreLocal (ofString "p") ((decClockHOLFinite st).locals.lookup (ofString "p"))
                      (restoreLocal (ofString "t") (s1.locals.lookup (ofString "t")) sp2)))
      (fun s3 => WsEnv s0 s3 ∧ s3.locals = s2.locals)
    · exact WsSafe.store_ws_scaled_post hs2_env
        (baseExp := .var .local (ofString "un"))
        (idxExp := .op .add [.var .local (ofString "i"), .var .local (ofString "j")])
        (valExp := .op .and [.var .local (ofString "t"), .const 4294967295#64])
        (off := 0) (idx := iv + jv)
        (by simp only [evalHOLExact]; exact hun_s2) hev_ij (by omega) rfl
    intro s3 ⟨hs3_env, hs3_loc⟩
    have hk_s3 : s3.locals.lookup (ofString "k") = some (.val (.word kv)) := by
      rw [hs3_loc]; simp [s2, s1, setVarHOLFinite, FUPDATE,
        show ofString "t" ≠ ofString "k" by decide,
        show ofString "p" ≠ ofString "k" by decide, hk_st]
    apply WsSafe.seq_post'
      (fun sp2 => P (restoreLocal (ofString "p") ((decClockHOLFinite st).locals.lookup (ofString "p"))
                      (restoreLocal (ofString "t") (s1.locals.lookup (ofString "t")) sp2)))
      (fun s4 => WsEnv s0 s4 ∧
        ∃ kw' : BitVec 64, s4 = setVarHOLFinite (ofString "k") (.val (.word kw')) s3)
    · exact WsSafe.assign_word_post
        (Q := fun s4 => WsEnv s0 s4 ∧
          ∃ kw' : BitVec 64, s4 = setVarHOLFinite (ofString "k") (.val (.word kw')) s3)
        hs3_env ⟨kv, hk_s3⟩
        (fun kw' _ => ⟨hs3_env.with_locals_clock _ _, kw', rfl⟩)
        (fun _ hv => eval_word_of_isWordValExp rfl hv)
    intro s4 ⟨hs4_env, kw', hs4_eq⟩
    subst hs4_eq
    have hi_s4 : (setVarHOLFinite (ofString "k") (.val (.word kw')) s3).locals.lookup (ofString "i") =
        some (.val (.word (BitVec.ofNat 64 iv))) := by
      simp [setVarHOLFinite, FUPDATE, show ofString "k" ≠ ofString "i" by decide, hs3_loc, hi_s2]
    refine WsSafe.assign_word_post
      (Q := fun sp2 => P (restoreLocal (ofString "p") ((decClockHOLFinite st).locals.lookup (ofString "p"))
                      (restoreLocal (ofString "t") (s1.locals.lookup (ofString "t")) sp2)))
      hs4_env ⟨_, hi_s4⟩
      (fun wi hwi => ?_) (fun _ hv => eval_word_of_isWordValExp rfl hv)
    have hwi_eq : wi = BitVec.ofNat 64 (iv + 1) := by
      simp only [evalHOLExact, evalListHOLExact, hi_s4, wordOpHOL, wordOp,
        valueIsWord, valueWord, List.all, List.map, Bool.and_self, ↓reduceIte, Option.map, List.foldr] at hwi
      injection hwi with hwi'; injection hwi' with hwi''; injection hwi'' with hwi'''
      rw [← hwi''', show (1#64 + 0 : BitVec 64) = 1#64 from BitVec.add_zero _]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    subst hwi_eq
    let s5 := setVarHOLFinite (ofString "i") (.val (.word (BitVec.ofNat 64 (iv + 1))))
      (setVarHOLFinite (ofString "k") (.val (.word kw')) s3)
    refine ⟨hs4_env.with_locals_clock _ _, ⟨iv + 1, by omega, ?_⟩, ⟨kw', ?_⟩, ?_⟩
    · rw [PanRunBounded.resVarEq_lookup, if_neg (show ofString "i" ≠ ofString "p" by decide),
          PanRunBounded.resVarEq_lookup, if_neg (show ofString "i" ≠ ofString "t" by decide)]
      simp [s5, setVarHOLFinite, FUPDATE]
    · rw [PanRunBounded.resVarEq_lookup, if_neg (show ofString "k" ≠ ofString "p" by decide),
          PanRunBounded.resVarEq_lookup, if_neg (show ofString "k" ≠ ofString "t" by decide)]
      simp [s5, setVarHOLFinite, FUPDATE, show ofString "i" ≠ ofString "k" by decide]
    · intro x hxi hxk
      rw [PanRunBounded.resVarEq_lookup]
      by_cases hxp : x = ofString "p"
      · subst hxp; simp only [↓reduceIte]; exact hother_st (ofString "p") (by decide) (by decide)
      · rw [if_neg hxp, PanRunBounded.resVarEq_lookup]
        by_cases hxt : x = ofString "t"
        · subst hxt; simp only [↓reduceIte, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "p" ≠ ofString "t" by decide]
          exact hother_st (ofString "t") (by decide) (by decide)
        · rw [if_neg hxt]
          simp [s5, setVarHOLFinite, hs3_loc, s2, s1, HolFiniteMapExact.lookup_update, FUPDATE,
            Ne.symm hxi, Ne.symm hxk, Ne.symm hxt, Ne.symm hxp, hother_st x hxi hxk]
  have hpost := WsSafe.while_loop_post hnb P
    (fun t ⟨h1, h2, h3, h4⟩ => ⟨⟨h1.code, h1.memaddrs, h1.globals, h1.ws_bnd⟩, h2, h3, h4⟩)
    hstep s hP0
  exact ⟨hpost.1, fun hn =>
    ⟨(hpost.2 hn).1, ⟨(hpost.2 hn).2.1.choose, (hpost.2 hn).2.1.choose_spec.2⟩,
     (hpost.2 hn).2.2.1, (hpost.2 hn).2.2.2⟩⟩

/-- Helper for the add-back `while (i < n)` loop in `divmnu` (`tt <s 0` branch). -/
theorem divmnu_addback_loop_wsSafe {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    (he : WsEnv s0 s) {jv nv : Nat}
    (hun : s.locals.lookup (ofString "un") =
      some (.val (.word (BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 0))))
    (hj : s.locals.lookup (ofString "j") = some (.val (.word (BitVec.ofNat 64 jv))))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 nv))))
    (hi0 : s.locals.lookup (ofString "i") = some (.val (.word 0#64)))
    (hk0 : ∃ kv : BitVec 64, s.locals.lookup (ofString "k") = some (.val (.word kv)))
    (hn_le : nv ≤ 8) (hjn_le : jv + nv ≤ 16) :
    let body := ProgHOL.dec (ofString "t2") .one
      (.op .add [
        .load .one (.op .add [.var .local (ofString "un"),
          .panop .mul [.op .add [.var .local (ofString "i"), .var .local (ofString "j")], .const 8#64]]),
        .load .one (.op .add [.var .local (ofString "vn"),
          .panop .mul [.var .local (ofString "i"), .const 8#64]]),
        .var .local (ofString "k")])
      (.seq
        (.store (.op .add [.var .local (ofString "un"),
            .panop .mul [.op .add [.var .local (ofString "i"), .var .local (ofString "j")], .const 8#64]])
          (.op .and [.var .local (ofString "t2"), .const 4294967295#64]))
        (.seq
          (.assign .local (ofString "k") (.shift .lsr (.var .local (ofString "t2")) (.const 32#64)))
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1#64]))))
    let prog := ProgHOL.while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) body
    WsSafe s (untypedGlobalBufIvls s0) (evaluateHOLFiniteState s prog) ∧
    ((evaluateHOLFiniteState s prog).1 = none →
      WsEnv s0 (evaluateHOLFiniteState s prog).2 ∧
      (∃ iv : Nat, (evaluateHOLFiniteState s prog).2.locals.lookup (ofString "i") =
        some (.val (.word (BitVec.ofNat 64 iv)))) ∧
      (∃ kv : BitVec 64, (evaluateHOLFiniteState s prog).2.locals.lookup (ofString "k") =
        some (.val (.word kv))) ∧
      (∀ x, x ≠ ofString "i" → x ≠ ofString "k" →
        (evaluateHOLFiniteState s prog).2.locals.lookup x = s.locals.lookup x)) := by
  dsimp only
  let body := ProgHOL.dec (ofString "t2") .one
    (.op .add [
      .load .one (.op .add [.var .local (ofString "un"),
        .panop .mul [.op .add [.var .local (ofString "i"), .var .local (ofString "j")], .const 8#64]]),
      .load .one (.op .add [.var .local (ofString "vn"),
        .panop .mul [.var .local (ofString "i"), .const 8#64]]),
      .var .local (ofString "k")])
    (.seq
      (.store (.op .add [.var .local (ofString "un"),
          .panop .mul [.op .add [.var .local (ofString "i"), .var .local (ofString "j")], .const 8#64]])
        (.op .and [.var .local (ofString "t2"), .const 4294967295#64]))
      (.seq
        (.assign .local (ofString "k") (.shift .lsr (.var .local (ofString "t2")) (.const 32#64)))
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1#64]))))
  let P : PanSemStateFiniteExact 64 F → Prop := fun st =>
    WsEnv s0 st ∧
    (∃ iv : Nat, iv ≤ nv ∧ st.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 iv)))) ∧
    (∃ kv : BitVec 64, st.locals.lookup (ofString "k") = some (.val (.word kv))) ∧
    (∀ x, x ≠ ofString "i" → x ≠ ofString "k" → st.locals.lookup x = s.locals.lookup x)
  have hP0 : P s := ⟨he, ⟨0, by omega, hi0⟩, hk0, fun _ _ _ => rfl⟩
  have hnb : noTopBreakContinue body = true := rfl
  have hstep : ∀ st w, P (decClockHOLFinite st) →
      @evalHOLFinite 64 F _ st (fun a => Classical.propDecidable (st.memaddrs a))
        (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) =
        some (.val (.word w)) → w ≠ 0 →
      WsSafe (decClockHOLFinite st) (untypedGlobalBufIvls s0)
        (evaluateHOLFiniteState (decClockHOLFinite st) body) ∧
      ((evaluateHOLFiniteState (decClockHOLFinite st) body).1 = none →
        P (evaluateHOLFiniteState (decClockHOLFinite st) body).2) := by
    intro st w ⟨hst_env, ⟨iv, hiv_le, hi_st⟩, ⟨kv, hk_st⟩, hother_st⟩ hcnd hw0
    have hi_st0 : st.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 iv))) := hi_st
    have hn_st0 : st.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 nv))) := by
      change (decClockHOLFinite st).locals.lookup (ofString "n") = _
      rw [hother_st (ofString "n") (by decide) (by decide)]; exact hn
    have hiv_lt : iv < nv := by
      simp only [evalHOLFinite, evalHOLExact, hi_st0, hn_st0, wordCmpHOL, BitVec.lt_def,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show iv < 2 ^ 64 by omega),
        Nat.mod_eq_of_lt (show nv < 2 ^ 64 by omega)] at hcnd
      by_cases hlt : iv < nv
      · exact hlt
      · simp [hlt] at hcnd; exact absurd hcnd.symm hw0
    refine WsSafe.dec_post (Q := P) fun vt hvt hsht => ?_
    obtain ⟨wt, rfl⟩ := eval_word_of_isWordValExp (s := decClockHOLFinite st) rfl hvt
    set s2 := setVarHOLFinite (ofString "t2") (.val (.word wt)) (decClockHOLFinite st)
    have hs2_env : WsEnv s0 s2 := hst_env.with_locals_clock _ _
    have hun_s2 : s2.locals.lookup (ofString "un") =
        some (.val (.word (BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 0))) := by
      simp [s2, setVarHOLFinite, FUPDATE,
        show ofString "t2" ≠ ofString "un" by decide,
        hother_st (ofString "un") (by decide) (by decide), hun]
    have hi_s2 : s2.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 iv))) := by
      simp [s2, setVarHOLFinite, FUPDATE,
        show ofString "t2" ≠ ofString "i" by decide, hi_st]
    have hj_s2 : s2.locals.lookup (ofString "j") = some (.val (.word (BitVec.ofNat 64 jv))) := by
      simp [s2, setVarHOLFinite, FUPDATE,
        show ofString "t2" ≠ ofString "j" by decide,
        hother_st (ofString "j") (by decide) (by decide), hj]
    have hev_ij : @evalHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a))
        (.op .add [.var .local (ofString "i"), .var .local (ofString "j")]) =
        some (.val (.word (BitVec.ofNat 64 (iv + jv)))) := by
      simp only [evalHOLExact, evalListHOLExact, hi_s2, hj_s2, wordOpHOL, wordOp,
        valueIsWord, valueWord, List.all, List.map, Bool.and_self, ↓reduceIte, Option.map, List.foldr]
      congr 3
      rw [show (BitVec.ofNat 64 jv + 0 : BitVec 64) = BitVec.ofNat 64 jv from BitVec.add_zero _]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    apply WsSafe.seq_post'
      (fun sp2 => P (restoreLocal (ofString "t2") ((decClockHOLFinite st).locals.lookup (ofString "t2")) sp2))
      (fun s3 => WsEnv s0 s3 ∧ s3.locals = s2.locals)
    · exact WsSafe.store_ws_scaled_post hs2_env
        (baseExp := .var .local (ofString "un"))
        (idxExp := .op .add [.var .local (ofString "i"), .var .local (ofString "j")])
        (valExp := .op .and [.var .local (ofString "t2"), .const 4294967295#64])
        (off := 0) (idx := iv + jv)
        (by simp only [evalHOLExact]; exact hun_s2) hev_ij (by omega) rfl
    intro s3 ⟨hs3_env, hs3_loc⟩
    have hk_s3 : s3.locals.lookup (ofString "k") = some (.val (.word kv)) := by
      rw [hs3_loc]; simp [s2, setVarHOLFinite, FUPDATE,
        show ofString "t2" ≠ ofString "k" by decide, hk_st]
    apply WsSafe.seq_post'
      (fun sp2 => P (restoreLocal (ofString "t2") ((decClockHOLFinite st).locals.lookup (ofString "t2")) sp2))
      (fun s4 => WsEnv s0 s4 ∧
        ∃ kw' : BitVec 64, s4 = setVarHOLFinite (ofString "k") (.val (.word kw')) s3)
    · exact WsSafe.assign_word_post
        (Q := fun s4 => WsEnv s0 s4 ∧
          ∃ kw' : BitVec 64, s4 = setVarHOLFinite (ofString "k") (.val (.word kw')) s3)
        hs3_env ⟨kv, hk_s3⟩
        (fun kw' _ => ⟨hs3_env.with_locals_clock _ _, kw', rfl⟩)
        (fun _ hv => eval_word_of_isWordValExp rfl hv)
    intro s4 ⟨hs4_env, kw', hs4_eq⟩
    subst hs4_eq
    have hi_s4 : (setVarHOLFinite (ofString "k") (.val (.word kw')) s3).locals.lookup (ofString "i") =
        some (.val (.word (BitVec.ofNat 64 iv))) := by
      simp [setVarHOLFinite, FUPDATE, show ofString "k" ≠ ofString "i" by decide, hs3_loc, hi_s2]
    refine WsSafe.assign_word_post
      (Q := fun sp2 => P (restoreLocal (ofString "t2") ((decClockHOLFinite st).locals.lookup (ofString "t2")) sp2))
      hs4_env ⟨_, hi_s4⟩
      (fun wi hwi => ?_) (fun _ hv => eval_word_of_isWordValExp rfl hv)
    have hwi_eq : wi = BitVec.ofNat 64 (iv + 1) := by
      simp only [evalHOLExact, evalListHOLExact, hi_s4, wordOpHOL, wordOp,
        valueIsWord, valueWord, List.all, List.map, Bool.and_self, ↓reduceIte, Option.map, List.foldr] at hwi
      injection hwi with hwi'; injection hwi' with hwi''; injection hwi'' with hwi'''
      rw [← hwi''', show (1#64 + 0 : BitVec 64) = 1#64 from BitVec.add_zero _]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    subst hwi_eq
    let s5 := setVarHOLFinite (ofString "i") (.val (.word (BitVec.ofNat 64 (iv + 1))))
      (setVarHOLFinite (ofString "k") (.val (.word kw')) s3)
    refine ⟨hs4_env.with_locals_clock _ _, ⟨iv + 1, by omega, ?_⟩, ⟨kw', ?_⟩, ?_⟩
    · rw [PanRunBounded.resVarEq_lookup, if_neg (show ofString "i" ≠ ofString "t2" by decide)]
      simp [s5, setVarHOLFinite, FUPDATE]
    · rw [PanRunBounded.resVarEq_lookup, if_neg (show ofString "k" ≠ ofString "t2" by decide)]
      simp [s5, setVarHOLFinite, FUPDATE, show ofString "i" ≠ ofString "k" by decide]
    · intro x hxi hxk
      rw [PanRunBounded.resVarEq_lookup]
      by_cases hxt : x = ofString "t2"
      · subst hxt; simp only [↓reduceIte]; exact hother_st (ofString "t2") (by decide) (by decide)
      · rw [if_neg hxt]
        simp [s5, setVarHOLFinite, hs3_loc, s2, HolFiniteMapExact.lookup_update, FUPDATE,
          Ne.symm hxi, Ne.symm hxk, Ne.symm hxt, hother_st x hxi hxk]
  have hpost := WsSafe.while_loop_post hnb P
    (fun t ⟨h1, h2, h3, h4⟩ => ⟨⟨h1.code, h1.memaddrs, h1.globals, h1.ws_bnd⟩, h2, h3, h4⟩)
    hstep s hP0
  exact ⟨hpost.1, fun hn =>
    ⟨(hpost.2 hn).1, ⟨(hpost.2 hn).2.1.choose, (hpost.2 hn).2.1.choose_spec.2⟩,
     (hpost.2 hn).2.2.1, (hpost.2 hn).2.2.2⟩⟩

private def divmnuOuterLoopBodyAST : Flapjack.Prog (BitVec 64) :=
  Prog.seq
    (Prog.assign VarKind.local "j" (Exp.op BinOp.sub [(Exp.var VarKind.local "j"), (Exp.const (BitVec.ofNat 64 1))]))
    (Prog.dec "ujn" Shape.one (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "un"), (Exp.panOp PanOp.mul [(Exp.op BinOp.add [(Exp.var VarKind.local "j"), (Exp.var VarKind.local "n")]), (Exp.const (BitVec.ofNat 64 8))])]))
      (Prog.dec "ujn1" Shape.one (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "un"), (Exp.panOp PanOp.mul [(Exp.op BinOp.sub [(Exp.op BinOp.add [(Exp.var VarKind.local "j"), (Exp.var VarKind.local "n")]), (Exp.const (BitVec.ofNat 64 1))]), (Exp.const (BitVec.ofNat 64 8))])]))
        (Prog.dec "ujn2" Shape.one (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "un"), (Exp.panOp PanOp.mul [(Exp.op BinOp.sub [(Exp.op BinOp.add [(Exp.var VarKind.local "j"), (Exp.var VarKind.local "n")]), (Exp.const (BitVec.ofNat 64 2))]), (Exp.const (BitVec.ofNat 64 8))])]))
          (Prog.dec "qhat" Shape.one (Exp.const (BitVec.ofNat 64 0))
            (Prog.dec "rhat" Shape.one (Exp.const (BitVec.ofNat 64 0))
              (Prog.seq
                (Prog.ite (Exp.cmp Cmp.notLower (Exp.var VarKind.local "ujn") (Exp.var VarKind.local "vtop"))
                  (Prog.seq
                    (Prog.assign VarKind.local "qhat" (Exp.const (BitVec.ofNat 64 4294967295)))
                    (Prog.assign VarKind.local "rhat" (Exp.op BinOp.sub [(Exp.op BinOp.or [(Exp.shift Shift.lsl (Exp.var VarKind.local "ujn") (Exp.const (BitVec.ofNat 64 32))), (Exp.var VarKind.local "ujn1")]), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "qhat"), (Exp.var VarKind.local "vtop")])])))
                  (Prog.decCall "qr" (Shape.comb [Shape.one, Shape.one]) "div64by32" [(Exp.var VarKind.local "ujn"), (Exp.var VarKind.local "ujn1"), (Exp.var VarKind.local "vtop")]
                    (Prog.seq
                      (Prog.assign VarKind.local "qhat" (Exp.rField 0 (Exp.var VarKind.local "qr")))
                      (Prog.assign VarKind.local "rhat" (Exp.rField 1 (Exp.var VarKind.local "qr"))))))
                (Prog.dec "again" Shape.one (Exp.const (BitVec.ofNat 64 1))
                  (Prog.seq
                    (Prog.while (Exp.cmp Cmp.equal (Exp.var VarKind.local "again") (Exp.const (BitVec.ofNat 64 1)))
                      (Prog.seq
                        (Prog.assign VarKind.local "again" (Exp.const (BitVec.ofNat 64 0)))
                        (Prog.ite (Exp.cmp Cmp.lower (Exp.var VarKind.local "rhat") (Exp.const (BitVec.ofNat 64 4294967296)))
                          (Prog.ite (Exp.cmp Cmp.lower (Exp.op BinOp.or [(Exp.shift Shift.lsl (Exp.var VarKind.local "rhat") (Exp.const (BitVec.ofNat 64 32))), (Exp.var VarKind.local "ujn2")]) (Exp.panOp PanOp.mul [(Exp.var VarKind.local "qhat"), (Exp.var VarKind.local "vsec")]))
                            (Prog.seq
                              (Prog.assign VarKind.local "qhat" (Exp.op BinOp.sub [(Exp.var VarKind.local "qhat"), (Exp.const (BitVec.ofNat 64 1))]))
                              (Prog.seq
                              (Prog.assign VarKind.local "rhat" (Exp.op BinOp.add [(Exp.var VarKind.local "rhat"), (Exp.var VarKind.local "vtop")]))
                              (Prog.assign VarKind.local "again" (Exp.const (BitVec.ofNat 64 1)))))
                            Prog.skip)
                          Prog.skip)))
                    (Prog.dec "k" Shape.one (Exp.const (BitVec.ofNat 64 0))
                      (Prog.seq
                        (Prog.assign VarKind.local "i" (Exp.const (BitVec.ofNat 64 0)))
                        (Prog.seq
                        (Prog.while (Exp.cmp Cmp.lower (Exp.var VarKind.local "i") (Exp.var VarKind.local "n"))
                          (Prog.dec "p" Shape.one (Exp.panOp PanOp.mul [(Exp.var VarKind.local "qhat"), (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "vn"), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "i"), (Exp.const (BitVec.ofNat 64 8))])]))])
                            (Prog.dec "t" Shape.one (Exp.op BinOp.sub [(Exp.op BinOp.sub [(Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "un"), (Exp.panOp PanOp.mul [(Exp.op BinOp.add [(Exp.var VarKind.local "i"), (Exp.var VarKind.local "j")]), (Exp.const (BitVec.ofNat 64 8))])])), (Exp.var VarKind.local "k")]), (Exp.op BinOp.and [(Exp.var VarKind.local "p"), (Exp.const (BitVec.ofNat 64 4294967295))])])
                              (Prog.seq
                                (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "un"), (Exp.panOp PanOp.mul [(Exp.op BinOp.add [(Exp.var VarKind.local "i"), (Exp.var VarKind.local "j")]), (Exp.const (BitVec.ofNat 64 8))])]) (Exp.op BinOp.and [(Exp.var VarKind.local "t"), (Exp.const (BitVec.ofNat 64 4294967295))]))
                                (Prog.seq
                                (Prog.assign VarKind.local "k" (Exp.op BinOp.sub [(Exp.shift Shift.lsr (Exp.var VarKind.local "p") (Exp.const (BitVec.ofNat 64 32))), (Exp.shift Shift.asr (Exp.var VarKind.local "t") (Exp.const (BitVec.ofNat 64 32)))]))
                                (Prog.assign VarKind.local "i" (Exp.op BinOp.add [(Exp.var VarKind.local "i"), (Exp.const (BitVec.ofNat 64 1))])))))))
                        (Prog.dec "tt" Shape.one (Exp.op BinOp.sub [(Exp.var VarKind.local "ujn"), (Exp.var VarKind.local "k")])
                          (Prog.ite (Exp.cmp Cmp.less (Exp.var VarKind.local "tt") (Exp.const (BitVec.ofNat 64 0)))
                            (Prog.seq
                              (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "q"), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "j"), (Exp.const (BitVec.ofNat 64 8))])]) (Exp.op BinOp.sub [(Exp.var VarKind.local "qhat"), (Exp.const (BitVec.ofNat 64 1))]))
                              (Prog.seq
                              (Prog.assign VarKind.local "k" (Exp.const (BitVec.ofNat 64 0)))
                              (Prog.seq
                              (Prog.assign VarKind.local "i" (Exp.const (BitVec.ofNat 64 0)))
                              (Prog.seq
                              (Prog.while (Exp.cmp Cmp.lower (Exp.var VarKind.local "i") (Exp.var VarKind.local "n"))
                                (Prog.dec "t2" Shape.one (Exp.op BinOp.add [(Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "un"), (Exp.panOp PanOp.mul [(Exp.op BinOp.add [(Exp.var VarKind.local "i"), (Exp.var VarKind.local "j")]), (Exp.const (BitVec.ofNat 64 8))])])), (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "vn"), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "i"), (Exp.const (BitVec.ofNat 64 8))])])), (Exp.var VarKind.local "k")])
                                  (Prog.seq
                                    (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "un"), (Exp.panOp PanOp.mul [(Exp.op BinOp.add [(Exp.var VarKind.local "i"), (Exp.var VarKind.local "j")]), (Exp.const (BitVec.ofNat 64 8))])]) (Exp.op BinOp.and [(Exp.var VarKind.local "t2"), (Exp.const (BitVec.ofNat 64 4294967295))]))
                                    (Prog.seq
                                    (Prog.assign VarKind.local "k" (Exp.shift Shift.lsr (Exp.var VarKind.local "t2") (Exp.const (BitVec.ofNat 64 32))))
                                    (Prog.assign VarKind.local "i" (Exp.op BinOp.add [(Exp.var VarKind.local "i"), (Exp.const (BitVec.ofNat 64 1))]))))))
                              (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "un"), (Exp.panOp PanOp.mul [(Exp.op BinOp.add [(Exp.var VarKind.local "j"), (Exp.var VarKind.local "n")]), (Exp.const (BitVec.ofNat 64 8))])]) (Exp.op BinOp.and [(Exp.op BinOp.add [(Exp.var VarKind.local "tt"), (Exp.var VarKind.local "k")]), (Exp.const (BitVec.ofNat 64 4294967295))]))))))
                            (Prog.seq
                              (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "q"), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "j"), (Exp.const (BitVec.ofNat 64 8))])]) (Exp.var VarKind.local "qhat"))
                              (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "un"), (Exp.panOp PanOp.mul [(Exp.op BinOp.add [(Exp.var VarKind.local "j"), (Exp.var VarKind.local "n")]), (Exp.const (BitVec.ofNat 64 8))])]) (Exp.var VarKind.local "tt"))))))))))))))))

/-- Outer `while (0 < j)` loop in `divmnu` (`n != 1`, `2 ≤ n ≤ m ≤ 16`). -/
theorem divmnu_outer_loop_wsSafe {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    (he : WsEnv s0 s) {q_off mv nv j0 : Nat}
    (hq_off : q_off + 16 * 8 ≤ 640)
    (hq : s.locals.lookup (ofString "q") =
      some (.val (.word (BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 q_off))))
    (hun : s.locals.lookup (ofString "un") =
      some (.val (.word (BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 0))))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 nv))))
    (hj0 : s.locals.lookup (ofString "j") = some (.val (.word (BitVec.ofNat 64 j0))))
    (hi0 : ∃ wi : BitVec 64, s.locals.lookup (ofString "i") = some (.val (.word wi)))
    (hn_ge : 2 ≤ nv) (hn_le : nv ≤ 8) (hm_le : mv ≤ 16) (hnm : nv ≤ mv)
    (hj0_le : j0 ≤ mv - nv + 1) :
    let body := InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural divmnuOuterLoopBodyAST
    let prog := ProgHOL.while (.cmp .lower (.const 0#64) (.var .local (ofString "j"))) body
    WsSafe s (untypedGlobalBufIvls s0) (evaluateHOLFiniteState s prog) ∧
    ((evaluateHOLFiniteState s prog).1 = none →
      WsEnv s0 (evaluateHOLFiniteState s prog).2 ∧
      (∃ jv : Nat, (evaluateHOLFiniteState s prog).2.locals.lookup (ofString "j") =
        some (.val (.word (BitVec.ofNat 64 jv)))) ∧
      (∃ wi : BitVec 64, (evaluateHOLFiniteState s prog).2.locals.lookup (ofString "i") =
        some (.val (.word wi))) ∧
      (∀ x, x ≠ ofString "j" → x ≠ ofString "i" →
        (evaluateHOLFiniteState s prog).2.locals.lookup x = s.locals.lookup x)) := by
  let body := InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural divmnuOuterLoopBodyAST
  dsimp only
  let P : PanSemStateFiniteExact 64 F → Prop := fun st =>
    WsEnv s0 st ∧
    (∃ jv : Nat, jv ≤ mv - nv + 1 ∧ st.locals.lookup (ofString "j") = some (.val (.word (BitVec.ofNat 64 jv)))) ∧
    (∃ wi : BitVec 64, st.locals.lookup (ofString "i") = some (.val (.word wi))) ∧
    (∀ x, x ≠ ofString "j" → x ≠ ofString "i" → st.locals.lookup x = s.locals.lookup x)
  have hP0 : P s := ⟨he, ⟨j0, hj0_le, hj0⟩, hi0, fun _ _ _ => rfl⟩
  have hnb : noTopBreakContinue body = true := rfl
  refine (by
    have hstep : ∀ st w, P (decClockHOLFinite st) →
        @evalHOLFinite 64 F _ st (fun a => Classical.propDecidable (st.memaddrs a))
          (.cmp .lower (.const 0#64) (.var .local (ofString "j"))) =
          some (.val (.word w)) → w ≠ 0 →
        WsSafe (decClockHOLFinite st) (untypedGlobalBufIvls s0)
          (evaluateHOLFiniteState (decClockHOLFinite st) body) ∧
        ((evaluateHOLFiniteState (decClockHOLFinite st) body).1 = none →
          P (evaluateHOLFiniteState (decClockHOLFinite st) body).2) := by
      intro st w ⟨hst_env, ⟨jv0, hjv0_le, hj_st⟩, ⟨wi0, hi_st⟩, hother_st⟩ hcnd hw0
      have hj_st0 : st.locals.lookup (ofString "j") = some (.val (.word (BitVec.ofNat 64 jv0))) := hj_st
      have hjv0_pos : 1 ≤ jv0 := by
        simp only [evalHOLFinite, evalHOLExact, hj_st0, wordCmpHOL, BitVec.lt_def,
          BitVec.toNat_ofNat, Nat.zero_mod, Nat.mod_eq_of_lt (show jv0 < 2 ^ 64 by omega)] at hcnd
        by_cases hpos : 0 < jv0
        · omega
        · simp [hpos] at hcnd; exact absurd hcnd.symm hw0
      let jv := jv0 - 1
      have hjv_le : jv + nv ≤ mv := by omega
      have hev_jdec : @evalHOLExact 64 F _ (decClockHOLFinite st).toExact
          (fun a => Classical.propDecidable ((decClockHOLFinite st).memaddrs a))
          (.op .sub [.var .local (ofString "j"), .const 1#64]) =
          some (.val (.word (BitVec.ofNat 64 jv))) := by
        simp only [evalHOLExact, evalListHOLExact, hj_st, wordOpHOL, wordOp,
          valueIsWord, valueWord, List.all, List.map, Bool.and_self, ↓reduceIte, Option.map]
        congr 3; apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
      dsimp only [body, divmnuOuterLoopBodyAST,
        InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
        List.map]
      apply WsSafe.seq_post' P
        (fun s1 => s1 = setVarHOLFinite (ofString "j") (.val (.word (BitVec.ofNat 64 jv))) (decClockHOLFinite st))
      · refine ⟨WsSafe.assign_local _ _ _ _, ?_⟩
        rw [assign_local_step_eq ⟨_, hj_st⟩ hev_jdec]
        exact fun _ => rfl
      intro s1 hs1_eq; subst hs1_eq
      set s1 := setVarHOLFinite (ofString "j") (.val (.word (BitVec.ofNat 64 jv))) (decClockHOLFinite st)
      have hs1_env : WsEnv s0 s1 := hst_env.with_locals_clock _ _
      refine WsSafe.dec_post (Q := P) fun v_ujn hv_ujn _ => ?_
      obtain ⟨w_ujn, rfl⟩ := eval_word_of_isWordValExp (s := s1) rfl hv_ujn
      set s2 := setVarHOLFinite (ofString "ujn") (.val (.word w_ujn)) s1
      refine WsSafe.dec_post
        (Q := fun sp => P (restoreLocal (ofString "ujn") (s1.locals.lookup (ofString "ujn")) sp))
        fun v_ujn1 hv_ujn1 _ => ?_
      obtain ⟨w_ujn1, rfl⟩ := eval_word_of_isWordValExp (s := s2) rfl hv_ujn1
      set s3 := setVarHOLFinite (ofString "ujn1") (.val (.word w_ujn1)) s2
      refine WsSafe.dec_post
        (Q := fun sp => P (restoreLocal (ofString "ujn") (s1.locals.lookup (ofString "ujn"))
                            (restoreLocal (ofString "ujn1") (s2.locals.lookup (ofString "ujn1")) sp)))
        fun v_ujn2 hv_ujn2 _ => ?_
      obtain ⟨w_ujn2, rfl⟩ := eval_word_of_isWordValExp (s := s3) rfl hv_ujn2
      set s4 := setVarHOLFinite (ofString "ujn2") (.val (.word w_ujn2)) s3
      refine WsSafe.dec_post
        (Q := fun sp => P (restoreLocal (ofString "ujn") (s1.locals.lookup (ofString "ujn"))
                            (restoreLocal (ofString "ujn1") (s2.locals.lookup (ofString "ujn1"))
                              (restoreLocal (ofString "ujn2") (s3.locals.lookup (ofString "ujn2")) sp))))
        fun v_qh hv_qh _ => ?_
      obtain ⟨w_qh0, rfl⟩ := eval_word_of_isWordValExp (s := s4) rfl hv_qh
      set s5 := setVarHOLFinite (ofString "qhat") (.val (.word w_qh0)) s4
      refine WsSafe.dec_post
        (Q := fun sp => P (restoreLocal (ofString "ujn") (s1.locals.lookup (ofString "ujn"))
                            (restoreLocal (ofString "ujn1") (s2.locals.lookup (ofString "ujn1"))
                              (restoreLocal (ofString "ujn2") (s3.locals.lookup (ofString "ujn2"))
                                (restoreLocal (ofString "qhat") (s4.locals.lookup (ofString "qhat")) sp)))))
        fun v_rh hv_rh _ => ?_
      obtain ⟨w_rh0, rfl⟩ := eval_word_of_isWordValExp (s := s5) rfl hv_rh
      set s6 := setVarHOLFinite (ofString "rhat") (.val (.word w_rh0)) s5
      have hs6_env : WsEnv s0 s6 :=
        ((((hs1_env.with_locals_clock _ _).with_locals_clock _ _).with_locals_clock _ _).with_locals_clock _ _).with_locals_clock _ _
      let Q6 := fun sp : PanSemStateFiniteExact 64 F =>
        P (restoreLocal (ofString "ujn") (s1.locals.lookup (ofString "ujn"))
            (restoreLocal (ofString "ujn1") (s2.locals.lookup (ofString "ujn1"))
              (restoreLocal (ofString "ujn2") (s3.locals.lookup (ofString "ujn2"))
                (restoreLocal (ofString "qhat") (s4.locals.lookup (ofString "qhat"))
                  (restoreLocal (ofString "rhat") (s5.locals.lookup (ofString "rhat")) sp)))))
      have hqh_s6 : ∃ w : BitVec 64, s6.locals.lookup (ofString "qhat") = some (.val (.word w)) :=
        ⟨w_qh0, by simp [s6, s5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "rhat" ≠ ofString "qhat" by decide]⟩
      apply WsSafe.seq_post' Q6
        (fun s7 => WsEnv s0 s7 ∧
          (∃ w : BitVec 64, s7.locals.lookup (ofString "qhat") = some (.val (.word w))) ∧
          (∀ x, x ≠ ofString "qhat" ∧ x ≠ ofString "rhat" → s7.locals.lookup x = s6.locals.lookup x))
      · exact WsSafe.ro_preserving_word_and_locals hs6_env (by decide) (by decide) hqh_s6
          (fun x ⟨hxq, hxr⟩ => by simp [notAssignedLocal, bne_iff_ne, Ne.symm hxq, Ne.symm hxr])
      intro s7 ⟨hs7_env, hqh_s7, hother_s7⟩
      refine WsSafe.dec_post (Q := Q6) fun v_ag hv_ag _ => ?_
      obtain ⟨w_ag0, rfl⟩ := eval_word_of_isWordValExp (s := s7) rfl hv_ag
      set s8 := setVarHOLFinite (ofString "again") (.val (.word w_ag0)) s7
      have hs8_env : WsEnv s0 s8 := hs7_env.with_locals_clock _ _
      let Q8 := fun sp : PanSemStateFiniteExact 64 F =>
        Q6 (restoreLocal (ofString "again") (s7.locals.lookup (ofString "again")) sp)
      have hqh_s8 : ∃ w : BitVec 64, s8.locals.lookup (ofString "qhat") = some (.val (.word w)) := by
        obtain ⟨w, hw⟩ := hqh_s7
        exact ⟨w, by simp [s8, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "again" ≠ ofString "qhat" by decide, hw]⟩
      apply WsSafe.seq_post' Q8
        (fun s9 => WsEnv s0 s9 ∧
          (∃ w : BitVec 64, s9.locals.lookup (ofString "qhat") = some (.val (.word w))) ∧
          (∀ x, x ≠ ofString "qhat" ∧ x ≠ ofString "rhat" ∧ x ≠ ofString "again" →
            s9.locals.lookup x = s8.locals.lookup x))
      · exact WsSafe.ro_preserving_word_and_locals hs8_env (by decide) (by decide) hqh_s8
          (fun x ⟨hxq, hxr, hxa⟩ => by simp [notAssignedLocal, bne_iff_ne, Ne.symm hxq, Ne.symm hxr, Ne.symm hxa])
      intro s9 ⟨hs9_env, ⟨w_qh, hqh_s9⟩, hother_s9⟩
      refine WsSafe.dec_post (Q := Q8) fun v_k hv_k _ => ?_
      obtain ⟨w_k0, rfl⟩ := eval_word_of_isWordValExp (s := s9) rfl hv_k
      set s10 := setVarHOLFinite (ofString "k") (.val (.word w_k0)) s9
      have hs10_env : WsEnv s0 s10 := hs9_env.with_locals_clock _ _
      let Q10 := fun sp : PanSemStateFiniteExact 64 F =>
        Q8 (restoreLocal (ofString "k") (s9.locals.lookup (ofString "k")) sp)
      have hs9_base : ∀ x, x ≠ ofString "qhat" → x ≠ ofString "rhat" → x ≠ ofString "again" →
          x ≠ ofString "ujn" → x ≠ ofString "ujn1" → x ≠ ofString "ujn2" →
          s9.locals.lookup x = s1.locals.lookup x := by
        intro x h1 h2 h3 h4 h5 h6
        rw [hother_s9 x ⟨h1, h2, h3⟩]
        simp [s8, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm h3]
        rw [hother_s7 x ⟨h1, h2⟩]
        simp [s6, s5, s4, s3, s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          Ne.symm h1, Ne.symm h2, Ne.symm h4, Ne.symm h5, Ne.symm h6]
      have hi_s10 : ∃ wi : BitVec 64, s10.locals.lookup (ofString "i") = some (.val (.word wi)) := by
        refine ⟨wi0, ?_⟩
        simp [s10, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "k" ≠ ofString "i" by decide]
        rw [hs9_base (ofString "i") (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
        simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "j" ≠ ofString "i" by decide, hi_st]
      apply WsSafe.seq_post' Q10
        (fun s11 => s11 = setVarHOLFinite (ofString "i") (.val (.word 0#64)) s10)
      · refine ⟨WsSafe.assign_local _ _ _ _, ?_⟩
        rw [assign_local_step_eq hi_s10 rfl]
        exact fun _ => rfl
      intro s11 hs11_eq; subst hs11_eq
      set s11 := setVarHOLFinite (ofString "i") (.val (.word 0#64)) s10
      have hs11_env : WsEnv s0 s11 := hs10_env.with_locals_clock _ _
      have hun_s11 : s11.locals.lookup (ofString "un") =
          some (.val (.word (BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 0))) := by
        rw [show (s11.locals.lookup (ofString "un")) = s10.locals.lookup (ofString "un") by
          simp [s11, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "i" ≠ ofString "un" by decide]]
        rw [show (s10.locals.lookup (ofString "un")) = s9.locals.lookup (ofString "un") by
          simp [s10, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "k" ≠ ofString "un" by decide]]
        rw [hs9_base (ofString "un") (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
        rw [show (s1.locals.lookup (ofString "un")) = (decClockHOLFinite st).locals.lookup (ofString "un") by
          simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "j" ≠ ofString "un" by decide]]
        rw [hother_st (ofString "un") (by decide) (by decide)]; exact hun
      have hj_s11 : s11.locals.lookup (ofString "j") = some (.val (.word (BitVec.ofNat 64 jv))) := by
        simp [s11, s10, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "i" ≠ ofString "j" by decide, show ofString "k" ≠ ofString "j" by decide]
        rw [hs9_base (ofString "j") (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
        simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hn_s11 : s11.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 nv))) := by
        simp [s11, s10, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "i" ≠ ofString "n" by decide, show ofString "k" ≠ ofString "n" by decide]
        rw [hs9_base (ofString "n") (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
        simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "j" ≠ ofString "n" by decide,
          hother_st (ofString "n") (by decide) (by decide), hn]
      have hi_s11 : s11.locals.lookup (ofString "i") = some (.val (.word 0#64)) := by
        simp [s11, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hk_s11 : ∃ kv : BitVec 64, s11.locals.lookup (ofString "k") = some (.val (.word kv)) := by
        exact ⟨w_k0, by simp [s11, s10, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "i" ≠ ofString "k" by decide]⟩
      apply WsSafe.seq_post' Q10
        (fun s12 => WsEnv s0 s12 ∧
          (∃ iv : Nat, s12.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 iv)))) ∧
          (∃ kv : BitVec 64, s12.locals.lookup (ofString "k") = some (.val (.word kv))) ∧
          (∀ x, x ≠ ofString "i" → x ≠ ofString "k" → s12.locals.lookup x = s11.locals.lookup x))
      · exact divmnu_submul_loop_wsSafe hs11_env hun_s11 hj_s11 hn_s11 hi_s11 hk_s11 hn_le (by omega)
      intro s12 ⟨hs12_env, ⟨iv12, hi_s12⟩, ⟨kv12, hk_s12⟩, hother_s12⟩
      refine WsSafe.dec_post (Q := Q10) fun v_tt hv_tt _ => ?_
      obtain ⟨w_tt, rfl⟩ := eval_word_of_isWordValExp (s := s12) rfl hv_tt
      set s13 := setVarHOLFinite (ofString "tt") (.val (.word w_tt)) s12
      have hs13_env : WsEnv s0 s13 := hs12_env.with_locals_clock _ _
      let Q13 := fun sp : PanSemStateFiniteExact 64 F =>
        Q10 (restoreLocal (ofString "tt") (s12.locals.lookup (ofString "tt")) sp)
      have hq_s13 : s13.locals.lookup (ofString "q") =
          some (.val (.word (BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 q_off))) := by
        simp [s13, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "tt" ≠ ofString "q" by decide]
        rw [hother_s12 (ofString "q") (by decide) (by decide)]
        simp [s11, s10, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "i" ≠ ofString "q" by decide, show ofString "k" ≠ ofString "q" by decide]
        rw [hs9_base (ofString "q") (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
        simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "j" ≠ ofString "q" by decide,
          hother_st (ofString "q") (by decide) (by decide), hq]
      have hun_s13 : s13.locals.lookup (ofString "un") =
          some (.val (.word (BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 0))) := by
        rw [show s13.locals.lookup (ofString "un") = s12.locals.lookup (ofString "un") by
          simp [s13, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "tt" ≠ ofString "un" by decide]]
        rw [hother_s12 (ofString "un") (by decide) (by decide)]; exact hun_s11
      have hj_s13 : s13.locals.lookup (ofString "j") = some (.val (.word (BitVec.ofNat 64 jv))) := by
        simp [s13, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "tt" ≠ ofString "j" by decide]
        rw [hother_s12 (ofString "j") (by decide) (by decide)]; exact hj_s11
      have hn_s13 : s13.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 nv))) := by
        simp [s13, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "tt" ≠ ofString "n" by decide]
        rw [hother_s12 (ofString "n") (by decide) (by decide)]; exact hn_s11
      have hqh_s13 : s13.locals.lookup (ofString "qhat") = some (.val (.word w_qh)) := by
        simp [s13, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "tt" ≠ ofString "qhat" by decide]
        rw [hother_s12 (ofString "qhat") (by decide) (by decide)]
        simp [s11, s10, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "i" ≠ ofString "qhat" by decide, show ofString "k" ≠ ofString "qhat" by decide, hqh_s9]
      have htt_s13 : s13.locals.lookup (ofString "tt") = some (.val (.word w_tt)) := by
        simp [s13, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hk_s13 : s13.locals.lookup (ofString "k") = some (.val (.word kv12)) := by
        simp [s13, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "tt" ≠ ofString "k" by decide, hk_s12]
      have hi_s13 : s13.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 iv12))) := by
        simp [s13, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "tt" ≠ ofString "i" by decide, hi_s12]
      have hQ13_of : ∀ sp : PanSemStateFiniteExact 64 F,
          WsEnv s0 sp →
          (∃ iv : Nat, sp.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 iv)))) →
          (∀ x, x ≠ ofString "i" → x ≠ ofString "k" → sp.locals.lookup x = s13.locals.lookup x) →
          Q13 sp := by
        intro sp hsp_env ⟨ivp, hi_sp⟩ hsp_other
        refine ⟨(((((((hsp_env.with_locals_clock _ _).with_locals_clock _ _).with_locals_clock _ _).with_locals_clock _ _).with_locals_clock _ _).with_locals_clock _ _).with_locals_clock _ _).with_locals_clock _ _,
          ⟨jv, by omega, ?_⟩, ⟨BitVec.ofNat 64 ivp, ?_⟩, ?_⟩
        · simp only [restoreLocal, PanRunBounded.resVarEq_lookup,
            show ofString "j" ≠ ofString "ujn" by decide,
            show ofString "j" ≠ ofString "ujn1" by decide,
            show ofString "j" ≠ ofString "ujn2" by decide,
            show ofString "j" ≠ ofString "qhat" by decide,
            show ofString "j" ≠ ofString "rhat" by decide,
            show ofString "j" ≠ ofString "again" by decide,
            show ofString "j" ≠ ofString "k" by decide,
            show ofString "j" ≠ ofString "tt" by decide, ↓reduceIte]
          rw [hsp_other (ofString "j") (by decide) (by decide)]; exact hj_s13
        · simp only [restoreLocal, PanRunBounded.resVarEq_lookup,
            show ofString "i" ≠ ofString "ujn" by decide,
            show ofString "i" ≠ ofString "ujn1" by decide,
            show ofString "i" ≠ ofString "ujn2" by decide,
            show ofString "i" ≠ ofString "qhat" by decide,
            show ofString "i" ≠ ofString "rhat" by decide,
            show ofString "i" ≠ ofString "again" by decide,
            show ofString "i" ≠ ofString "k" by decide,
            show ofString "i" ≠ ofString "tt" by decide, ↓reduceIte]
          exact hi_sp
        · intro x hxj hxi
          simp only [restoreLocal, PanRunBounded.resVarEq_lookup]
          by_cases h1 : x = ofString "ujn"
          · subst h1; simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "j" ≠ ofString "ujn" by decide, hother_st (ofString "ujn") (by decide) (by decide)]
          · rw [if_neg h1]
            by_cases h2 : x = ofString "ujn1"
            · subst h2; simp [s2, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "ujn" ≠ ofString "ujn1" by decide, show ofString "j" ≠ ofString "ujn1" by decide, hother_st (ofString "ujn1") (by decide) (by decide)]
            · rw [if_neg h2]
              by_cases h3 : x = ofString "ujn2"
              · subst h3; simp [s3, s2, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "ujn1" ≠ ofString "ujn2" by decide, show ofString "ujn" ≠ ofString "ujn2" by decide, show ofString "j" ≠ ofString "ujn2" by decide, hother_st (ofString "ujn2") (by decide) (by decide)]
              · rw [if_neg h3]
                by_cases h4 : x = ofString "qhat"
                · subst h4; simp [s4, s3, s2, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "ujn2" ≠ ofString "qhat" by decide, show ofString "ujn1" ≠ ofString "qhat" by decide, show ofString "ujn" ≠ ofString "qhat" by decide, show ofString "j" ≠ ofString "qhat" by decide, hother_st (ofString "qhat") (by decide) (by decide)]
                · rw [if_neg h4]
                  by_cases h5 : x = ofString "rhat"
                  · subst h5; simp [s5, s4, s3, s2, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "qhat" ≠ ofString "rhat" by decide, show ofString "ujn2" ≠ ofString "rhat" by decide, show ofString "ujn1" ≠ ofString "rhat" by decide, show ofString "ujn" ≠ ofString "rhat" by decide, show ofString "j" ≠ ofString "rhat" by decide, hother_st (ofString "rhat") (by decide) (by decide)]
                  · rw [if_neg h5]
                    by_cases h6 : x = ofString "again"
                    · subst h6; simp only [↓reduceIte]
                      rw [hother_s7 (ofString "again") ⟨by decide, by decide⟩]
                      simp [s6, s5, s4, s3, s2, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                        show ofString "rhat" ≠ ofString "again" by decide,
                        show ofString "qhat" ≠ ofString "again" by decide,
                        show ofString "ujn2" ≠ ofString "again" by decide,
                        show ofString "ujn1" ≠ ofString "again" by decide,
                        show ofString "ujn" ≠ ofString "again" by decide,
                        show ofString "j" ≠ ofString "again" by decide,
                        hother_st (ofString "again") (by decide) (by decide)]
                    · rw [if_neg h6]
                      by_cases h7 : x = ofString "k"
                      · subst h7; simp only [↓reduceIte]
                        rw [hs9_base (ofString "k") (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
                        simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                          show ofString "j" ≠ ofString "k" by decide,
                          hother_st (ofString "k") (by decide) (by decide)]
                      · rw [if_neg h7]
                        by_cases h8 : x = ofString "tt"
                        · subst h8; simp only [↓reduceIte]
                          rw [hother_s12 (ofString "tt") (by decide) (by decide)]
                          simp [s11, s10, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                            show ofString "i" ≠ ofString "tt" by decide,
                            show ofString "k" ≠ ofString "tt" by decide]
                          rw [hs9_base (ofString "tt") (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
                          simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                            show ofString "j" ≠ ofString "tt" by decide,
                            hother_st (ofString "tt") (by decide) (by decide)]
                        · rw [if_neg h8]
                          rw [hsp_other x hxi h7]
                          simp [s13, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm h8]
                          rw [hother_s12 x hxi h7]
                          simp [s11, s10, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                            Ne.symm hxi, Ne.symm h7]
                          rw [hs9_base x h4 h5 h6 h1 h2 h3]
                          simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                            Ne.symm hxj, hother_st x hxj hxi]
      refine WsSafe.ite_post (Q := Q13)
        (hyes := fun _ _ _ => ?_)
        (hno := fun _ => ?_)
      · -- `tt <s 0` branch: store q+j*8, k:=0, i:=0, addback loop, store un+(j+n)*8
        apply WsSafe.seq_post' Q13
          (fun s14 => WsEnv s0 s14 ∧ s14.locals = s13.locals)
        · exact WsSafe.store_ws_scaled_post hs13_env
            (baseExp := .var .local (ofString "q"))
            (idxExp := .var .local (ofString "j"))
            (valExp := .op .sub [.var .local (ofString "qhat"), .const 1#64])
            (off := q_off) (idx := jv)
            (by simp only [evalHOLExact]; exact hq_s13)
            (by simp only [evalHOLExact]; exact hj_s13)
            (by omega) rfl
        intro s14 ⟨hs14_env, hs14_loc⟩
        apply WsSafe.seq_post' Q13
          (fun s15 => s15 = setVarHOLFinite (ofString "k") (.val (.word 0#64)) s14)
        · refine ⟨WsSafe.assign_local _ _ _ _, ?_⟩
          rw [assign_local_step_eq ⟨kv12, by rw [hs14_loc]; exact hk_s13⟩ rfl]
          exact fun _ => rfl
        intro s15 hs15_eq; subst hs15_eq
        set s15 := setVarHOLFinite (ofString "k") (.val (.word 0#64)) s14
        have hs15_env : WsEnv s0 s15 := hs14_env.with_locals_clock _ _
        apply WsSafe.seq_post' Q13
          (fun s16 => s16 = setVarHOLFinite (ofString "i") (.val (.word 0#64)) s15)
        · refine ⟨WsSafe.assign_local _ _ _ _, ?_⟩
          rw [assign_local_step_eq ⟨BitVec.ofNat 64 iv12, by
            simp [s15, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "k" ≠ ofString "i" by decide, hs14_loc, hi_s13]⟩ rfl]
          exact fun _ => rfl
        intro s16 hs16_eq; subst hs16_eq
        set s16 := setVarHOLFinite (ofString "i") (.val (.word 0#64)) s15
        have hs16_env : WsEnv s0 s16 := hs15_env.with_locals_clock _ _
        have hun_s16 : s16.locals.lookup (ofString "un") =
            some (.val (.word (BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 0))) := by
          rw [show s16.locals.lookup (ofString "un") = s14.locals.lookup (ofString "un") by
            simp [s16, s15, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "i" ≠ ofString "un" by decide, show ofString "k" ≠ ofString "un" by decide]]
          rw [hs14_loc]; exact hun_s13
        have hj_s16 : s16.locals.lookup (ofString "j") = some (.val (.word (BitVec.ofNat 64 jv))) := by
          simp [s16, s15, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "i" ≠ ofString "j" by decide, show ofString "k" ≠ ofString "j" by decide, hs14_loc, hj_s13]
        have hn_s16 : s16.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 nv))) := by
          simp [s16, s15, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "i" ≠ ofString "n" by decide, show ofString "k" ≠ ofString "n" by decide, hs14_loc, hn_s13]
        have hi_s16 : s16.locals.lookup (ofString "i") = some (.val (.word 0#64)) := by
          simp [s16, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have hk_s16 : ∃ kv : BitVec 64, s16.locals.lookup (ofString "k") = some (.val (.word kv)) := by
          exact ⟨0#64, by simp [s16, s15, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "i" ≠ ofString "k" by decide]⟩
        apply WsSafe.seq_post' Q13
          (fun s17 => WsEnv s0 s17 ∧
            (∃ iv : Nat, s17.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 iv)))) ∧
            (∃ kv : BitVec 64, s17.locals.lookup (ofString "k") = some (.val (.word kv))) ∧
            (∀ x, x ≠ ofString "i" → x ≠ ofString "k" → s17.locals.lookup x = s16.locals.lookup x))
        · exact divmnu_addback_loop_wsSafe hs16_env hun_s16 hj_s16 hn_s16 hi_s16 hk_s16 hn_le (by omega)
        intro s17 ⟨hs17_env, ⟨iv17, hi_s17⟩, _, hother_s17⟩
        have hun_s17 : s17.locals.lookup (ofString "un") =
            some (.val (.word (BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 0))) := by
          rw [hother_s17 (ofString "un") (by decide) (by decide)]; exact hun_s16
        have hj_s17 : s17.locals.lookup (ofString "j") = some (.val (.word (BitVec.ofNat 64 jv))) := by
          rw [hother_s17 (ofString "j") (by decide) (by decide)]; exact hj_s16
        have hn_s17 : s17.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 nv))) := by
          rw [hother_s17 (ofString "n") (by decide) (by decide)]; exact hn_s16
        have hev_jn17 : @evalHOLExact 64 F _ s17.toExact (fun a => Classical.propDecidable (s17.memaddrs a))
            (.op .add [.var .local (ofString "j"), .var .local (ofString "n")]) =
            some (.val (.word (BitVec.ofNat 64 (jv + nv)))) := by
          simp only [evalHOLExact, evalListHOLExact, hj_s17, hn_s17, wordOpHOL, wordOp,
            valueIsWord, valueWord, List.all, List.map, Bool.and_self, ↓reduceIte, Option.map, List.foldr]
          congr 3
          rw [show (BitVec.ofNat 64 nv + 0 : BitVec 64) = BitVec.ofNat 64 nv from BitVec.add_zero _]
          apply BitVec.eq_of_toNat_eq
          simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
        have hst18 := WsSafe.store_ws_scaled_post hs17_env
          (baseExp := .var .local (ofString "un"))
          (idxExp := .op .add [.var .local (ofString "j"), .var .local (ofString "n")])
          (valExp := .op .and [.op .add [.var .local (ofString "tt"), .var .local (ofString "k")], .const 4294967295#64])
          (off := 0) (idx := jv + nv)
          (by simp only [evalHOLExact]; exact hun_s17) hev_jn17 (by omega) rfl
        refine ⟨hst18.1, fun hn18 => ?_⟩
        obtain ⟨hs18_env, hs18_loc⟩ := hst18.2 hn18
        refine hQ13_of _ hs18_env ⟨iv17, by rw [hs18_loc]; exact hi_s17⟩ (fun x hxi hxk => ?_)
        rw [hs18_loc, hother_s17 x hxi hxk]
        simp [s16, s15, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          Ne.symm hxi, Ne.symm hxk, hs14_loc]
      · -- `¬ (tt <s 0)` branch: store q+j*8 qhat, store un+(j+n)*8 tt
        have hst_q := WsSafe.store_ws_scaled hs13_env
          (baseExp := .var .local (ofString "q"))
          (idxExp := .var .local (ofString "j"))
          (valExp := .var .local (ofString "qhat"))
          (off := q_off) (idx := jv)
          (by simp only [evalHOLExact]; exact hq_s13)
          (by simp only [evalHOLExact]; exact hj_s13)
          (by omega)
          (fun v hv => by
            simp only [evalHOLExact, hqh_s13] at hv
            injection hv with hv'; exact ⟨w_qh, hv'.symm⟩)
        apply WsSafe.seq_post' Q13
          (fun s14 => WsEnv s0 s14 ∧ s14.locals = s13.locals)
        · exact ⟨hst_q, fun hn14 => ⟨hs13_env.step (hst_q.1 hn14), store_none_locals hn14⟩⟩
        intro s14 ⟨hs14_env, hs14_loc⟩
        have hun_s14 : s14.locals.lookup (ofString "un") =
            some (.val (.word (BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 0))) := by
          rw [hs14_loc]; exact hun_s13
        have hj_s14 : s14.locals.lookup (ofString "j") = some (.val (.word (BitVec.ofNat 64 jv))) := by
          rw [hs14_loc]; exact hj_s13
        have hn_s14 : s14.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 nv))) := by
          rw [hs14_loc]; exact hn_s13
        have htt_s14 : s14.locals.lookup (ofString "tt") = some (.val (.word w_tt)) := by
          rw [hs14_loc]; exact htt_s13
        have hev_jn14 : @evalHOLExact 64 F _ s14.toExact (fun a => Classical.propDecidable (s14.memaddrs a))
            (.op .add [.var .local (ofString "j"), .var .local (ofString "n")]) =
            some (.val (.word (BitVec.ofNat 64 (jv + nv)))) := by
          simp only [evalHOLExact, evalListHOLExact, hj_s14, hn_s14, wordOpHOL, wordOp,
            valueIsWord, valueWord, List.all, List.map, Bool.and_self, ↓reduceIte, Option.map, List.foldr]
          congr 3
          rw [show (BitVec.ofNat 64 nv + 0 : BitVec 64) = BitVec.ofNat 64 nv from BitVec.add_zero _]
          apply BitVec.eq_of_toNat_eq
          simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
        have hst_un := WsSafe.store_ws_scaled hs14_env
          (baseExp := .var .local (ofString "un"))
          (idxExp := .op .add [.var .local (ofString "j"), .var .local (ofString "n")])
          (valExp := .var .local (ofString "tt"))
          (off := 0) (idx := jv + nv)
          (by simp only [evalHOLExact]; exact hun_s14)
          hev_jn14
          (by omega)
          (fun v hv => by
            simp only [evalHOLExact, htt_s14] at hv
            injection hv with hv'; exact ⟨w_tt, hv'.symm⟩)
        refine ⟨hst_un, fun hn15 => ?_⟩
        have hs15_env := hs14_env.step (hst_un.1 hn15)
        have hs15_loc := store_none_locals hn15
        refine hQ13_of _ hs15_env ⟨iv12, by rw [hs15_loc, hs14_loc]; exact hi_s13⟩ (fun x _ _ => ?_)
        rw [hs15_loc, hs14_loc]
    have hpost := WsSafe.while_loop_post hnb P
      (fun t ⟨h1, h2, h3, h4⟩ => ⟨⟨h1.code, h1.memaddrs, h1.globals, h1.ws_bnd⟩, h2, h3, h4⟩)
      hstep s hP0
    exact ⟨hpost.1, fun hn =>
      ⟨(hpost.2 hn).1, ⟨(hpost.2 hn).2.1.choose, (hpost.2 hn).2.1.choose_spec.2⟩,
       (hpost.2 hn).2.2.1, (hpost.2 hn).2.2.2⟩⟩)

/-! ## 6. Parameter-lookup helpers and `divmnu_wsSafe` -/

private theorem shapeEqHOL_symm {a b : ShapeHOL} (h : shapeEqHOL a b = true) :
    shapeEqHOL b a = true :=
  (shapeEqHOL_eq_true _ _).mpr ((shapeEqHOL_eq_true _ _).mp h).symm

private theorem lookup_u256_to_digits_locals
    {vals : List (ValueHOL 64)} {body : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {rs : ShapeHOL}
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup
      (ofString "u256_to_digits") vals = some (body, callee, rs)) :
    ∃ vp va, vals = [vp, va] ∧
      body = InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_u256_to_digits).body ∧
      callee.lookup (ofString "p") = some vp ∧
      callee.lookup (ofString "a") = some va ∧
      shapeEqHOL (shapeOfHOLExact vp) .one = true ∧
      shapeEqHOL (shapeOfHOLExact va) (.comb [.one, .one, .one, .one]) = true := by
  have hraw := lookupCodeHOLFinite_eq_some _ _ _ _ _ _ hl
  simp only [lookupCodeHOLExact, lookup_u256_to_digits, List.length] at hraw
  rcases vals with _ | ⟨vp, _ | ⟨va, _ | _⟩⟩
  · simp at hraw
  · simp at hraw
  · simp only [List.length, ↓reduceIte, List.zip, List.zipWith, List.all,
      List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hraw
    split at hraw
    · rename_i hshapes
      have hinj := Option.some.inj hraw
      have hb : body = _ := (Prod.mk.inj hinj).1.symm
      have hfn : callee.lookup = _ := (Prod.mk.inj (Prod.mk.inj hinj).2).1.symm
      have hp := congrFun hfn (ofString "p")
      have ha := congrFun hfn (ofString "a")
      refine ⟨vp, va, rfl, hb, ?_, ?_,
        shapeEqHOL_symm hshapes.2.2.1, shapeEqHOL_symm hshapes.2.2.2⟩
      · simpa [FUPDATE_LIST, FUPDATE, show ofString "p" ≠ ofString "a" by decide] using hp
      · simpa [FUPDATE_LIST, FUPDATE] using ha
    · simp at hraw
  · simp [List.length] at hraw

private theorem lookup_digits_len_locals
    {vals : List (ValueHOL 64)} {body : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {rs : ShapeHOL}
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup
      (ofString "digits_len") vals = some (body, callee, rs)) :
    ∃ vp vn, vals = [vp, vn] ∧
      body = digitsLenBody ∧
      callee.lookup (ofString "p") = some vp ∧
      callee.lookup (ofString "n") = some vn ∧
      shapeEqHOL (shapeOfHOLExact vp) .one = true ∧
      shapeEqHOL (shapeOfHOLExact vn) .one = true := by
  have hraw := lookupCodeHOLFinite_eq_some _ _ _ _ _ _ hl
  simp only [lookupCodeHOLExact, lookup_digits_len, List.length] at hraw
  rcases vals with _ | ⟨vp, _ | ⟨vn, _ | _⟩⟩
  · simp at hraw
  · simp at hraw
  · simp only [List.length, ↓reduceIte, List.zip, List.zipWith, List.all,
      List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hraw
    split at hraw
    · rename_i hshapes
      have hinj := Option.some.inj hraw
      have hb : body = _ := (Prod.mk.inj hinj).1.symm
      have hfn : callee.lookup = _ := (Prod.mk.inj (Prod.mk.inj hinj).2).1.symm
      have hp := congrFun hfn (ofString "p")
      have hn := congrFun hfn (ofString "n")
      refine ⟨vp, vn, rfl, hb, ?_, ?_,
        shapeEqHOL_symm hshapes.2.2.1, shapeEqHOL_symm hshapes.2.2.2⟩
      · simpa [FUPDATE_LIST, FUPDATE, show ofString "p" ≠ ofString "n" by decide] using hp
      · simpa [FUPDATE_LIST, FUPDATE] using hn
    · simp at hraw
  · simp [List.length] at hraw

private theorem lookup_divmnu_locals
    {vals : List (ValueHOL 64)} {body : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {rs : ShapeHOL}
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup
      (ofString "divmnu") vals = some (body, callee, rs)) :
    ∃ vq vr vu vm vv vn, vals = [vq, vr, vu, vm, vv, vn] ∧
      body = InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_divmnu).body ∧
      callee.lookup (ofString "q") = some vq ∧
      callee.lookup (ofString "r") = some vr ∧
      callee.lookup (ofString "u") = some vu ∧
      callee.lookup (ofString "m") = some vm ∧
      callee.lookup (ofString "v") = some vv ∧
      callee.lookup (ofString "n") = some vn ∧
      shapeEqHOL (shapeOfHOLExact vu) .one = true ∧
      shapeEqHOL (shapeOfHOLExact vv) .one = true := by
  have hraw := lookupCodeHOLFinite_eq_some _ _ _ _ _ _ hl
  simp only [lookupCodeHOLExact, lookup_divmnu, List.length] at hraw
  rcases vals with _ | ⟨vq, _ | ⟨vr, _ | ⟨vu, _ | ⟨vm, _ | ⟨vv, _ | ⟨vn, _ | _⟩⟩⟩⟩⟩⟩
  · simp at hraw
  · simp at hraw
  · simp at hraw
  · simp at hraw
  · simp at hraw
  · simp at hraw
  · simp only [List.length, ↓reduceIte, List.zip, List.zipWith, List.all,
      List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hraw
    split at hraw
    · rename_i hshapes
      have hinj := Option.some.inj hraw
      have hb : body = _ := (Prod.mk.inj hinj).1.symm
      have hfn : callee.lookup = _ := (Prod.mk.inj (Prod.mk.inj hinj).2).1.symm
      refine ⟨vq, vr, vu, vm, vv, vn, rfl, hb, ?_, ?_, ?_, ?_, ?_, ?_,
        shapeEqHOL_symm hshapes.2.2.2.2.1, shapeEqHOL_symm hshapes.2.2.2.2.2.2.1⟩
      · simpa [FUPDATE_LIST, FUPDATE,
          show ofString "q" ≠ ofString "n" by decide,
          show ofString "q" ≠ ofString "v" by decide,
          show ofString "q" ≠ ofString "m" by decide,
          show ofString "q" ≠ ofString "u" by decide,
          show ofString "q" ≠ ofString "r" by decide] using congrFun hfn (ofString "q")
      · simpa [FUPDATE_LIST, FUPDATE,
          show ofString "r" ≠ ofString "n" by decide,
          show ofString "r" ≠ ofString "v" by decide,
          show ofString "r" ≠ ofString "m" by decide,
          show ofString "r" ≠ ofString "u" by decide] using congrFun hfn (ofString "r")
      · simpa [FUPDATE_LIST, FUPDATE,
          show ofString "u" ≠ ofString "n" by decide,
          show ofString "u" ≠ ofString "v" by decide,
          show ofString "u" ≠ ofString "m" by decide] using congrFun hfn (ofString "u")
      · simpa [FUPDATE_LIST, FUPDATE,
          show ofString "m" ≠ ofString "n" by decide,
          show ofString "m" ≠ ofString "v" by decide] using congrFun hfn (ofString "m")
      · simpa [FUPDATE_LIST, FUPDATE,
          show ofString "v" ≠ ofString "n" by decide,
          show ofString "v" ≠ ofString "n" by decide] using congrFun hfn (ofString "v")
      · simpa [FUPDATE_LIST, FUPDATE] using congrFun hfn (ofString "n")
    · simp at hraw
  · simp [List.length] at hraw

private theorem lookup_digits_divmod_locals
    {vals : List (ValueHOL 64)} {body : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {rs : ShapeHOL}
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup
      (ofString "digits_divmod") vals = some (body, callee, rs)) :
    ∃ vu vm vd, vals = [vu, vm, vd] ∧
      body = InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_digits_divmod).body ∧
      callee.lookup (ofString "u") = some vu ∧
      callee.lookup (ofString "m") = some vm ∧
      callee.lookup (ofString "d") = some vd ∧
      shapeEqHOL (shapeOfHOLExact vu) .one = true ∧
      shapeEqHOL (shapeOfHOLExact vm) .one = true ∧
      shapeEqHOL (shapeOfHOLExact vd) (.comb [.one, .one, .one, .one]) = true := by
  have hraw := lookupCodeHOLFinite_eq_some _ _ _ _ _ _ hl
  simp only [lookupCodeHOLExact, lookup_digits_divmod, List.length] at hraw
  rcases vals with _ | ⟨vu, _ | ⟨vm, _ | ⟨vd, _ | _⟩⟩⟩
  · simp at hraw
  · simp at hraw
  · simp at hraw
  · simp only [List.length, ↓reduceIte, List.zip, List.zipWith, List.all,
      List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hraw
    split at hraw
    · rename_i hshapes
      have hinj := Option.some.inj hraw
      have hb : body = _ := (Prod.mk.inj hinj).1.symm
      have hfn : callee.lookup = _ := (Prod.mk.inj (Prod.mk.inj hinj).2).1.symm
      refine ⟨vu, vm, vd, rfl, hb, ?_, ?_, ?_,
        shapeEqHOL_symm hshapes.2.2.1, shapeEqHOL_symm hshapes.2.2.2.1, shapeEqHOL_symm hshapes.2.2.2.2⟩
      · simpa [FUPDATE_LIST, FUPDATE,
          show ofString "u" ≠ ofString "d" by decide,
          show ofString "u" ≠ ofString "m" by decide] using congrFun hfn (ofString "u")
      · simpa [FUPDATE_LIST, FUPDATE,
          show ofString "m" ≠ ofString "d" by decide] using congrFun hfn (ofString "m")
      · simpa [FUPDATE_LIST, FUPDATE] using congrFun hfn (ofString "d")
    · simp at hraw
  · simp [List.length] at hraw

private theorem evalList_two_eq {F : Type} {s : PanSemStateFiniteExact 64 F}
    {e1 e2 : ExpHOL 64} {vals : List (ValueHOL 64)}
    (h : evalListHOLFinite s (h := fun x => Classical.propDecidable (s.memaddrs x)) [e1, e2] = some vals) :
    ∃ v1 v2,
      @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) e1 = some v1 ∧
      @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) e2 = some v2 ∧
      vals = [v1, v2] := by
  rcases h1 : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) e1 with _ | v1
  · simp [evalListHOLFinite, evalListHOLExact, h1] at h
  rcases h2 : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) e2 with _ | v2
  · simp [evalListHOLFinite, evalListHOLExact, h1, h2] at h
  refine ⟨v1, v2, rfl, rfl, ?_⟩
  simpa [evalListHOLFinite, evalListHOLExact, h1, h2] using h.symm

private theorem evalList_three_eq {F : Type} {s : PanSemStateFiniteExact 64 F}
    {e1 e2 e3 : ExpHOL 64} {vals : List (ValueHOL 64)}
    (h : evalListHOLFinite s (h := fun x => Classical.propDecidable (s.memaddrs x)) [e1, e2, e3] = some vals) :
    ∃ v1 v2 v3,
      @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) e1 = some v1 ∧
      @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) e2 = some v2 ∧
      @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) e3 = some v3 ∧
      vals = [v1, v2, v3] := by
  rcases h1 : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) e1 with _ | v1
  · simp [evalListHOLFinite, evalListHOLExact, h1] at h
  rcases h2 : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) e2 with _ | v2
  · simp [evalListHOLFinite, evalListHOLExact, h1, h2] at h
  rcases h3 : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) e3 with _ | v3
  · simp [evalListHOLFinite, evalListHOLExact, h1, h2, h3] at h
  refine ⟨v1, v2, v3, rfl, rfl, rfl, ?_⟩
  simpa [evalListHOLFinite, evalListHOLExact, h1, h2, h3] using h.symm

private theorem evalList_six_eq {F : Type} {s : PanSemStateFiniteExact 64 F}
    {e1 e2 e3 e4 e5 e6 : ExpHOL 64} {vals : List (ValueHOL 64)}
    (h : evalListHOLFinite s (h := fun x => Classical.propDecidable (s.memaddrs x))
      [e1, e2, e3, e4, e5, e6] = some vals) :
    ∃ v1 v2 v3 v4 v5 v6,
      @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) e1 = some v1 ∧
      @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) e2 = some v2 ∧
      @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) e3 = some v3 ∧
      @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) e4 = some v4 ∧
      @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) e5 = some v5 ∧
      @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) e6 = some v6 ∧
      vals = [v1, v2, v3, v4, v5, v6] := by
  rcases h1 : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) e1 with _ | v1
  · simp [evalListHOLFinite, evalListHOLExact, h1] at h
  rcases h2 : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) e2 with _ | v2
  · simp [evalListHOLFinite, evalListHOLExact, h1, h2] at h
  rcases h3 : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) e3 with _ | v3
  · simp [evalListHOLFinite, evalListHOLExact, h1, h2, h3] at h
  rcases h4 : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) e4 with _ | v4
  · simp [evalListHOLFinite, evalListHOLExact, h1, h2, h3, h4] at h
  rcases h5 : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) e5 with _ | v5
  · simp [evalListHOLFinite, evalListHOLExact, h1, h2, h3, h4, h5] at h
  rcases h6 : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) e6 with _ | v6
  · simp [evalListHOLFinite, evalListHOLExact, h1, h2, h3, h4, h5, h6] at h
  refine ⟨v1, v2, v3, v4, v5, v6, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  simpa [evalListHOLFinite, evalListHOLExact, h1, h2, h3, h4, h5, h6] using h.symm

private theorem eval_u256_ws_plus {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    (he : WsEnv s0 s) {off : Nat} {v : ValueHOL 64}
    (hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .global (ofString "u256_ws"), .const (BitVec.ofNat 64 off)]) = some v) :
    v = .val (.word (BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 off)) := by
  simp only [evalHOLExact, evalListHOLExact, wordOpHOL] at hev
  rcases hgl : s.globals.lookup (ofString "u256_ws") with _ | gv
  · simp [hgl] at hev
  · rcases gv with ⟨⟨gw⟩⟩ | _ | _ <;> simp [hgl, valueIsWord, valueWord, wordOp] at hev
    have hgw := eval_global_word_eq_ofNat he.globals hgl
    rw [hgw] at hev
    simpa [BitVec.add_zero] using hev.symm

/-- `divmnu(q, r, u, m, v, n)` only writes inside `u256_ws` when `q` and `r` point into `u256_ws`
with sufficient room (`q_off + 128 ≤ 640`, `r_off + 64 ≤ 640`), `1 ≤ n ≤ 8`, and `n ≤ m ≤ 16`. -/
theorem divmnu_wsSafe {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    (he : WsEnv s0 s) {q_off r_off mv nv : Nat} {uw vw : BitVec 64}
    (hq_off : q_off + 16 * 8 ≤ 640) (hr_off : r_off + 8 * 8 ≤ 640)
    (hq : s.locals.lookup (ofString "q") =
      some (.val (.word (BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 q_off))))
    (hr : s.locals.lookup (ofString "r") =
      some (.val (.word (BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 r_off))))
    (_hu : s.locals.lookup (ofString "u") = some (.val (.word uw)))
    (hm : s.locals.lookup (ofString "m") = some (.val (.word (BitVec.ofNat 64 mv))))
    (_hv : s.locals.lookup (ofString "v") = some (.val (.word vw)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 nv))))
    (hn_ge : 1 ≤ nv) (hn_le : nv ≤ 8) (hm_le : mv ≤ 16) (hnm : nv ≤ mv) :
    WsSafe s (untypedGlobalBufIvls s0)
      (evaluateHOLFiniteState s
        (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
          (extractFn Guest.Software.guestFn_divmnu).body)) := by
  dsimp only [extractFn, Guest.Software.guestFn_divmnu]
  change WsSafe s (untypedGlobalBufIvls s0)
    (evaluateHOLFiniteState s
      (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (Prog.dec "i" Shape.one (Exp.const (BitVec.ofNat 64 0))
          (Prog.dec "j" Shape.one (Exp.const (BitVec.ofNat 64 0))
            (Prog.seq
              (Prog.ite (Exp.cmp Cmp.equal (Exp.var VarKind.local "n") (Exp.const (BitVec.ofNat 64 1)))
                (Prog.dec "d" Shape.one (Exp.load Shape.one (Exp.var VarKind.local "v"))
                  (Prog.dec "k" Shape.one (Exp.const (BitVec.ofNat 64 0))
                    (Prog.seq
                      (Prog.assign VarKind.local "j" (Exp.var VarKind.local "m"))
                      (Prog.seq
                      (Prog.while (Exp.cmp Cmp.lower (Exp.const (BitVec.ofNat 64 0)) (Exp.var VarKind.local "j"))
                        (Prog.seq
                          (Prog.assign VarKind.local "j" (Exp.op BinOp.sub [(Exp.var VarKind.local "j"), (Exp.const (BitVec.ofNat 64 1))]))
                          (Prog.decCall "qr" (Shape.comb [Shape.one, Shape.one]) "div64by32" [(Exp.var VarKind.local "k"), (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "u"), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "j"), (Exp.const (BitVec.ofNat 64 8))])])), (Exp.var VarKind.local "d")]
                            (Prog.seq
                              (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "q"), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "j"), (Exp.const (BitVec.ofNat 64 8))])]) (Exp.rField 0 (Exp.var VarKind.local "qr")))
                              (Prog.assign VarKind.local "k" (Exp.rField 1 (Exp.var VarKind.local "qr")))))))
                      (Prog.seq
                      (Prog.store (Exp.var VarKind.local "r") (Exp.var VarKind.local "k"))
                      (Prog.return (Exp.const (BitVec.ofNat 64 0))))))))
                Prog.skip)
              (Prog.dec "un" Shape.one (Exp.op BinOp.add [(Exp.var VarKind.global "u256_ws"), (Exp.const (BitVec.ofNat 64 0))])
                (Prog.dec "vn" Shape.one (Exp.op BinOp.add [(Exp.var VarKind.global "u256_ws"), (Exp.const (BitVec.ofNat 64 144))])
                  (Prog.decCall "s" Shape.one "nlz32" [(Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "v"), (Exp.panOp PanOp.mul [(Exp.op BinOp.sub [(Exp.var VarKind.local "n"), (Exp.const (BitVec.ofNat 64 1))]), (Exp.const (BitVec.ofNat 64 8))])]))]
                    (Prog.seq
                      (Prog.assign VarKind.local "i" (Exp.op BinOp.sub [(Exp.var VarKind.local "n"), (Exp.const (BitVec.ofNat 64 1))]))
                      (Prog.seq
                      (Prog.while (Exp.cmp Cmp.lower (Exp.const (BitVec.ofNat 64 0)) (Exp.var VarKind.local "i"))
                        (Prog.seq
                          (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "vn"), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "i"), (Exp.const (BitVec.ofNat 64 8))])]) (Exp.op BinOp.and [(Exp.op BinOp.or [(Exp.shift Shift.lsl (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "v"), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "i"), (Exp.const (BitVec.ofNat 64 8))])])) (Exp.var VarKind.local "s")), (Exp.shift Shift.lsr (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "v"), (Exp.panOp PanOp.mul [(Exp.op BinOp.sub [(Exp.var VarKind.local "i"), (Exp.const (BitVec.ofNat 64 1))]), (Exp.const (BitVec.ofNat 64 8))])])) (Exp.op BinOp.sub [(Exp.const (BitVec.ofNat 64 32)), (Exp.var VarKind.local "s")]))]), (Exp.const (BitVec.ofNat 64 4294967295))]))
                          (Prog.assign VarKind.local "i" (Exp.op BinOp.sub [(Exp.var VarKind.local "i"), (Exp.const (BitVec.ofNat 64 1))]))))
                      (Prog.seq
                      (Prog.store (Exp.var VarKind.local "vn") (Exp.op BinOp.and [(Exp.shift Shift.lsl (Exp.load Shape.one (Exp.var VarKind.local "v")) (Exp.var VarKind.local "s")), (Exp.const (BitVec.ofNat 64 4294967295))]))
                      (Prog.seq
                      (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "un"), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "m"), (Exp.const (BitVec.ofNat 64 8))])]) (Exp.shift Shift.lsr (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "u"), (Exp.panOp PanOp.mul [(Exp.op BinOp.sub [(Exp.var VarKind.local "m"), (Exp.const (BitVec.ofNat 64 1))]), (Exp.const (BitVec.ofNat 64 8))])])) (Exp.op BinOp.sub [(Exp.const (BitVec.ofNat 64 32)), (Exp.var VarKind.local "s")])))
                      (Prog.seq
                      (Prog.assign VarKind.local "i" (Exp.op BinOp.sub [(Exp.var VarKind.local "m"), (Exp.const (BitVec.ofNat 64 1))]))
                      (Prog.seq
                      (Prog.while (Exp.cmp Cmp.lower (Exp.const (BitVec.ofNat 64 0)) (Exp.var VarKind.local "i"))
                        (Prog.seq
                          (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "un"), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "i"), (Exp.const (BitVec.ofNat 64 8))])]) (Exp.op BinOp.and [(Exp.op BinOp.or [(Exp.shift Shift.lsl (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "u"), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "i"), (Exp.const (BitVec.ofNat 64 8))])])) (Exp.var VarKind.local "s")), (Exp.shift Shift.lsr (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "u"), (Exp.panOp PanOp.mul [(Exp.op BinOp.sub [(Exp.var VarKind.local "i"), (Exp.const (BitVec.ofNat 64 1))]), (Exp.const (BitVec.ofNat 64 8))])])) (Exp.op BinOp.sub [(Exp.const (BitVec.ofNat 64 32)), (Exp.var VarKind.local "s")]))]), (Exp.const (BitVec.ofNat 64 4294967295))]))
                          (Prog.assign VarKind.local "i" (Exp.op BinOp.sub [(Exp.var VarKind.local "i"), (Exp.const (BitVec.ofNat 64 1))]))))
                      (Prog.seq
                      (Prog.store (Exp.var VarKind.local "un") (Exp.op BinOp.and [(Exp.shift Shift.lsl (Exp.load Shape.one (Exp.var VarKind.local "u")) (Exp.var VarKind.local "s")), (Exp.const (BitVec.ofNat 64 4294967295))]))
                      (Prog.dec "vtop" Shape.one (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "vn"), (Exp.panOp PanOp.mul [(Exp.op BinOp.sub [(Exp.var VarKind.local "n"), (Exp.const (BitVec.ofNat 64 1))]), (Exp.const (BitVec.ofNat 64 8))])]))
                        (Prog.dec "vsec" Shape.one (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "vn"), (Exp.panOp PanOp.mul [(Exp.op BinOp.sub [(Exp.var VarKind.local "n"), (Exp.const (BitVec.ofNat 64 2))]), (Exp.const (BitVec.ofNat 64 8))])]))
                          (Prog.seq
                            (Prog.assign VarKind.local "j" (Exp.op BinOp.add [(Exp.op BinOp.sub [(Exp.var VarKind.local "m"), (Exp.var VarKind.local "n")]), (Exp.const (BitVec.ofNat 64 1))]))
                            (Prog.seq
                            (Prog.while (Exp.cmp Cmp.lower (Exp.const (BitVec.ofNat 64 0)) (Exp.var VarKind.local "j"))
                              divmnuOuterLoopBodyAST)
                            (Prog.seq
                            (Prog.assign VarKind.local "j" (Exp.op BinOp.add [(Exp.op BinOp.sub [(Exp.var VarKind.local "m"), (Exp.var VarKind.local "n")]), (Exp.const (BitVec.ofNat 64 1))]))
                            (Prog.seq
                            (Prog.while (Exp.cmp Cmp.lower (Exp.var VarKind.local "j") (Exp.var VarKind.local "m"))
                              (Prog.seq
                                (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "q"), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "j"), (Exp.const (BitVec.ofNat 64 8))])]) (Exp.const (BitVec.ofNat 64 0)))
                                (Prog.assign VarKind.local "j" (Exp.op BinOp.add [(Exp.var VarKind.local "j"), (Exp.const (BitVec.ofNat 64 1))]))))
                            (Prog.seq
                            (Prog.assign VarKind.local "i" (Exp.const (BitVec.ofNat 64 0)))
                            (Prog.seq
                            (Prog.while (Exp.cmp Cmp.lower (Exp.var VarKind.local "i") (Exp.var VarKind.local "n"))
                              (Prog.seq
                                (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "r"), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "i"), (Exp.const (BitVec.ofNat 64 8))])]) (Exp.op BinOp.or [(Exp.shift Shift.lsr (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "un"), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "i"), (Exp.const (BitVec.ofNat 64 8))])])) (Exp.var VarKind.local "s")), (Exp.op BinOp.and [(Exp.shift Shift.lsl (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "un"), (Exp.panOp PanOp.mul [(Exp.op BinOp.add [(Exp.var VarKind.local "i"), (Exp.const (BitVec.ofNat 64 1))]), (Exp.const (BitVec.ofNat 64 8))])])) (Exp.op BinOp.sub [(Exp.const (BitVec.ofNat 64 32)), (Exp.var VarKind.local "s")])), (Exp.const (BitVec.ofNat 64 4294967295))])]))
                                (Prog.assign VarKind.local "i" (Exp.op BinOp.add [(Exp.var VarKind.local "i"), (Exp.const (BitVec.ofNat 64 1))]))))
                            (Prog.return (Exp.const (BitVec.ofNat 64 0))))))))))))))))))))))))))
  dsimp only [InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural,
    Option.map, List.map]
  refine WsSafe.dec fun vi hvi _ => ?_
  obtain ⟨rfl⟩ : vi = .val (.word 0#64) := by simpa [evalHOLExact] using hvi.symm
  set s1 := setVarHOLFinite (ofString "i") (.val (.word 0#64)) s
  refine WsSafe.dec fun vj hvj _ => ?_
  obtain ⟨rfl⟩ : vj = .val (.word 0#64) := by simpa [evalHOLExact] using hvj.symm
  set s2 := setVarHOLFinite (ofString "j") (.val (.word 0#64)) s1
  have hs2_env : WsEnv s0 s2 := (he.with_locals_clock _ _).with_locals_clock _ _
  have hn_s2 : s2.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 nv))) := by
    simp [s2, s1, setVarHOLFinite, FUPDATE,
      show ofString "j" ≠ ofString "n" by decide,
      show ofString "i" ≠ ofString "n" by decide, hn]
  -- Step 1: `if (n == 1) { ... return 0; } else skip`
  refine WsSafe.seq ?_ ?_
  · refine WsSafe.ite (fun w hw hw0 => ?_) (fun _ => WsSafe.skip _ _)
    refine WsSafe.dec fun vd hvd _ => ?_
    obtain ⟨dw, rfl⟩ := eval_word_of_isWordValExp (s := s2) rfl hvd
    set s3 := setVarHOLFinite (ofString "d") (.val (.word dw)) s2
    refine WsSafe.dec fun vk hvk _ => ?_
    obtain ⟨rfl⟩ : vk = .val (.word 0#64) := by simpa [evalHOLExact] using hvk.symm
    set s4 := setVarHOLFinite (ofString "k") (.val (.word 0#64)) s3
    have hs4_env : WsEnv s0 s4 := (hs2_env.with_locals_clock _ _).with_locals_clock _ _
    have hm_s4 : s4.locals.lookup (ofString "m") = some (.val (.word (BitVec.ofNat 64 mv))) := by
      simp [s4, s3, s2, s1, setVarHOLFinite, FUPDATE,
        show ofString "k" ≠ ofString "m" by decide,
        show ofString "d" ≠ ofString "m" by decide,
        show ofString "j" ≠ ofString "m" by decide,
        show ofString "i" ≠ ofString "m" by decide, hm]
    have hj_s4 : s4.locals.lookup (ofString "j") = some (.val (.word 0#64)) := by
      simp [s4, s3, s2, setVarHOLFinite, FUPDATE,
        show ofString "k" ≠ ofString "j" by decide,
        show ofString "d" ≠ ofString "j" by decide]
    refine WsSafe.seq_assign_word hs4_env ⟨0#64, hj_s4⟩
      (by simp only [evalHOLExact]; exact hm_s4) fun hs5_env => ?_
    set s5 := setVarHOLFinite (ofString "j") (.val (.word (BitVec.ofNat 64 mv))) s4
    have hq_s5 : s5.locals.lookup (ofString "q") =
        some (.val (.word (BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 q_off))) := by
      simp [s5, s4, s3, s2, s1, setVarHOLFinite, FUPDATE,
        show ofString "j" ≠ ofString "q" by decide,
        show ofString "k" ≠ ofString "q" by decide,
        show ofString "d" ≠ ofString "q" by decide,
        show ofString "i" ≠ ofString "q" by decide, hq]
    have hk_s5 : s5.locals.lookup (ofString "k") = some (.val (.word 0#64)) := by
      simp [s5, s4, setVarHOLFinite, FUPDATE, show ofString "j" ≠ ofString "k" by decide]
    have hj_s5 : s5.locals.lookup (ofString "j") = some (.val (.word (BitVec.ofNat 64 mv))) := by
      simp [s5, setVarHOLFinite, FUPDATE]
    have hl_n1 := divmnu_n1_loop_wsSafe hs5_env hm_le hq_off hq_s5 hk_s5 hj_s5
    refine WsSafe.seq hl_n1.1 fun hn_l1 _ => ?_
    obtain ⟨hs6_env, ⟨kw', hk_s6⟩, hother_s6⟩ := hl_n1.2 hn_l1
    have hr_s6 : (evaluateHOLFiniteState s5
        (.while (.cmp .lower (.const 0#64) (.var .local (ofString "j")))
          (.seq (.assign .local (ofString "j") (.op .sub [.var .local (ofString "j"), .const 1#64]))
            (.decCall (ofString "qr") (.comb [.one, .one]) (ofString "div64by32")
              [.var .local (ofString "k"),
               .load .one (.op .add [.var .local (ofString "u"), .panop .mul [.var .local (ofString "j"), .const 8#64]]),
               .var .local (ofString "d")]
              (.seq
                (.store (.op .add [.var .local (ofString "q"), .panop .mul [.var .local (ofString "j"), .const 8#64]])
                  (.rfield 0 (.var .local (ofString "qr"))))
                (.assign .local (ofString "k") (.rfield 1 (.var .local (ofString "qr"))))))))).2.locals.lookup (ofString "r") =
        some (.val (.word (BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 r_off))) := by
      rw [hother_s6 (ofString "r") (by decide) (by decide)]
      simp [s5, s4, s3, s2, s1, setVarHOLFinite, FUPDATE,
        show ofString "j" ≠ ofString "r" by decide,
        show ofString "k" ≠ ofString "r" by decide,
        show ofString "d" ≠ ofString "r" by decide,
        show ofString "i" ≠ ofString "r" by decide, hr]
    refine WsSafe.seq_store_ws_const_off hs6_env (off := r_off)
      (by simp only [evalHOLExact]; exact hr_s6)
      (by omega)
      (fun v hv => ⟨kw', eval_word_of_local hk_s6 hv⟩)
      fun _ _ _ => WsSafe.return_exp _ _ _
  -- Step 2: continuation when `if (n == 1) ... else skip` finishes with `none`
  intro hn_ite _
  -- Since the `n == 1` branch always ends in `.return 0` (never `none`), we must have `nv ≠ 1` and `s_after = s2`!
  have hite_eq : nv ≠ 1 ∧
      (evaluateHOLFiniteState s2
        (.ite (.cmp .equal (.var .local (ofString "n")) (.const 1#64))
          (.dec (ofString "d") .one (.load .one (.var .local (ofString "v")))
            (.dec (ofString "k") .one (.const 0#64)
              (.seq (.assign .local (ofString "j") (.var .local (ofString "m")))
                (.seq
                  (.while (.cmp .lower (.const 0#64) (.var .local (ofString "j")))
                    (.seq (.assign .local (ofString "j") (.op .sub [.var .local (ofString "j"), .const 1#64]))
                      (.decCall (ofString "qr") (.comb [.one, .one]) (ofString "div64by32")
                        [.var .local (ofString "k"),
                         .load .one (.op .add [.var .local (ofString "u"), .panop .mul [.var .local (ofString "j"), .const 8#64]]),
                         .var .local (ofString "d")]
                        (.seq
                          (.store (.op .add [.var .local (ofString "q"), .panop .mul [.var .local (ofString "j"), .const 8#64]])
                            (.rfield 0 (.var .local (ofString "qr"))))
                          (.assign .local (ofString "k") (.rfield 1 (.var .local (ofString "qr"))))))))
                  (.seq (.store (.var .local (ofString "r")) (.var .local (ofString "k")))
                    (.return (.const 0#64)))))))
          .skip)).2 = s2 := by
    rw [evaluateHOLFiniteState_ite] at hn_ite ⊢
    by_cases hnv1 : nv = 1
    · subst hnv1
      have hw1 : @evalHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a))
          (.cmp .equal (.var .local (ofString "n")) (.const 1#64)) = some (.val (.word 1#64)) := by
        simp [evalHOLExact, hn_s2, wordCmpHOL]
      rw [hw1] at hn_ite
      dsimp only at hn_ite
      rw [if_neg (by decide : (1#64 : BitVec 64) ≠ 0)] at hn_ite
      -- The `yes` branch ends with `.return (.const 0#64)`, so its `.1` can never be `none`!
      exfalso
      revert hn_ite
      rw [evaluateHOLFiniteState_dec_total]; dsimp only
      split; · simp
      split; swap; · simp
      rw [evaluateHOLFiniteState_dec_total]; dsimp only
      split; · simp
      split; swap; · simp
      rw [evaluateHOLFiniteState_seq_line780]
      rcases evaluateHOLFiniteState _ (.assign _ _ _) with ⟨ra, sa⟩
      cases ra; swap; · simp
      dsimp only
      rw [evaluateHOLFiniteState_seq_line780]
      rcases evaluateHOLFiniteState sa (.while _ _) with ⟨rw1, sw1⟩
      cases rw1; swap; · simp
      dsimp only
      rw [evaluateHOLFiniteState_seq_line780]
      rcases evaluateHOLFiniteState sw1 (.store _ _) with ⟨rs1, ss1⟩
      cases rs1; swap; · simp
      dsimp only
      rw [evaluateHOLFiniteState_return]
      simp [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL]
    · have hw0 : @evalHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a))
          (.cmp .equal (.var .local (ofString "n")) (.const 1#64)) = some (.val (.word 0#64)) := by
        simp only [evalHOLExact, hn_s2, wordCmpHOL]
        have hcmp_f : ¬ ((BitVec.ofNat 64 nv == 1#64) = true) := by
          simp only [beq_iff_eq]
          intro heq
          have := congrArg BitVec.toNat heq
          simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show nv < 2 ^ 64 by omega)] at this
          omega
        simp [hcmp_f]
      rw [hw0]
      dsimp only
      simp only [ite_true, evaluateHOLFiniteState_skip]
      exact ⟨hnv1, rfl⟩
  rw [hite_eq.2]
  have hn_ge2 : 2 ≤ nv := by have := hite_eq.1; omega
  -- Now in `s2`, `2 ≤ nv ≤ 8` and `nv ≤ mv ≤ 16`.
  refine WsSafe.dec fun vun hvun _ => ?_
  rw [eval_u256_ws_plus hs2_env hvun]
  set s3 := setVarHOLFinite (ofString "un")
    (.val (.word (BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 0))) s2
  have hs3_env : WsEnv s0 s3 := hs2_env.with_locals_clock _ _
  refine WsSafe.dec fun vvn hvvn _ => ?_
  rw [eval_u256_ws_plus hs3_env hvvn]
  set s4 := setVarHOLFinite (ofString "vn")
    (.val (.word (BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 144))) s3
  have hs4_env : WsEnv s0 s4 := hs3_env.with_locals_clock _ _
  refine WsSafe.decCall_ro hs4_env (by decide) fun vs cpost_s hs5_env hsh_s _ => ?_
  obtain ⟨ws, rfl⟩ := eval_word_of_shape_one (Or.inr hsh_s)
  set s5 := setVarHOLFinite (ofString "s") (.val (.word ws)) { cpost_s with locals := s4.locals }
  have hi_s5 : s5.locals.lookup (ofString "i") = some (.val (.word 0#64)) := by
    simp [s5, s4, s3, s2, s1, setVarHOLFinite, FUPDATE,
      show ofString "s" ≠ ofString "i" by decide,
      show ofString "vn" ≠ ofString "i" by decide,
      show ofString "un" ≠ ofString "i" by decide,
      show ofString "j" ≠ ofString "i" by decide]
  have hn_s5 : s5.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 nv))) := by
    simp [s5, s4, s3, s2, s1, setVarHOLFinite, FUPDATE,
      show ofString "s" ≠ ofString "n" by decide,
      show ofString "vn" ≠ ofString "n" by decide,
      show ofString "un" ≠ ofString "n" by decide,
      show ofString "j" ≠ ofString "n" by decide,
      show ofString "i" ≠ ofString "n" by decide, hn]
  have hev_nm1 : @evalHOLExact 64 F _ s5.toExact (fun a => Classical.propDecidable (s5.memaddrs a))
      (.op .sub [.var .local (ofString "n"), .const 1#64]) =
      some (.val (.word (BitVec.ofNat 64 (nv - 1)))) := by
    simp only [evalHOLExact, evalListHOLExact, hn_s5, wordOpHOL, wordOp,
      valueIsWord, valueWord, List.all, List.map, Bool.and_self, ↓reduceIte, Option.map]
    congr 3; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  refine WsSafe.seq_assign_word hs5_env ⟨0#64, hi_s5⟩ hev_nm1 fun hs6_env => ?_
  set s6 := setVarHOLFinite (ofString "i") (.val (.word (BitVec.ofNat 64 (nv - 1)))) s5
  have hvn_s6 : s6.locals.lookup (ofString "vn") =
      some (.val (.word (BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 144))) := by
    simp [s6, s5, s4, setVarHOLFinite, FUPDATE,
      show ofString "i" ≠ ofString "vn" by decide,
      show ofString "s" ≠ ofString "vn" by decide]
  have hi_s6 : s6.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 (nv - 1)))) := by
    simp [s6, setVarHOLFinite, FUPDATE]
  -- Loop 1: `while (0 < i)` storing `vn + i*8` for `1 ≤ i ≤ nv - 1`
  have hw_vn := WsSafe.while_down_post_store hs6_env
    (cnt := ofString "i") (base := ofString "vn")
    (valExp := .op .and [.op .or [
      .shift .lsl (.load .one (.op .add [.var .local (ofString "v"), .panop .mul [.var .local (ofString "i"), .const 8#64]])) (.var .local (ofString "s")),
      .shift .lsr (.load .one (.op .add [.var .local (ofString "v"), .panop .mul [.op .sub [.var .local (ofString "i"), .const 1#64], .const 8#64]])) (.op .sub [.const 32#64, .var .local (ofString "s")])],
      .const 4294967295#64])
    (by decide) hvn_s6 hi_s6 (by omega) (fun k _ hk => by omega) rfl
  dsimp only at hw_vn
  refine WsSafe.seq hw_vn.1 fun hn_wvn _ => ?_
  set s7 := (evaluateHOLFiniteState s6 _).2
  obtain ⟨hs7_env, ⟨iv7, _, hi_s7⟩, hother_s7⟩ := hw_vn.2 hn_wvn
  have hvn_s7 : s7.locals.lookup (ofString "vn") =
      some (.val (.word (BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 144))) := by
    rw [hother_s7 (ofString "vn") (by decide)]; exact hvn_s6
  -- Store `vn[0]` (`144`)
  refine WsSafe.seq_store_ws_const_off hs7_env (off := 144)
    (by simp only [evalHOLExact]; exact hvn_s7) (by omega)
    (fun _ hv => eval_word_of_isWordValExp rfl hv) fun s8 hs8_env hs8_loc => ?_
  have hun_s8 : s8.locals.lookup (ofString "un") =
      some (.val (.word (BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 0))) := by
    rw [hs8_loc, hother_s7 (ofString "un") (by decide)]
    simp [s6, s5, s4, s3, setVarHOLFinite, FUPDATE,
      show ofString "i" ≠ ofString "un" by decide,
      show ofString "s" ≠ ofString "un" by decide,
      show ofString "vn" ≠ ofString "un" by decide]
  have hm_s8 : s8.locals.lookup (ofString "m") = some (.val (.word (BitVec.ofNat 64 mv))) := by
    rw [hs8_loc, hother_s7 (ofString "m") (by decide)]
    simp [s6, s5, s4, s3, s2, s1, setVarHOLFinite, FUPDATE,
      show ofString "i" ≠ ofString "m" by decide,
      show ofString "s" ≠ ofString "m" by decide,
      show ofString "vn" ≠ ofString "m" by decide,
      show ofString "un" ≠ ofString "m" by decide,
      show ofString "j" ≠ ofString "m" by decide, hm]
  -- Store `un + m*8` (`mv ≤ 16`, so `0 + mv*8 + 8 ≤ 136 ≤ 640`)
  refine WsSafe.seq_store_ws_scaled hs8_env (off := 0) (idx := mv)
    (by simp only [evalHOLExact]; exact hun_s8)
    (by simp only [evalHOLExact]; exact hm_s8)
    (by omega)
    (fun _ hv => eval_word_of_isWordValExp rfl hv) fun s9 hs9_env hs9_loc => ?_
  have hi_s9 : s9.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 iv7))) := by
    rw [hs9_loc, hs8_loc]; exact hi_s7
  have hm_s9 : s9.locals.lookup (ofString "m") = some (.val (.word (BitVec.ofNat 64 mv))) := by
    rw [hs9_loc]; exact hm_s8
  have hev_mm1 : @evalHOLExact 64 F _ s9.toExact (fun a => Classical.propDecidable (s9.memaddrs a))
      (.op .sub [.var .local (ofString "m"), .const 1#64]) =
      some (.val (.word (BitVec.ofNat 64 (mv - 1)))) := by
    simp only [evalHOLExact, evalListHOLExact, hm_s9, wordOpHOL, wordOp,
      valueIsWord, valueWord, List.all, List.map, Bool.and_self, ↓reduceIte, Option.map]
    congr 3; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  refine WsSafe.seq_assign_word hs9_env ⟨_, hi_s9⟩ hev_mm1 fun hs10_env => ?_
  set s10 := setVarHOLFinite (ofString "i") (.val (.word (BitVec.ofNat 64 (mv - 1)))) s9
  have hun_s10 : s10.locals.lookup (ofString "un") =
      some (.val (.word (BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 0))) := by
    rw [show s10.locals.lookup (ofString "un") = s9.locals.lookup (ofString "un") by
      simp [s10, setVarHOLFinite, FUPDATE, show ofString "i" ≠ ofString "un" by decide], hs9_loc]
    exact hun_s8
  have hi_s10 : s10.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 (mv - 1)))) := by
    simp [s10, setVarHOLFinite, FUPDATE]
  -- Loop 2: `while (0 < i)` storing `un + i*8` for `1 ≤ i ≤ mv - 1`
  have hw_un := WsSafe.while_down_post_store hs10_env
    (cnt := ofString "i") (base := ofString "un")
    (valExp := .op .and [.op .or [
      .shift .lsl (.load .one (.op .add [.var .local (ofString "u"), .panop .mul [.var .local (ofString "i"), .const 8#64]])) (.var .local (ofString "s")),
      .shift .lsr (.load .one (.op .add [.var .local (ofString "u"), .panop .mul [.op .sub [.var .local (ofString "i"), .const 1#64], .const 8#64]])) (.op .sub [.const 32#64, .var .local (ofString "s")])],
      .const 4294967295#64])
    (by decide) hun_s10 hi_s10 (by omega) (fun k _ hk => by omega) rfl
  dsimp only at hw_un
  refine WsSafe.seq hw_un.1 fun hn_wun _ => ?_
  set s11 := (evaluateHOLFiniteState s10 _).2
  obtain ⟨hs11_env, ⟨iv11, _, hi_s11⟩, hother_s11⟩ := hw_un.2 hn_wun
  have hun_s11 : s11.locals.lookup (ofString "un") =
      some (.val (.word (BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 0))) := by
    rw [hother_s11 (ofString "un") (by decide)]; exact hun_s10
  -- Store `un[0]` (`0`)
  refine WsSafe.seq_store_ws_const_off hs11_env (off := 0)
    (by simp only [evalHOLExact]; exact hun_s11) (by omega)
    (fun _ hv => eval_word_of_isWordValExp rfl hv) fun s12 hs12_env hs12_loc => ?_
  refine WsSafe.dec fun vvtop hvvtop _ => ?_
  obtain ⟨w_vtop, rfl⟩ := eval_word_of_isWordValExp (s := s12) rfl hvvtop
  set s13 := setVarHOLFinite (ofString "vtop") (.val (.word w_vtop)) s12
  refine WsSafe.dec fun vvsec hvvsec _ => ?_
  obtain ⟨w_vsec, rfl⟩ := eval_word_of_isWordValExp (s := s13) rfl hvvsec
  set s14 := setVarHOLFinite (ofString "vsec") (.val (.word w_vsec)) s13
  have hs14_env : WsEnv s0 s14 := (hs12_env.with_locals_clock _ _).with_locals_clock _ _
  have hkeep14 : ∀ x, x ≠ ofString "vsec" → x ≠ ofString "vtop" → x ≠ ofString "i" →
      x ≠ ofString "s" → x ≠ ofString "vn" → x ≠ ofString "un" →
      s14.locals.lookup x = s2.locals.lookup x := by
    intro x h1 h2 h3 h4 h5 h6
    have step14 : s14.locals.lookup x = s12.locals.lookup x := by
      simp [s14, s13, setVarHOLFinite, FUPDATE, Ne.symm h1, Ne.symm h2]
    rw [step14, hs12_loc, hother_s11 x h3]
    have step10 : s10.locals.lookup x = s9.locals.lookup x := by
      simp [s10, setVarHOLFinite, FUPDATE, Ne.symm h3]
    rw [step10, hs9_loc, hs8_loc, hother_s7 x h3]
    simp [s6, s5, s4, s3, setVarHOLFinite, FUPDATE,
      Ne.symm h3, Ne.symm h4, Ne.symm h5, Ne.symm h6]
  have hm_s14 : s14.locals.lookup (ofString "m") = some (.val (.word (BitVec.ofNat 64 mv))) := by
    rw [hkeep14 (ofString "m") (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp [s2, s1, setVarHOLFinite, FUPDATE,
      show ofString "j" ≠ ofString "m" by decide,
      show ofString "i" ≠ ofString "m" by decide, hm]
  have hn_s14 : s14.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 nv))) := by
    rw [hkeep14 (ofString "n") (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hn_s2
  have hj_s14 : s14.locals.lookup (ofString "j") = some (.val (.word 0#64)) := by
    rw [hkeep14 (ofString "j") (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp [s2, setVarHOLFinite, FUPDATE]
  have hev_mnp1 : @evalHOLExact 64 F _ s14.toExact (fun a => Classical.propDecidable (s14.memaddrs a))
      (.op .add [.op .sub [.var .local (ofString "m"), .var .local (ofString "n")], .const 1#64]) =
      some (.val (.word (BitVec.ofNat 64 (mv - nv + 1)))) := by
    simp only [evalHOLExact, evalListHOLExact, hm_s14, hn_s14, wordOpHOL, wordOp,
      valueIsWord, valueWord, List.all, List.map, Bool.and_self, ↓reduceIte, Option.map, List.foldr]
    congr 3
    rw [show (1#64 + 0 : BitVec 64) = 1#64 from BitVec.add_zero _]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  refine WsSafe.seq_assign_word hs14_env ⟨0#64, hj_s14⟩ hev_mnp1 fun hs15_env => ?_
  set s15 := setVarHOLFinite (ofString "j") (.val (.word (BitVec.ofNat 64 (mv - nv + 1)))) s14
  have hq_s15 : s15.locals.lookup (ofString "q") =
      some (.val (.word (BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 q_off))) := by
    rw [show s15.locals.lookup (ofString "q") = s14.locals.lookup (ofString "q") by
      simp [s15, setVarHOLFinite, FUPDATE, show ofString "j" ≠ ofString "q" by decide]]
    rw [hkeep14 (ofString "q") (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp [s2, s1, setVarHOLFinite, FUPDATE,
      show ofString "j" ≠ ofString "q" by decide,
      show ofString "i" ≠ ofString "q" by decide, hq]
  have hun_s15 : s15.locals.lookup (ofString "un") =
      some (.val (.word (BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 0))) := by
    rw [show s15.locals.lookup (ofString "un") = s12.locals.lookup (ofString "un") by
      simp [s15, s14, s13, setVarHOLFinite, FUPDATE,
        show ofString "j" ≠ ofString "un" by decide,
        show ofString "vsec" ≠ ofString "un" by decide,
        show ofString "vtop" ≠ ofString "un" by decide], hs12_loc]
    exact hun_s11
  have hn_s15 : s15.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 nv))) := by
    rw [show s15.locals.lookup (ofString "n") = s14.locals.lookup (ofString "n") by
      simp [s15, setVarHOLFinite, FUPDATE, show ofString "j" ≠ ofString "n" by decide]]
    exact hn_s14
  have hj_s15 : s15.locals.lookup (ofString "j") = some (.val (.word (BitVec.ofNat 64 (mv - nv + 1)))) := by
    simp [s15, setVarHOLFinite, FUPDATE]
  have hi_s15 : ∃ wi : BitVec 64, s15.locals.lookup (ofString "i") = some (.val (.word wi)) := by
    refine ⟨BitVec.ofNat 64 iv11, ?_⟩
    rw [show s15.locals.lookup (ofString "i") = s12.locals.lookup (ofString "i") by
      simp [s15, s14, s13, setVarHOLFinite, FUPDATE,
        show ofString "j" ≠ ofString "i" by decide,
        show ofString "vsec" ≠ ofString "i" by decide,
        show ofString "vtop" ≠ ofString "i" by decide], hs12_loc]
    exact hi_s11
  -- Outer loop: `while (0 < j)`
  have hl_outer := divmnu_outer_loop_wsSafe hs15_env hq_off hq_s15 hun_s15 hn_s15 hj_s15 hi_s15
    hn_ge2 hn_le hm_le hnm (le_refl _)
  dsimp only at hl_outer
  refine WsSafe.seq hl_outer.1 fun hn_outer _ => ?_
  set s16 := (evaluateHOLFiniteState s15 _).2
  obtain ⟨hs16_env, ⟨jv16, hj_s16⟩, ⟨wi16, hi_s16⟩, hother_s16⟩ := hl_outer.2 hn_outer
  have hm_s16 : s16.locals.lookup (ofString "m") =
      some (.val (.word (BitVec.ofNat 64 mv))) := by
    rw [hother_s16 (ofString "m") (by decide) (by decide)]
    rw [show s15.locals.lookup (ofString "m") = s14.locals.lookup (ofString "m") by
      simp [s15, setVarHOLFinite, FUPDATE, show ofString "j" ≠ ofString "m" by decide]]
    exact hm_s14
  have hn_s16 : s16.locals.lookup (ofString "n") =
      some (.val (.word (BitVec.ofNat 64 nv))) := by
    rw [hother_s16 (ofString "n") (by decide) (by decide)]; exact hn_s15
  have hev_mnp1_16 : @evalHOLExact 64 F _ s16.toExact
      (fun a => Classical.propDecidable (s16.memaddrs a))
      (.op .add [.op .sub [.var .local (ofString "m"), .var .local (ofString "n")], .const 1#64]) =
      some (.val (.word (BitVec.ofNat 64 (mv - nv + 1)))) := by
    simp only [evalHOLExact, evalListHOLExact, hm_s16, hn_s16, wordOpHOL, wordOp,
      valueIsWord, valueWord, List.all, List.map, Bool.and_self, ↓reduceIte, Option.map, List.foldr]
    congr 3
    rw [show (1#64 + 0 : BitVec 64) = 1#64 from BitVec.add_zero _]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  refine WsSafe.seq_assign_word hs16_env ⟨_, hj_s16⟩ hev_mnp1_16 fun hs17_env => ?_
  set s17 := setVarHOLFinite (ofString "j") (.val (.word (BitVec.ofNat 64 (mv - nv + 1)))) s16
  have hq_s17 : s17.locals.lookup (ofString "q") =
      some (.val (.word (BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 q_off))) := by
    rw [show s17.locals.lookup (ofString "q") = s16.locals.lookup (ofString "q") by
      simp [s17, setVarHOLFinite, FUPDATE, show ofString "j" ≠ ofString "q" by decide]]
    rw [hother_s16 (ofString "q") (by decide) (by decide)]; exact hq_s15
  have hm_s17 : s17.locals.lookup (ofString "m") = some (.val (.word (BitVec.ofNat 64 mv))) := by
    rw [show s17.locals.lookup (ofString "m") = s16.locals.lookup (ofString "m") by
      simp [s17, setVarHOLFinite, FUPDATE, show ofString "j" ≠ ofString "m" by decide]]
    exact hm_s16
  have hj_s17 : s17.locals.lookup (ofString "j") = some (.val (.word (BitVec.ofNat 64 (mv - nv + 1)))) := by
    simp [s17, setVarHOLFinite, FUPDATE]
  -- Quotient high-limb zeroing loop: `while (j < m) { store (q + j*8) 0; j := j + 1 }`
  have hw_qzero := WsSafe.while_up_store hs17_env
    (cnt := ofString "j") (base := ofString "q")
    (limExp := .var .local (ofString "m")) (valExp := .const 0#64)
    (off := q_off) (lim := mv) (idx0 := mv - nv + 1)
    (by decide)
    (fun t hoth => by simp only [evalHOLExact]; rw [hoth (ofString "m") (by decide)]; exact hm_s17)
    hq_s17 hj_s17 (by omega) (by omega) (fun k hk => by omega) rfl
  dsimp only at hw_qzero
  refine WsSafe.seq hw_qzero.1 fun hn_qz _ => ?_
  set s18 := (evaluateHOLFiniteState s17 _).2
  obtain ⟨hs18_env, _, hother_s18⟩ := hw_qzero.2 hn_qz
  have hi_s18 : s18.locals.lookup (ofString "i") = some (.val (.word wi16)) := by
    rw [hother_s18 (ofString "i") (by decide)]
    rw [show s17.locals.lookup (ofString "i") = s16.locals.lookup (ofString "i") by
      simp [s17, setVarHOLFinite, FUPDATE, show ofString "j" ≠ ofString "i" by decide]]
    exact hi_s16
  refine WsSafe.seq_assign_word hs18_env ⟨wi16, hi_s18⟩ (w := 0#64) rfl fun hs19_env => ?_
  set s19 := setVarHOLFinite (ofString "i") (.val (.word 0#64)) s18
  have hr_s19 : s19.locals.lookup (ofString "r") =
      some (.val (.word (BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 r_off))) := by
    rw [show s19.locals.lookup (ofString "r") = s18.locals.lookup (ofString "r") by
      simp [s19, setVarHOLFinite, FUPDATE, show ofString "i" ≠ ofString "r" by decide]]
    rw [hother_s18 (ofString "r") (by decide)]
    rw [show s17.locals.lookup (ofString "r") = s16.locals.lookup (ofString "r") by
      simp [s17, setVarHOLFinite, FUPDATE, show ofString "j" ≠ ofString "r" by decide]]
    rw [hother_s16 (ofString "r") (by decide) (by decide)]
    rw [show s15.locals.lookup (ofString "r") = s14.locals.lookup (ofString "r") by
      simp [s15, setVarHOLFinite, FUPDATE, show ofString "j" ≠ ofString "r" by decide]]
    rw [hkeep14 (ofString "r") (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp [s2, s1, setVarHOLFinite, FUPDATE,
      show ofString "j" ≠ ofString "r" by decide,
      show ofString "i" ≠ ofString "r" by decide, hr]
  have hn_s19 : s19.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 nv))) := by
    rw [show s19.locals.lookup (ofString "n") = s18.locals.lookup (ofString "n") by
      simp [s19, setVarHOLFinite, FUPDATE, show ofString "i" ≠ ofString "n" by decide]]
    rw [hother_s18 (ofString "n") (by decide)]
    rw [show s17.locals.lookup (ofString "n") = s16.locals.lookup (ofString "n") by
      simp [s17, setVarHOLFinite, FUPDATE, show ofString "j" ≠ ofString "n" by decide]]
    exact hn_s16
  have hi_s19 : s19.locals.lookup (ofString "i") = some (.val (.word 0#64)) := by
    simp [s19, setVarHOLFinite, FUPDATE]
  -- Remainder loop: `while (i < n) { store (r + i*8) (...); i := i + 1 }`
  have hw_rem := WsSafe.while_up_store hs19_env
    (cnt := ofString "i") (base := ofString "r")
    (limExp := .var .local (ofString "n"))
    (valExp := .op .or [
      .shift .lsr (.load .one (.op .add [.var .local (ofString "un"), .panop .mul [.var .local (ofString "i"), .const 8#64]])) (.var .local (ofString "s")),
      .op .and [
        .shift .lsl (.load .one (.op .add [.var .local (ofString "un"), .panop .mul [.op .add [.var .local (ofString "i"), .const 1#64], .const 8#64]])) (.op .sub [.const 32#64, .var .local (ofString "s")]),
        .const 4294967295#64]])
    (off := r_off) (lim := nv) (idx0 := 0)
    (by decide)
    (fun t hoth => by simp only [evalHOLExact]; rw [hoth (ofString "n") (by decide)]; exact hn_s19)
    hr_s19 hi_s19 (by omega) (by omega) (fun k hk => by omega) rfl
  exact WsSafe.seq hw_rem.1 fun _ _ => WsSafe.return_exp _ _ _

/-! ## 7. `digits_divmod`, `u256_divmod`, `eps_of_wsSafe`, and arithmetic specs -/

private theorem eval_or4_ne_zero {F : Type} {s : PanSemStateFiniteExact 64 F}
    {nm : MlS} {b0 b1 b2 b3 : BitVec 64}
    (hb : s.locals.lookup nm =
      some (.rStruct [.val (.word b0), .val (.word b1), .val (.word b2), .val (.word b3)]))
    (hcmp : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .equal
        (.op .or [.rfield 0 (.var .local nm), .rfield 1 (.var .local nm),
                  .rfield 2 (.var .local nm), .rfield 3 (.var .local nm)])
        (.const 0#64)) = some (.val (.word 0#64))) :
    (b0 ||| b1 ||| b2 ||| b3) ≠ 0 := by
  intro hz
  have h1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .equal
        (.op .or [.rfield 0 (.var .local nm), .rfield 1 (.var .local nm),
                  .rfield 2 (.var .local nm), .rfield 3 (.var .local nm)])
        (.const 0#64)) = some (.val (.word 1#64)) := by
    simp only [evalHOLExact, evalListHOLExact, hb, wordOpHOL, wordOp, valueIsWord, valueWord,
      List.getElem?_cons_zero, List.getElem?_cons_succ,
      List.all, List.map, Bool.and_self, ↓reduceIte, Option.map, List.foldr]
    have hz' : OrOp.or b0 (OrOp.or b1 (OrOp.or b2 (OrOp.or b3 0))) = 0#64 := by
      change (b0 ||| (b1 ||| (b2 ||| (b3 ||| 0#64)))) = 0#64
      simpa [BitVec.or_zero, BitVec.or_assoc] using hz
    rw [hz']
    simp [wordCmpHOL]
  rw [h1] at hcmp
  simp at hcmp

theorem digits_divmod_wsSafe {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    (he : WsEnv s0 s) {mv : Nat} {uw d0 d1 d2 d3 : BitVec 64}
    (hu : s.locals.lookup (ofString "u") = some (.val (.word uw)))
    (hm : s.locals.lookup (ofString "m") = some (.val (.word (BitVec.ofNat 64 mv))))
    (hd : s.locals.lookup (ofString "d") =
      some (.rStruct [.val (.word d0), .val (.word d1), .val (.word d2), .val (.word d3)]))
    (hm_le : mv ≤ 16)
    (hd_nz : (d0 ||| d1 ||| d2 ||| d3) ≠ 0) :
    WsSafe s (untypedGlobalBufIvls s0)
      (evaluateHOLFiniteState s
        (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
          (extractFn Guest.Software.guestFn_digits_divmod).body)) := by
  dsimp only [extractFn, Guest.Software.guestFn_digits_divmod,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural,
    Option.map, List.map]
  refine WsSafe.dec fun vq hvq _ => ?_
  rw [eval_u256_ws_plus he hvq]
  set s1 := setVarHOLFinite (ofString "q")
    (.val (.word (BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 216))) s
  have hs1_env : WsEnv s0 s1 := he.with_locals_clock _ _
  refine WsSafe.dec fun vr hvr _ => ?_
  rw [eval_u256_ws_plus hs1_env hvr]
  set s2 := setVarHOLFinite (ofString "r")
    (.val (.word (BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 352))) s1
  have hs2_env : WsEnv s0 s2 := hs1_env.with_locals_clock _ _
  refine WsSafe.dec fun vv hvv _ => ?_
  rw [eval_u256_ws_plus hs2_env hvv]
  set s3 := setVarHOLFinite (ofString "v")
    (.val (.word (BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 560))) s2
  have hs3_env : WsEnv s0 s3 := hs2_env.with_locals_clock _ _
  have hv_s3 : s3.locals.lookup (ofString "v") =
      some (.val (.word (BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 560))) := by
    simp [s3, setVarHOLFinite, FUPDATE]
  have hd_s3 : s3.locals.lookup (ofString "d") =
      some (.rStruct [.val (.word d0), .val (.word d1), .val (.word d2), .val (.word d3)]) := by
    simp [s3, s2, s1, setVarHOLFinite, FUPDATE,
      show ofString "v" ≠ ofString "d" by decide,
      show ofString "r" ≠ ofString "d" by decide,
      show ofString "q" ≠ ofString "d" by decide, hd]
  -- Call `u256_to_digits(v, d)` and track nonzero-digit postcondition on `s4.memory`!
  have hcall_td : WsSafe s3 (untypedGlobalBufIvls s0)
      (evaluateHOLFiniteState s3
        (.call (some (none, none)) (ofString "u256_to_digits")
          [.var .local (ofString "v"), .var .local (ofString "d")])) ∧
      ((evaluateHOLFiniteState s3
        (.call (some (none, none)) (ofString "u256_to_digits")
          [.var .local (ofString "v"), .var .local (ofString "d")])).1 = none →
        let s4 := (evaluateHOLFiniteState s3
          (.call (some (none, none)) (ofString "u256_to_digits")
            [.var .local (ofString "v"), .var .local (ofString "d")])).2
        WsEnv s0 s4 ∧ s4.locals = s3.locals ∧
        ∃ k : Nat, k < 8 ∧ ∃ wk : BitVec 64, wk ≠ 0 ∧
          s4.memory (BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 560 +
            BitVec.ofNat 64 (8 * k)) = .word wk) := by
    refine ⟨WsSafe.call_void ?_, ?_⟩
    · intro vals body callee rs hargs hl _
      obtain ⟨v1, v2, hv1, hv2, rfl⟩ := evalList_two_eq hargs
      have hv1_eq : v1 = .val (.word (BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 560)) := by
        simpa [evalHOLExact, hv_s3] using hv1.symm
      have hv2_eq : v2 = .rStruct [.val (.word d0), .val (.word d1), .val (.word d2), .val (.word d3)] := by
        simpa [evalHOLExact, hd_s3] using hv2.symm
      subst hv1_eq hv2_eq
      rw [hs3_env.code] at hl
      obtain ⟨_, _, hinj_v, rfl, hp_cal, ha_cal, _, _⟩ := lookup_u256_to_digits_locals hl
      simp only [List.cons.injEq] at hinj_v
      obtain ⟨rfl, rfl, _⟩ := hinj_v
      exact (u256_to_digits_wsSafe_and_post (hs3_env.with_locals_clock callee _) (by omega) hp_cal ha_cal).1
    · rw [evaluateHOLFiniteState_call]
      rcases hargs : evalListHOLFinite s3 (h := fun a => Classical.propDecidable (s3.memaddrs a))
        [.var .local (ofString "v"), .var .local (ofString "d")] with _ | vals
      · simp
      · dsimp only
        rcases hl : lookupCodeHOLFinite s3.code.lookup (ofString "u256_to_digits") vals with _ | ⟨body, callee, rs⟩
        · simp
        · dsimp only
          split
          · simp
          · obtain ⟨v1, v2, hv1, hv2, rfl⟩ := evalList_two_eq hargs
            have hv1_eq : v1 = .val (.word (BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 560)) := by
              simpa [evalHOLExact, hv_s3] using hv1.symm
            have hv2_eq : v2 = .rStruct [.val (.word d0), .val (.word d1), .val (.word d2), .val (.word d3)] := by
              simpa [evalHOLExact, hd_s3] using hv2.symm
            subst hv1_eq hv2_eq
            have hl' := hl
            rw [hs3_env.code] at hl'
            obtain ⟨_, _, hinj_v, rfl, hp_cal, ha_cal, _, _⟩ := lookup_u256_to_digits_locals hl'
            simp only [List.cons.injEq] at hinj_v
            obtain ⟨rfl, rfl, _⟩ := hinj_v
            have hspec := u256_to_digits_wsSafe_and_post (s := callEntryStateHOLFinite s3 callee)
              (hs3_env.with_locals_clock callee (s3.clock - 1)) (by omega) hp_cal ha_cal
            dsimp only at hspec
            rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s3 callee) _ with ⟨rb, cpost⟩
            rw [hrun] at hspec
            cases rb with
            | none => simp
            | some r0 =>
              cases r0 with
              | returned rv =>
                dsimp only
                split
                · intro _
                  have heff_cp := ((ByteRegionEffect.refl s3 _).with_locals_clock callee (s3.clock - 1)).trans
                    (hspec.1.2 (Or.inl ⟨rv, rfl⟩))
                  exact ⟨(hs3_env.step heff_cp).with_locals_clock s3.locals cpost.clock,
                    rfl, hspec.2 rv cpost rfl hd_nz⟩
                · simp
              | exception _ _ | timeOut | error | «break» | «continue» | finalFfi _ => simp
  refine WsSafe.seq hcall_td.1 fun hn_td _ => ?_
  obtain ⟨hs4_env, hs4_loc, hpos_v⟩ := hcall_td.2 hn_td
  set s4 := (evaluateHOLFiniteState s3
    (.call (some (none, none)) (ofString "u256_to_digits")
      [.var .local (ofString "v"), .var .local (ofString "d")])).2
  have hv_s4 : s4.locals.lookup (ofString "v") =
      some (.val (.word (BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 560))) := by
    rw [hs4_loc]; exact hv_s3
  -- `decCall "n" .one "digits_len" [v, 8]` -> `1 ≤ n ≤ 8`
  refine WsSafe.decCall ?_ ?_
  · intro vals body callee rs _ hl _
    rw [hs4_env.code] at hl
    exact WsSafe.of_readOnly hs4_env.code (opRoCallees_good (ofString "digits_len") (by decide) vals body callee rs hl)
  intro vals_n body_n callee_n rs_n vn cpost_n hargs_n hl_n _ hrun_n heff_n _ _
  obtain ⟨vp_n, vn_arg, hvp_n, hvn_arg, rfl⟩ := evalList_two_eq hargs_n
  have hvp_n_eq : vp_n = .val (.word (BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 560)) := by
    simpa [evalHOLExact, hv_s4] using hvp_n.symm
  have hvn_arg_eq : vn_arg = .val (.word 8#64) := by
    simpa [evalHOLExact] using hvn_arg.symm
  subst hvp_n_eq hvn_arg_eq
  rw [hs4_env.code] at hl_n
  obtain ⟨_, _, hinj_n, rfl, hp_cal_n, hn_cal_n, _, _⟩ := lookup_digits_len_locals hl_n
  simp only [List.cons.injEq] at hinj_n
  obtain ⟨rfl, rfl, _⟩ := hinj_n
  have hdl_n := (digits_len_wsSafe_and_post (N := 8)
    (hs4_env.with_locals_clock callee_n _) hp_cal_n hn_cal_n (by decide)).2 vn cpost_n hrun_n
  obtain ⟨wn, rfl, hwn_le, hwn_pos_imp⟩ := hdl_n
  have hwn_ge : 1 ≤ wn.toNat := hwn_pos_imp (by
    obtain ⟨k, hk, wk, hwk, hmk⟩ := hpos_v
    exact ⟨k, by simpa using hk, wk, hwk, hmk⟩)
  set nv := wn.toNat
  have hwn_ofNat : wn = BitVec.ofNat 64 nv := by simp [nv]
  rw [hwn_ofNat]
  set s5 := setVarHOLFinite (ofString "n") (.val (.word (BitVec.ofNat 64 nv))) { cpost_n with locals := s4.locals }
  have hs5_env : WsEnv s0 s5 := (hs4_env.step heff_n).with_locals_clock _ _
  have hu_s5 : s5.locals.lookup (ofString "u") = some (.val (.word uw)) := by
    simp [s5, setVarHOLFinite, hs4_loc, s3, s2, s1, FUPDATE,
      show ofString "n" ≠ ofString "u" by decide,
      show ofString "v" ≠ ofString "u" by decide,
      show ofString "r" ≠ ofString "u" by decide,
      show ofString "q" ≠ ofString "u" by decide, hu]
  have hm_s5 : s5.locals.lookup (ofString "m") = some (.val (.word (BitVec.ofNat 64 mv))) := by
    simp [s5, setVarHOLFinite, hs4_loc, s3, s2, s1, FUPDATE,
      show ofString "n" ≠ ofString "m" by decide,
      show ofString "v" ≠ ofString "m" by decide,
      show ofString "r" ≠ ofString "m" by decide,
      show ofString "q" ≠ ofString "m" by decide, hm]
  -- `decCall "mm" .one "digits_len" [u, m]` -> `mm ≤ mv ≤ 16`
  refine WsSafe.decCall ?_ ?_
  · intro vals body callee rs _ hl _
    rw [hs5_env.code] at hl
    exact WsSafe.of_readOnly hs5_env.code (opRoCallees_good (ofString "digits_len") (by decide) vals body callee rs hl)
  intro vals_m body_m callee_m rs_m vmm cpost_m hargs_m hl_m _ hrun_m heff_m _ _
  obtain ⟨vp_m, vm_arg, hvp_m, hvm_arg, rfl⟩ := evalList_two_eq hargs_m
  have hvp_m_eq : vp_m = .val (.word uw) := by
    simpa [evalHOLExact, hu_s5] using hvp_m.symm
  have hvm_arg_eq : vm_arg = .val (.word (BitVec.ofNat 64 mv)) := by
    simpa [evalHOLExact, hm_s5] using hvm_arg.symm
  subst hvp_m_eq hvm_arg_eq
  rw [hs5_env.code] at hl_m
  obtain ⟨_, _, hinj_m, rfl, hp_cal_m, hn_cal_m, _, _⟩ := lookup_digits_len_locals hl_m
  simp only [List.cons.injEq] at hinj_m
  obtain ⟨rfl, rfl, _⟩ := hinj_m
  have hmv_toNat : (BitVec.ofNat 64 mv).toNat ≤ mv := by
    simp only [BitVec.toNat_ofNat]; omega
  obtain ⟨wmm, rfl, hwmm_le, _⟩ := (digits_len_wsSafe_and_post (N := mv)
    (hs5_env.with_locals_clock callee_m _) hp_cal_m hn_cal_m hmv_toNat).2 vmm cpost_m hrun_m
  set mmv := wmm.toNat
  have hwmm_ofNat : wmm = BitVec.ofNat 64 mmv := by simp [mmv]
  rw [hwmm_ofNat]
  set s6 := setVarHOLFinite (ofString "mm") (.val (.word (BitVec.ofNat 64 mmv))) { cpost_m with locals := s5.locals }
  have hs6_env : WsEnv s0 s6 := (hs5_env.step heff_m).with_locals_clock _ _
  refine WsSafe.dec fun vi hvi _ => ?_
  obtain ⟨rfl⟩ : vi = .val (.word 0#64) := by simpa [evalHOLExact] using hvi.symm
  set s7 := setVarHOLFinite (ofString "i") (.val (.word 0#64)) s6
  have hs7_env : WsEnv s0 s7 := hs6_env.with_locals_clock _ _
  have hq_s7 : s7.locals.lookup (ofString "q") =
      some (.val (.word (BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 216))) := by
    simp [s7, s6, s5, setVarHOLFinite, hs4_loc, s3, s2, s1, FUPDATE,
      show ofString "i" ≠ ofString "q" by decide,
      show ofString "mm" ≠ ofString "q" by decide,
      show ofString "n" ≠ ofString "q" by decide,
      show ofString "v" ≠ ofString "q" by decide,
      show ofString "r" ≠ ofString "q" by decide]
  have hi_s7 : s7.locals.lookup (ofString "i") = some (.val (.word 0#64)) := by
    simp [s7, setVarHOLFinite, FUPDATE]
  -- Loop: `while (i < 16) { store (q + i*8) 0; i := i + 1 }`
  have hw_q16 := WsSafe.while_up_store hs7_env
    (cnt := ofString "i") (base := ofString "q")
    (limExp := .const 16#64) (valExp := .const 0#64)
    (off := 216) (lim := 16) (idx0 := 0)
    (by decide)
    (fun _ _ => rfl)
    hq_s7 hi_s7 (by omega) (by omega) (fun k hk => by omega) rfl
  refine WsSafe.seq hw_q16.1 fun hn_q16 _ => ?_
  obtain ⟨hs8_env, ⟨iv8, _, hi_s8⟩, hother_s8⟩ := hw_q16.2 hn_q16
  set s8 := (evaluateHOLFiniteState s7 _).2
  have hmm_s8 : s8.locals.lookup (ofString "mm") = some (.val (.word (BitVec.ofNat 64 mmv))) := by
    rw [hother_s8 (ofString "mm") (by decide)]
    simp [s7, s6, setVarHOLFinite, FUPDATE, show ofString "i" ≠ ofString "mm" by decide]
  have hn_s8 : s8.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 nv))) := by
    rw [hother_s8 (ofString "n") (by decide)]
    simp [s7, s6, s5, setVarHOLFinite, FUPDATE,
      show ofString "i" ≠ ofString "n" by decide,
      show ofString "mm" ≠ ofString "n" by decide]
  -- `ite (mm < n) (call none "digits_to_u256" [u]) skip`
  refine WsSafe.seq ?_ ?_
  · refine WsSafe.ite (fun _ _ _ => ?_) (fun _ => WsSafe.skip _ _)
    exact WsSafe.of_readOnly hs8_env.code (by decide)
  intro hn_ite _
  -- When `.ite` finishes with `none`, the `mm < n` tail-call branch was NOT taken (since `.call none` never finishes with `none`), so `nv ≤ mmv` and state is `s8`!
  have hite_s8 : nv ≤ mmv ∧
      (evaluateHOLFiniteState s8
        (.ite (.cmp .lower (.var .local (ofString "mm")) (.var .local (ofString "n")))
          (.call none (ofString "digits_to_u256") [.var .local (ofString "u")])
          .skip)).2 = s8 := by
    by_cases hlt : mmv < nv
    · exfalso
      have hw1 : @evalHOLExact 64 F _ s8.toExact (fun a => Classical.propDecidable (s8.memaddrs a))
          (.cmp .lower (.var .local (ofString "mm")) (.var .local (ofString "n"))) =
          some (.val (.word 1#64)) := by
        simp only [evalHOLExact, hmm_s8, hn_s8, wordCmpHOL]
        have hcmp_t : (BitVec.ofNat 64 mmv < BitVec.ofNat 64 nv) := by
          rw [BitVec.lt_def]
          simp only [BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (show mmv < 2 ^ 64 by omega),
            Nat.mod_eq_of_lt (show nv < 2 ^ 64 by omega)]
          exact hlt
        simp [hcmp_t]
      rw [evaluateHOLFiniteState_ite, hw1] at hn_ite
      dsimp only at hn_ite
      rw [if_neg (by decide : (1#64 : BitVec 64) ≠ 0), evaluateHOLFiniteState_call] at hn_ite
      revert hn_ite
      rcases evalListHOLFinite s8 (h := fun a => Classical.propDecidable (s8.memaddrs a))
        [.var .local (ofString "u")] with _ | vals
      · simp
      · dsimp only
        rcases lookupCodeHOLFinite s8.code.lookup (ofString "digits_to_u256") vals with _ | ⟨b, cal, rs⟩
        · simp
        · dsimp only; split
          · simp
          · rcases evaluateHOLFiniteState (callEntryStateHOLFinite s8 cal) b with ⟨rb, cp⟩
            cases rb with
            | none => simp
            | some r0 =>
              cases r0 with
              | returned _ => dsimp only; split <;> simp
              | exception _ _ | timeOut | error | «break» | «continue» | finalFfi _ => simp
    · have hw0 : @evalHOLExact 64 F _ s8.toExact (fun a => Classical.propDecidable (s8.memaddrs a))
          (.cmp .lower (.var .local (ofString "mm")) (.var .local (ofString "n"))) =
          some (.val (.word 0#64)) := by
        simp only [evalHOLExact, hmm_s8, hn_s8, wordCmpHOL]
        have hcmp_f : ¬ (BitVec.ofNat 64 mmv < BitVec.ofNat 64 nv) := by
          rw [BitVec.lt_def]
          simp only [BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (show mmv < 2 ^ 64 by omega),
            Nat.mod_eq_of_lt (show nv < 2 ^ 64 by omega)]
          exact hlt
        simp [hcmp_f]
      rw [evaluateHOLFiniteState_ite, hw0]
      dsimp only
      simp only [ite_true, evaluateHOLFiniteState_skip]
      exact ⟨by omega, rfl⟩
  rw [hite_s8.2]
  refine WsSafe.seq_assign_word hs8_env ⟨_, hi_s8⟩
    (by simp [evalHOLExact] : @evalHOLExact 64 F _ s8.toExact (fun a => Classical.propDecidable (s8.memaddrs a)) (.const 0#64) = some (.val (.word 0#64)))
    fun hs9_env => ?_
  set s9 := setVarHOLFinite (ofString "i") (.val (.word 0#64)) s8
  have hr_s9 : s9.locals.lookup (ofString "r") =
      some (.val (.word (BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 352))) := by
    rw [show s9.locals.lookup (ofString "r") = s8.locals.lookup (ofString "r") by
      simp [s9, setVarHOLFinite, FUPDATE, show ofString "i" ≠ ofString "r" by decide]]
    rw [hother_s8 (ofString "r") (by decide)]
    simp [s7, s6, s5, setVarHOLFinite, hs4_loc, s3, s2, FUPDATE,
      show ofString "i" ≠ ofString "r" by decide,
      show ofString "mm" ≠ ofString "r" by decide,
      show ofString "n" ≠ ofString "r" by decide,
      show ofString "v" ≠ ofString "r" by decide]
  have hi_s9 : s9.locals.lookup (ofString "i") = some (.val (.word 0#64)) := by
    simp [s9, setVarHOLFinite, FUPDATE]
  -- Loop: `while (i < 8) { store (r + i*8) 0; i := i + 1 }`
  have hw_r8 := WsSafe.while_up_store hs9_env
    (cnt := ofString "i") (base := ofString "r")
    (limExp := .const 8#64) (valExp := .const 0#64)
    (off := 352) (lim := 8) (idx0 := 0)
    (by decide)
    (fun _ _ => rfl)
    hr_s9 hi_s9 (by omega) (by omega) (fun k hk => by omega) rfl
  refine WsSafe.seq hw_r8.1 fun hn_r8 _ => ?_
  obtain ⟨hs10_env, _, hother_s10⟩ := hw_r8.2 hn_r8
  set s10 := (evaluateHOLFiniteState s9 _).2
  have hkeep10 : ∀ x, x ≠ ofString "i" → s10.locals.lookup x = s7.locals.lookup x := by
    intro x hxi
    rw [hother_s10 x hxi]
    rw [show s9.locals.lookup x = s8.locals.lookup x by
      simp [s9, setVarHOLFinite, FUPDATE, Ne.symm hxi]]
    exact hother_s8 x hxi
  have hq_s10 : s10.locals.lookup (ofString "q") =
      some (.val (.word (BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 216))) := by
    rw [hkeep10 (ofString "q") (by decide)]; exact hq_s7
  have hr_s10 : s10.locals.lookup (ofString "r") =
      some (.val (.word (BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 352))) := by
    rw [hother_s10 (ofString "r") (by decide)]; exact hr_s9
  have hu_s10 : s10.locals.lookup (ofString "u") = some (.val (.word uw)) := by
    rw [hkeep10 (ofString "u") (by decide)]
    simp [s7, s6, setVarHOLFinite, FUPDATE,
      show ofString "i" ≠ ofString "u" by decide,
      show ofString "mm" ≠ ofString "u" by decide, hu_s5]
  have hmm_s10 : s10.locals.lookup (ofString "mm") = some (.val (.word (BitVec.ofNat 64 mmv))) := by
    rw [hother_s10 (ofString "mm") (by decide)]
    rw [show s9.locals.lookup (ofString "mm") = s8.locals.lookup (ofString "mm") by
      simp [s9, setVarHOLFinite, FUPDATE, show ofString "i" ≠ ofString "mm" by decide]]
    exact hmm_s8
  have hv_s10 : s10.locals.lookup (ofString "v") =
      some (.val (.word (BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 560))) := by
    rw [hkeep10 (ofString "v") (by decide)]
    simp [s7, s6, s5, setVarHOLFinite, FUPDATE,
      show ofString "i" ≠ ofString "v" by decide,
      show ofString "mm" ≠ ofString "v" by decide,
      show ofString "n" ≠ ofString "v" by decide, hv_s4]
  have hn_s10 : s10.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 nv))) := by
    rw [hother_s10 (ofString "n") (by decide)]
    rw [show s9.locals.lookup (ofString "n") = s8.locals.lookup (ofString "n") by
      simp [s9, setVarHOLFinite, FUPDATE, show ofString "i" ≠ ofString "n" by decide]]
    exact hn_s8
  -- Call `divmnu(q, r, u, mm, v, n)` then tail-call `digits_to_u256(r)`
  refine WsSafe.seq (WsSafe.call_void ?_) ?_
  · intro vals body callee rs hargs hl _
    obtain ⟨vq, vr, vu, vmm_a, vv_a, vn_a, hvq_a, hvr_a, hvu_a, hvmm_a, hvv_a, hvn_a, rfl⟩ :=
      evalList_six_eq hargs
    have hvq_eq : vq = .val (.word (BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 216)) := by
      simpa [evalHOLExact, hq_s10] using hvq_a.symm
    have hvr_eq : vr = .val (.word (BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 352)) := by
      simpa [evalHOLExact, hr_s10] using hvr_a.symm
    have hvu_eq : vu = .val (.word uw) := by
      simpa [evalHOLExact, hu_s10] using hvu_a.symm
    have hvmm_eq : vmm_a = .val (.word (BitVec.ofNat 64 mmv)) := by
      simpa [evalHOLExact, hmm_s10] using hvmm_a.symm
    have hvv_eq : vv_a = .val (.word (BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 560)) := by
      simpa [evalHOLExact, hv_s10] using hvv_a.symm
    have hvn_eq : vn_a = .val (.word (BitVec.ofNat 64 nv)) := by
      simpa [evalHOLExact, hn_s10] using hvn_a.symm
    subst hvq_eq hvr_eq hvu_eq hvmm_eq hvv_eq hvn_eq
    rw [hs10_env.code] at hl
    obtain ⟨_, _, _, _, _, _, hinj6, rfl, hq_c, hr_c, hu_c, hm_c, hv_c, hn_c, _, _⟩ :=
      lookup_divmnu_locals hl
    simp only [List.cons.injEq] at hinj6
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, _⟩ := hinj6
    exact divmnu_wsSafe (hs10_env.with_locals_clock callee _) (by omega) (by omega)
      hq_c hr_c hu_c hm_c hv_c hn_c hwn_ge hwn_le (by omega) hite_s8.1
  · intro _ heff_div
    exact WsSafe.of_readOnly (hs10_env.step heff_div).code (by decide)

private theorem call_void_u256_to_digits_wsSafe {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    (he : WsEnv s0 s) {pExp aExp : ExpHOL 64} {off : Nat}
    (hoff : off + 64 ≤ 640)
    (hp : ∀ vp, @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) pExp = some vp →
      vp = .val (.word (BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 off))) :
    WsSafe s (untypedGlobalBufIvls s0)
      (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "u256_to_digits") [pExp, aExp])) ∧
    ((evaluateHOLFiniteState s (.call (some (none, none)) (ofString "u256_to_digits") [pExp, aExp])).1 = none →
      (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "u256_to_digits") [pExp, aExp])).2.locals = s.locals) := by
  refine ⟨WsSafe.call_void ?_, ?_⟩
  · intro vals body callee rs hargs hl _
    obtain ⟨v1, v2, hv1, _, rfl⟩ := evalList_two_eq hargs
    have hv1_eq := hp v1 hv1; subst hv1_eq
    rw [he.code] at hl
    obtain ⟨_, _, hinj_v, rfl, hp_cal, ha_cal, _, hsh_a⟩ := lookup_u256_to_digits_locals hl
    simp only [List.cons.injEq] at hinj_v
    obtain ⟨rfl, rfl, _⟩ := hinj_v
    obtain ⟨a0, a1, a2, a3, rfl⟩ := eval_comb4_of_shape (Or.inr hsh_a)
    exact (u256_to_digits_wsSafe_and_post (he.with_locals_clock callee _) hoff hp_cal ha_cal).1
  · rw [evaluateHOLFiniteState_call]
    rcases evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [pExp, aExp] with _ | vals
    · simp
    · dsimp only
      rcases lookupCodeHOLFinite s.code.lookup (ofString "u256_to_digits") vals with _ | ⟨body, callee, rs⟩
      · simp
      · dsimp only; split
        · simp
        · rcases evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨rb, cpost⟩
          cases rb with
          | none => simp
          | some r0 =>
            cases r0 with
            | returned _ => dsimp only; split <;> simp
            | exception _ _ | timeOut | error | «break» | «continue» | finalFfi _ => simp

private theorem call_tail_digits_divmod_wsSafe {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    (he : WsEnv s0 s) {uExp dExp : ExpHOL 64} {mv : Nat} {d0 d1 d2 d3 : BitVec 64}
    (hm_le : mv ≤ 16)
    (hd : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dExp =
      some (.rStruct [.val (.word d0), .val (.word d1), .val (.word d2), .val (.word d3)]))
    (hd_nz : (d0 ||| d1 ||| d2 ||| d3) ≠ 0) :
    WsSafe s (untypedGlobalBufIvls s0)
      (evaluateHOLFiniteState s
        (.call none (ofString "digits_divmod") [uExp, .const (BitVec.ofNat 64 mv), dExp])) := by
  refine WsSafe.call_tail ?_
  intro vals body callee rs hargs hl _
  obtain ⟨v1, v2, v3, _, hv2, hv3, rfl⟩ := evalList_three_eq hargs
  have hv2_eq : v2 = .val (.word (BitVec.ofNat 64 mv)) := by simpa [evalHOLExact] using hv2.symm
  have hv3_eq : v3 = .rStruct [.val (.word d0), .val (.word d1), .val (.word d2), .val (.word d3)] := by
    rw [hd] at hv3; exact Option.some.inj hv3.symm
  subst hv2_eq hv3_eq
  rw [he.code] at hl
  obtain ⟨_, _, _, hinj3, rfl, hu_c, hm_c, hd_c, hsh_u, _, _⟩ := lookup_digits_divmod_locals hl
  simp only [List.cons.injEq] at hinj3
  obtain ⟨rfl, rfl, rfl, _⟩ := hinj3
  obtain ⟨uw, rfl⟩ := eval_word_of_shape_one (Or.inr hsh_u)
  exact digits_divmod_wsSafe (he.with_locals_clock callee _) hu_c hm_c hd_c hm_le hd_nz

private theorem ite_return_skip_none {F : Type} {s : PanSemStateFiniteExact 64 F}
    {cond retExp : ExpHOL 64}
    (hn : (evaluateHOLFiniteState s (.ite cond (.return retExp) .skip)).1 = none) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) cond =
      some (.val (.word 0#64)) ∧
    (evaluateHOLFiniteState s (.ite cond (.return retExp) .skip)).2 = s := by
  rw [evaluateHOLFiniteState_ite] at hn ⊢
  rcases hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) cond with _ | v
  · simp [hcond] at hn
  · cases v with
    | val hl =>
      cases hl with
      | word w =>
        simp only [hcond] at hn ⊢
        by_cases hw0 : w = 0
        · subst hw0
          exact ⟨rfl, by simp [evaluateHOLFiniteState_skip]⟩
        · simp only [hw0, ↓reduceIte, Bool.false_eq_true, evaluateHOLFiniteState_return] at hn
          exfalso; revert hn
          split; · simp
          split <;> simp
    | rStruct _ => simp [hcond] at hn
    | nStruct _ _ => simp [hcond] at hn

private theorem ite_tail_skip_none {F : Type} {s : PanSemStateFiniteExact 64 F}
    {cond : ExpHOL 64} {fname : MlS} {args : List (ExpHOL 64)}
    (hn : (evaluateHOLFiniteState s (.ite cond (.call none fname args) .skip)).1 = none) :
    (evaluateHOLFiniteState s (.ite cond (.call none fname args) .skip)).2 = s := by
  rw [evaluateHOLFiniteState_ite] at hn ⊢
  rcases hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) cond with _ | v
  · simp [hcond] at hn
  · cases v with
    | val hl =>
      cases hl with
      | word w =>
        simp only [hcond] at hn ⊢
        by_cases hw0 : w = 0
        · subst hw0
          simp [evaluateHOLFiniteState_skip]
        · simp only [hw0, ↓reduceIte, Bool.false_eq_true, evaluateHOLFiniteState_call] at hn
          exfalso; revert hn
          rcases evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vals
          · simp
          · dsimp only
            rcases lookupCodeHOLFinite s.code.lookup fname vals with _ | ⟨b, cal, rs⟩
            · simp
            · dsimp only; split
              · simp
              · rcases evaluateHOLFiniteState (callEntryStateHOLFinite s cal) b with ⟨rb, cp⟩
                cases rb with
                | none => simp
                | some r0 =>
                  cases r0 with
                  | returned _ => dsimp only; split <;> simp
                  | exception _ _ | timeOut | error | «break» | «continue» | finalFfi _ => simp
    | rStruct _ => simp [hcond] at hn
    | nStruct _ _ => simp [hcond] at hn

private theorem lookup_two_comb4_locals {fname : MlS} {body0 : ProgHOL 64} {retSh : ShapeHOL}
    (hlk : originalRuntimeCode.lookup fname =
      some ([(ofString "a", .comb [.one, .one, .one, .one]),
             (ofString "b", .comb [.one, .one, .one, .one])], body0, retSh))
    {vals : List (ValueHOL 64)} {body : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {rs : ShapeHOL}
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup fname vals = some (body, callee, rs)) :
    body = body0 ∧
    (∃ a0 a1 a2 a3, callee.lookup (ofString "a") =
      some (.rStruct [.val (.word a0), .val (.word a1), .val (.word a2), .val (.word a3)])) ∧
    (∃ b0 b1 b2 b3, callee.lookup (ofString "b") =
      some (.rStruct [.val (.word b0), .val (.word b1), .val (.word b2), .val (.word b3)])) := by
  have hraw := lookupCodeHOLFinite_eq_some _ _ _ _ _ _ hl
  simp only [lookupCodeHOLExact, hlk, List.length] at hraw
  rcases vals with _ | ⟨va, _ | ⟨vb, _ | _⟩⟩
  · simp at hraw
  · simp at hraw
  · simp only [List.length, ↓reduceIte, List.zip, List.zipWith, List.all,
      List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hraw
    split at hraw
    · rename_i hshapes
      have hinj := Option.some.inj hraw
      have hb : body = body0 := (Prod.mk.inj hinj).1.symm
      have hfn : callee.lookup = _ := (Prod.mk.inj (Prod.mk.inj hinj).2).1.symm
      obtain ⟨a0, a1, a2, a3, rfl⟩ := eval_comb4_of_shape (Or.inl hshapes.2.2.1)
      obtain ⟨b0, b1, b2, b3, rfl⟩ := eval_comb4_of_shape (Or.inl hshapes.2.2.2)
      refine ⟨hb, ⟨a0, a1, a2, a3, ?_⟩, ⟨b0, b1, b2, b3, ?_⟩⟩
      · simpa [FUPDATE_LIST, FUPDATE, show ofString "a" ≠ ofString "b" by decide] using congrFun hfn (ofString "a")
      · simpa [FUPDATE_LIST, FUPDATE] using congrFun hfn (ofString "b")
    · simp at hraw
  · simp [List.length] at hraw

private theorem lookup_three_comb4_locals {fname : MlS} {body0 : ProgHOL 64} {retSh : ShapeHOL}
    (hlk : originalRuntimeCode.lookup fname =
      some ([(ofString "a", .comb [.one, .one, .one, .one]),
             (ofString "b", .comb [.one, .one, .one, .one]),
             (ofString "m", .comb [.one, .one, .one, .one])], body0, retSh))
    {vals : List (ValueHOL 64)} {body : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {rs : ShapeHOL}
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup fname vals = some (body, callee, rs)) :
    body = body0 ∧
    (∃ m0 m1 m2 m3, callee.lookup (ofString "m") =
      some (.rStruct [.val (.word m0), .val (.word m1), .val (.word m2), .val (.word m3)])) := by
  have hraw := lookupCodeHOLFinite_eq_some _ _ _ _ _ _ hl
  simp only [lookupCodeHOLExact, hlk, List.length] at hraw
  rcases vals with _ | ⟨va, _ | ⟨vb, _ | ⟨vm, _ | _⟩⟩⟩
  · simp at hraw
  · simp at hraw
  · simp at hraw
  · simp only [List.length, ↓reduceIte, List.zip, List.zipWith, List.all,
      List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hraw
    split at hraw
    · rename_i hshapes
      have hinj := Option.some.inj hraw
      have hb : body = body0 := (Prod.mk.inj hinj).1.symm
      have hfn : callee.lookup = _ := (Prod.mk.inj (Prod.mk.inj hinj).2).1.symm
      obtain ⟨m0, m1, m2, m3, rfl⟩ := eval_comb4_of_shape (Or.inl hshapes.2.2.2.2)
      refine ⟨hb, ⟨m0, m1, m2, m3, ?_⟩⟩
      simpa [FUPDATE_LIST, FUPDATE] using congrFun hfn (ofString "m")
    · simp at hraw
  · simp [List.length] at hraw

theorem u256_divmod_wsSafe {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    (he : WsEnv s0 s) {b0 b1 b2 b3 : BitVec 64}
    (hb : s.locals.lookup (ofString "b") =
      some (.rStruct [.val (.word b0), .val (.word b1), .val (.word b2), .val (.word b3)])) :
    WsSafe s (untypedGlobalBufIvls s0)
      (evaluateHOLFiniteState s
        (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
          (extractFn Guest.Software.guestFn_u256_divmod).body)) := by
  dsimp only [extractFn, Guest.Software.guestFn_u256_divmod,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural,
    Option.map, List.map]
  -- 1. `if ((b0 | b1 | b2 | b3) == 0) return 0`
  refine WsSafe.seq (WsSafe.ite (fun _ _ _ => WsSafe.return_exp _ _ _) (fun _ => WsSafe.skip _ _)) ?_
  intro hn_b0 _
  obtain ⟨hcmp_b0, hs_b0⟩ := ite_return_skip_none hn_b0
  have hb_nz : (b0 ||| b1 ||| b2 ||| b3) ≠ 0 := eval_or4_ne_zero hb hcmp_b0
  rw [hs_b0]
  -- 2. `decCall "lt" .one "u256_lt" [a, b]`
  refine WsSafe.decCall_ro he (by decide) fun vlt cpost_lt hs1_env _ _ => ?_
  set s1 := setVarHOLFinite (ofString "lt") vlt { cpost_lt with locals := s.locals }
  -- 3. `if (lt == 1) return (0, a)`
  refine WsSafe.seq (WsSafe.ite (fun _ _ _ => WsSafe.return_exp _ _ _) (fun _ => WsSafe.skip _ _)) ?_
  intro hn_lt _
  rw [(ite_return_skip_none hn_lt).2]
  -- 4. `if (high limbs == 0) { decCall qr udivmod ... return ... } else skip`
  refine WsSafe.seq (WsSafe.of_readOnly hs1_env.code (by decide)) ?_
  intro hn_fast _
  have hs_fast := by
    let p_fast : ProgHOL 64 :=
      .ite (.cmp .equal (.op .or [.rfield 1 (.var .local (ofString "a")),
                                  .rfield 2 (.var .local (ofString "a")),
                                  .rfield 3 (.var .local (ofString "a")),
                                  .rfield 1 (.var .local (ofString "b")),
                                  .rfield 2 (.var .local (ofString "b")),
                                  .rfield 3 (.var .local (ofString "b"))]) (.const 0#64))
        (.decCall (ofString "qr") (.comb [.one, .one]) (ofString "udivmod")
          [.rfield 0 (.var .local (ofString "a")), .rfield 0 (.var .local (ofString "b"))]
          (.return (.rstruct [.rfield 0 (.var .local (ofString "qr")), .const 0#64, .const 0#64, .const 0#64,
                              .rfield 1 (.var .local (ofString "qr")), .const 0#64, .const 0#64, .const 0#64])))
        .skip
    show (evaluateHOLFiniteState s1 p_fast).2 = s1
    change (evaluateHOLFiniteState s1 p_fast).1 = none at hn_fast
    dsimp only [p_fast] at hn_fast ⊢
    rw [evaluateHOLFiniteState_ite] at hn_fast ⊢
    rcases hcond : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
      (.cmp .equal (.op .or [.rfield 1 (.var .local (ofString "a")),
                             .rfield 2 (.var .local (ofString "a")),
                             .rfield 3 (.var .local (ofString "a")),
                             .rfield 1 (.var .local (ofString "b")),
                             .rfield 2 (.var .local (ofString "b")),
                             .rfield 3 (.var .local (ofString "b"))]) (.const 0#64)) with _ | v
    · simp [hcond] at hn_fast
    · cases v with
      | val hl =>
        cases hl with
        | word w =>
          simp only [hcond] at hn_fast ⊢
          by_cases hw0 : w = 0
          · subst hw0; simp [evaluateHOLFiniteState_skip]
          · simp only [hw0, ↓reduceIte, Bool.false_eq_true, evaluateHOLFiniteState_decCall_fixClockRewrite] at hn_fast
            exfalso; revert hn_fast
            rcases evalListHOLFinite s1 (h := fun a => Classical.propDecidable (s1.memaddrs a)) _ with _ | vals
            · simp
            · dsimp only
              rcases lookupCodeHOLFinite s1.code.lookup (ofString "udivmod") vals with _ | ⟨bd, cal, rs⟩
              · simp
              · dsimp only; split
                · simp
                · rcases evaluateHOLFiniteState (callEntryStateHOLFinite s1 cal) bd with ⟨rb, cp⟩
                  cases rb with
                  | none => simp
                  | some r0 =>
                    cases r0 with
                    | returned rv =>
                      dsimp only; split
                      · rw [evaluateHOLFiniteState_return]
                        split; · simp
                        split <;> simp
                      · simp
                    | exception _ _ | timeOut | error | «break» | «continue» | finalFfi _ => simp
      | rStruct _ => simp [hcond] at hn_fast
      | nStruct _ _ => simp [hcond] at hn_fast
  rw [hs_fast]
  -- 5. `dec "u" (u256_ws + 424)`
  refine WsSafe.dec fun vu hvu _ => ?_
  rw [eval_u256_ws_plus hs1_env hvu]
  set s2 := setVarHOLFinite (ofString "u")
    (.val (.word (BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 424))) s1
  have hs2_env : WsEnv s0 s2 := hs1_env.with_locals_clock _ _
  have hu_s2 : s2.locals.lookup (ofString "u") =
      some (.val (.word (BitVec.ofNat 64 (globN s0 "u256_ws") + BitVec.ofNat 64 424))) := by
    simp [s2, setVarHOLFinite, FUPDATE]
  have hb_s2 : s2.locals.lookup (ofString "b") =
      some (.rStruct [.val (.word b0), .val (.word b1), .val (.word b2), .val (.word b3)]) := by
    simp [s2, s1, setVarHOLFinite, FUPDATE,
      show ofString "u" ≠ ofString "b" by decide,
      show ofString "lt" ≠ ofString "b" by decide, hb]
  -- 6. `call (some (none, none)) "u256_to_digits" [u, a]`
  have htd := call_void_u256_to_digits_wsSafe hs2_env
    (pExp := .var .local (ofString "u")) (aExp := .var .local (ofString "a")) (off := 424)
    (by omega) (fun vp hvp => by simpa [evalHOLExact, hu_s2] using hvp.symm)
  refine WsSafe.seq htd.1 fun hn_td heff_td => ?_
  set s3 := (evaluateHOLFiniteState s2 _).2
  have hs3_env : WsEnv s0 s3 := hs2_env.step heff_td
  have hs3_loc : s3.locals = s2.locals := htd.2 hn_td
  have hb_s3 : s3.locals.lookup (ofString "b") =
      some (.rStruct [.val (.word b0), .val (.word b1), .val (.word b2), .val (.word b3)]) := by
    rw [hs3_loc]; exact hb_s2
  -- 7. `decCall "r" .comb4 "digits_divmod" [u, 8, b]`
  refine WsSafe.decCall ?_ ?_
  · intro vals body callee rs hargs hl _
    obtain ⟨v1, v2, v3, _, hv2, hv3, rfl⟩ := evalList_three_eq hargs
    have hv2_eq : v2 = .val (.word 8#64) := by simpa [evalHOLExact] using hv2.symm
    have hv3_eq : v3 = .rStruct [.val (.word b0), .val (.word b1), .val (.word b2), .val (.word b3)] := by
      simpa [evalHOLExact, hb_s3] using hv3.symm
    subst hv2_eq hv3_eq
    rw [hs3_env.code] at hl
    obtain ⟨_, _, _, hinj3, rfl, hu_c, hm_c, hd_c, hsh_u, _, _⟩ := lookup_digits_divmod_locals hl
    simp only [List.cons.injEq] at hinj3
    obtain ⟨rfl, rfl, rfl, _⟩ := hinj3
    obtain ⟨uw, rfl⟩ := eval_word_of_shape_one (Or.inr hsh_u)
    exact digits_divmod_wsSafe (hs3_env.with_locals_clock callee _) hu_c hm_c hd_c (by omega) hb_nz
  · intro _ _ _ _ vr cpost_r _ _ _ _ heff_r _ _
    set s4 := setVarHOLFinite (ofString "r") vr { cpost_r with locals := s3.locals }
    have hs4_env : WsEnv s0 s4 := ⟨(hs3_env.step heff_r).code, (hs3_env.step heff_r).memaddrs,
      (hs3_env.step heff_r).globals, hs3_env.ws_bnd⟩
    exact WsSafe.of_readOnly hs4_env.code (by decide)

theorem eps_of_wsSafe (idx : Nat) (hidx : idx < Guest.Software.guestAst.length)
    (d : Decl (BitVec 64)) (hd : Guest.Software.guestAst[idx] = .function (extractFn d))
    (hbody : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      WsEnv s s →
      (∃ values, lookupCodeHOLFinite originalRuntimeCode.lookup
        (ofString (extractFn d).name) values =
          some (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural (extractFn d).body,
                s.locals,
                InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural (extractFn d).returnShape)) →
      WsSafe s (untypedGlobalBufIvls s)
        (evaluateHOLFiniteState s
          (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural (extractFn d).body))) :
    EvmPreservingSpec (fun _ => True) (fun _ _ _ => True)
      (ofString (extractFn d).name) := by
  refine ⟨_, _, _, lookup_of_guestAst_getElem idx hidx (extractFn d) hd, ?_⟩
  intro F s hcode hInv _ hlk _
  have hsafe := hbody s (WsEnv.of_evmInv hcode hInv) hlk
  have hres (hr : Resumes (evaluateHOLFiniteState s
      (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural (extractFn d).body)).1) :
      let post := (evaluateHOLFiniteState s
        (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural (extractFn d).body)).2
      EvmInv post ∧ evmChain post = evmChain s ∧ evmR post ≤ evmR s := by
    have heff := hsafe.2 hr
    obtain ⟨hInv_p, _, hch, hR⟩ := evmStepR_of_untypedGlobalBufs hInv heff
    exact ⟨hInv_p, hch, le_of_eq hR⟩
  refine ⟨fun v hv => ?_, fun ⟨v, hv⟩ => hres (Or.inr ⟨_, v, hv, by decide⟩)⟩
  obtain ⟨h1, h2, h3⟩ := hres (Or.inl ⟨v, hv⟩)
  exact ⟨h1, h2, h3, trivial⟩

private theorem call_u256_divmod_wsSafe {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    (he : WsEnv s0 s) {vals : List (ValueHOL 64)} {body : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {rs : ShapeHOL}
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "u256_divmod") vals = some (body, callee, rs)) :
    WsSafe (callEntryStateHOLFinite s callee) (untypedGlobalBufIvls s0)
      (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body) := by
  rw [he.code] at hl
  obtain ⟨rfl, _, ⟨b0, b1, b2, b3, hb_c⟩⟩ := lookup_two_comb4_locals lookup_u256_divmod hl
  exact u256_divmod_wsSafe (he.with_locals_clock callee _) hb_c

theorem eps_u256_div : EvmPreservingSpec (fun _ => True) (fun _ _ _ => True) (ofString "u256_div") := by
  refine eps_of_wsSafe 70 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_div rfl ?_
  intro F s he _
  dsimp only [extractFn, Guest.Software.guestFn_u256_div,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural,
    Option.map, List.map]
  refine WsSafe.decCall ?_ ?_
  · intro vals body callee rs _ hl _
    exact call_u256_divmod_wsSafe he hl
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _
    exact WsSafe.return_exp _ _ _

theorem eps_u256_mod : EvmPreservingSpec (fun _ => True) (fun _ _ _ => True) (ofString "u256_mod") := by
  refine eps_of_wsSafe 71 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_mod rfl ?_
  intro F s he _
  dsimp only [extractFn, Guest.Software.guestFn_u256_mod,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural,
    Option.map, List.map]
  refine WsSafe.decCall ?_ ?_
  · intro vals body callee rs _ hl _
    exact call_u256_divmod_wsSafe he hl
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _
    exact WsSafe.return_exp _ _ _

private theorem lookup_u256_div :
    originalRuntimeCode.lookup (ofString "u256_div") =
      some ([(ofString "a", .comb [.one, .one, .one, .one]), (ofString "b", .comb [.one, .one, .one, .one])],
            InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
              (extractFn Guest.Software.guestFn_u256_div).body,
            .comb [.one, .one, .one, .one]) :=
  lookup_of_guestAst_getElem 70 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_u256_div) rfl

private theorem lookup_u256_mod :
    originalRuntimeCode.lookup (ofString "u256_mod") =
      some ([(ofString "a", .comb [.one, .one, .one, .one]), (ofString "b", .comb [.one, .one, .one, .one])],
            InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
              (extractFn Guest.Software.guestFn_u256_mod).body,
            .comb [.one, .one, .one, .one]) :=
  lookup_of_guestAst_getElem 71 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_u256_mod) rfl

private theorem call_u256_div_wsSafe {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    (he : WsEnv s0 s) {vals : List (ValueHOL 64)} {body : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {rs : ShapeHOL}
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "u256_div") vals = some (body, callee, rs)) :
    WsSafe (callEntryStateHOLFinite s callee) (untypedGlobalBufIvls s0)
      (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body) := by
  rw [he.code] at hl
  obtain ⟨rfl, _, _⟩ := lookup_two_comb4_locals lookup_u256_div hl
  dsimp only [extractFn, Guest.Software.guestFn_u256_div,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map]
  refine WsSafe.decCall ?_ ?_
  · intro vals' body' callee' rs' _ hl' _
    exact call_u256_divmod_wsSafe (he.with_locals_clock callee _) hl'
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _
    exact WsSafe.return_exp _ _ _

private theorem call_u256_mod_wsSafe {F : Type} {s0 s : PanSemStateFiniteExact 64 F}
    (he : WsEnv s0 s) {vals : List (ValueHOL 64)} {body : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {rs : ShapeHOL}
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "u256_mod") vals = some (body, callee, rs)) :
    WsSafe (callEntryStateHOLFinite s callee) (untypedGlobalBufIvls s0)
      (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body) := by
  rw [he.code] at hl
  obtain ⟨rfl, _, _⟩ := lookup_two_comb4_locals lookup_u256_mod hl
  dsimp only [extractFn, Guest.Software.guestFn_u256_mod,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map]
  refine WsSafe.decCall ?_ ?_
  · intro vals' body' callee' rs' _ hl' _
    exact call_u256_divmod_wsSafe (he.with_locals_clock callee _) hl'
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _
    exact WsSafe.return_exp _ _ _

theorem eps_u256_sdiv : EvmPreservingSpec (fun _ => True) (fun _ _ _ => True) (ofString "u256_sdiv") := by
  refine eps_of_wsSafe 73 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_sdiv rfl ?_
  intro F s he _
  dsimp only [extractFn, Guest.Software.guestFn_u256_sdiv,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural,
    Option.map, List.map]
  refine WsSafe.seq (WsSafe.ite (fun _ _ _ => WsSafe.return_exp _ _ _) (fun _ => WsSafe.skip _ _)) ?_
  intro _ heff0
  have he1 := he.step heff0
  refine WsSafe.decCall_ro he1 (by decide) fun _ _ he2 _ _ => ?_
  refine WsSafe.decCall_ro he2 (by decide) fun _ _ he3 _ _ => ?_
  refine WsSafe.decCall ?_ ?_
  · intro vals body callee rs _ hl _
    exact call_u256_div_wsSafe he3 hl
  · intro _ _ _ _ vq cpost _ _ _ _ heff_q _ _
    exact WsSafe.of_readOnly (he3.step heff_q).code (by decide)

theorem eps_u256_smod : EvmPreservingSpec (fun _ => True) (fun _ _ _ => True) (ofString "u256_smod") := by
  refine eps_of_wsSafe 74 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_smod rfl ?_
  intro F s he _
  dsimp only [extractFn, Guest.Software.guestFn_u256_smod,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural,
    Option.map, List.map]
  refine WsSafe.seq (WsSafe.ite (fun _ _ _ => WsSafe.return_exp _ _ _) (fun _ => WsSafe.skip _ _)) ?_
  intro _ heff0
  have he1 := he.step heff0
  refine WsSafe.decCall_ro he1 (by decide) fun _ _ he2 _ _ => ?_
  refine WsSafe.decCall_ro he2 (by decide) fun _ _ he3 _ _ => ?_
  refine WsSafe.decCall ?_ ?_
  · intro vals body callee rs _ hl _
    exact call_u256_mod_wsSafe he3 hl
  · intro _ _ _ _ vr cpost _ _ _ _ heff_r _ _
    exact WsSafe.of_readOnly (he3.step heff_r).code (by decide)

private theorem lookup_u256_addmod :
    originalRuntimeCode.lookup (ofString "u256_addmod") =
      some ([(ofString "a", .comb [.one, .one, .one, .one]),
             (ofString "b", .comb [.one, .one, .one, .one]),
             (ofString "m", .comb [.one, .one, .one, .one])],
            InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
              (extractFn Guest.Software.guestFn_u256_addmod).body,
            .comb [.one, .one, .one, .one]) :=
  lookup_of_guestAst_getElem 75 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_u256_addmod) rfl

private theorem lookup_u256_mulmod :
    originalRuntimeCode.lookup (ofString "u256_mulmod") =
      some ([(ofString "a", .comb [.one, .one, .one, .one]),
             (ofString "b", .comb [.one, .one, .one, .one]),
             (ofString "m", .comb [.one, .one, .one, .one])],
            InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
              (extractFn Guest.Software.guestFn_u256_mulmod).body,
            .comb [.one, .one, .one, .one]) :=
  lookup_of_guestAst_getElem 76 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_u256_mulmod) rfl

theorem eps_u256_addmod : EvmPreservingSpec (fun _ => True) (fun _ _ _ => True) (ofString "u256_addmod") := by
  refine eps_of_wsSafe 75 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_addmod rfl ?_
  intro F s he ⟨vals0, hlk0⟩
  obtain ⟨_, m0, m1, m2, m3, hm⟩ := lookup_three_comb4_locals lookup_u256_addmod hlk0
  dsimp only [extractFn, Guest.Software.guestFn_u256_addmod,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural,
    Option.map, List.map]
  -- 1. `if ((m0 | m1 | m2 | m3) == 0) return 0`
  refine WsSafe.seq (WsSafe.ite (fun _ _ _ => WsSafe.return_exp _ _ _) (fun _ => WsSafe.skip _ _)) ?_
  intro hn_m0 _
  obtain ⟨hcmp_m0, hs_m0⟩ := ite_return_skip_none hn_m0
  have hm_nz : (m0 ||| m1 ||| m2 ||| m3) ≠ 0 := eval_or4_ne_zero hm hcmp_m0
  rw [hs_m0]
  -- 2. `decCall "s" .comb5 "u256_add_carry" [a, b]`
  refine WsSafe.decCall_ro he (by decide) fun vs cpost_s hs1_env _ _ => ?_
  set s1 := setVarHOLFinite (ofString "s") vs { cpost_s with locals := s.locals }
  -- 3. `dec "sum" .comb4 ...`
  refine WsSafe.dec fun vsum _ _ => ?_
  set s2 := setVarHOLFinite (ofString "sum") vsum s1
  have hs2_env : WsEnv s s2 := hs1_env.with_locals_clock _ _
  -- 4. `if (s.4 == 0) (call none "u256_mod" [sum, m]) else skip`
  refine WsSafe.seq
    (WsSafe.ite
      (fun _ _ _ => WsSafe.call_tail fun _ _ _ _ _ hl _ => call_u256_mod_wsSafe hs2_env hl)
      (fun _ => WsSafe.skip _ _)) ?_
  intro hn_ite _
  rw [ite_tail_skip_none hn_ite]
  -- 5. `dec "u" (u256_ws + 424)`
  refine WsSafe.dec fun vu hvu _ => ?_
  rw [eval_u256_ws_plus hs2_env hvu]
  set s3 := setVarHOLFinite (ofString "u")
    (.val (.word (BitVec.ofNat 64 (globN s "u256_ws") + BitVec.ofNat 64 424))) s2
  have hs3_env : WsEnv s s3 := hs2_env.with_locals_clock _ _
  have hu_s3 : s3.locals.lookup (ofString "u") =
      some (.val (.word (BitVec.ofNat 64 (globN s "u256_ws") + BitVec.ofNat 64 424))) := by
    simp [s3, setVarHOLFinite, FUPDATE]
  have hm_s3 : s3.locals.lookup (ofString "m") =
      some (.rStruct [.val (.word m0), .val (.word m1), .val (.word m2), .val (.word m3)]) := by
    simp [s3, s2, s1, setVarHOLFinite, FUPDATE,
      show ofString "u" ≠ ofString "m" by decide,
      show ofString "sum" ≠ ofString "m" by decide,
      show ofString "s" ≠ ofString "m" by decide, hm]
  -- 6. `u256_to_digits(u, sum)` (`424..488`)
  have htd := call_void_u256_to_digits_wsSafe hs3_env
    (pExp := .var .local (ofString "u")) (aExp := .var .local (ofString "sum")) (off := 424)
    (by omega) (fun vp hvp => by simpa [evalHOLExact, hu_s3] using hvp.symm)
  refine WsSafe.seq htd.1 fun hn_td heff_td => ?_
  set s4 := (evaluateHOLFiniteState s3 _).2
  have hs4_env : WsEnv s s4 := hs3_env.step heff_td
  have hs4_loc : s4.locals = s3.locals := htd.2 hn_td
  have hu_s4 : s4.locals.lookup (ofString "u") =
      some (.val (.word (BitVec.ofNat 64 (globN s "u256_ws") + BitVec.ofNat 64 424))) := by
    rw [hs4_loc]; exact hu_s3
  have hu_add : ∀ c : Nat, c < 100 →
      BitVec.ofNat 64 (globN s "u256_ws") + BitVec.ofNat 64 424 + BitVec.ofNat 64 c =
        BitVec.ofNat 64 (globN s "u256_ws") + BitVec.ofNat 64 (424 + c) := by
    intro c hc
    rw [BitVec.add_assoc]; congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  -- 7. `store (u + 64) 1` (`488`), `store (u + 72) 0` (`496`), tail-call `digits_divmod(u, 10, m)`
  refine WsSafe.seq_store_ws_const_off hs4_env (off := 488)
    (by
      simp only [evalHOLExact, evalListHOLExact, hu_s4, wordOpHOL, wordOp, valueIsWord, valueWord,
        List.all, List.map, Bool.and_self, ↓reduceIte, Option.map, List.foldr]
      congr 3
      rw [show (64#64 + 0 : BitVec 64) = 64#64 from BitVec.add_zero _]
      exact hu_add 64 (by omega))
    (by omega)
    (fun _ hv => eval_word_of_const hv) fun s5 hs5_env hs5_loc => ?_
  have hu_s5 : s5.locals.lookup (ofString "u") =
      some (.val (.word (BitVec.ofNat 64 (globN s "u256_ws") + BitVec.ofNat 64 424))) := by
    rw [hs5_loc]; exact hu_s4
  refine WsSafe.seq_store_ws_const_off hs5_env (off := 496)
    (by
      simp only [evalHOLExact, evalListHOLExact, hu_s5, wordOpHOL, wordOp, valueIsWord, valueWord,
        List.all, List.map, Bool.and_self, ↓reduceIte, Option.map, List.foldr]
      congr 3
      rw [show (72#64 + 0 : BitVec 64) = 72#64 from BitVec.add_zero _]
      exact hu_add 72 (by omega))
    (by omega)
    (fun _ hv => eval_word_of_const hv) fun s6 hs6_env hs6_loc => ?_
  have hm_s6 : s6.locals.lookup (ofString "m") =
      some (.rStruct [.val (.word m0), .val (.word m1), .val (.word m2), .val (.word m3)]) := by
    rw [hs6_loc, hs5_loc, hs4_loc]; exact hm_s3
  exact call_tail_digits_divmod_wsSafe hs6_env (by omega)
    (by simp only [evalHOLExact]; exact hm_s6) hm_nz

theorem eps_u256_mulmod : EvmPreservingSpec (fun _ => True) (fun _ _ _ => True) (ofString "u256_mulmod") := by
  refine eps_of_wsSafe 76 (by rw [guestAst_len]; decide) Guest.Software.guestFn_u256_mulmod rfl ?_
  intro F s he ⟨vals0, hlk0⟩
  obtain ⟨_, m0, m1, m2, m3, hm⟩ := lookup_three_comb4_locals lookup_u256_mulmod hlk0
  dsimp only [extractFn, Guest.Software.guestFn_u256_mulmod,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural,
    Option.map, List.map]
  -- 1. `if ((m0 | m1 | m2 | m3) == 0) return 0`
  refine WsSafe.seq (WsSafe.ite (fun _ _ _ => WsSafe.return_exp _ _ _) (fun _ => WsSafe.skip _ _)) ?_
  intro hn_m0 _
  obtain ⟨hcmp_m0, hs_m0⟩ := ite_return_skip_none hn_m0
  have hm_nz : (m0 ||| m1 ||| m2 ||| m3) ≠ 0 := eval_or4_ne_zero hm hcmp_m0
  rw [hs_m0]
  -- 2. `dec "u" (u256_ws + 424)`
  refine WsSafe.dec fun vu hvu _ => ?_
  rw [eval_u256_ws_plus he hvu]
  set s1 := setVarHOLFinite (ofString "u")
    (.val (.word (BitVec.ofNat 64 (globN s "u256_ws") + BitVec.ofNat 64 424))) s
  have hs1_env : WsEnv s s1 := he.with_locals_clock _ _
  have hu_s1 : s1.locals.lookup (ofString "u") =
      some (.val (.word (BitVec.ofNat 64 (globN s "u256_ws") + BitVec.ofNat 64 424))) := by
    simp [s1, setVarHOLFinite, FUPDATE]
  have hm_s1 : s1.locals.lookup (ofString "m") =
      some (.rStruct [.val (.word m0), .val (.word m1), .val (.word m2), .val (.word m3)]) := by
    simp [s1, setVarHOLFinite, FUPDATE, show ofString "u" ≠ ofString "m" by decide, hm]
  -- 3. `if (high limbs == 0) { decCall p mul64x64 ... } else skip`
  refine WsSafe.seq ?_ ?_
  · refine WsSafe.ite (fun _ _ _ => ?_) (fun _ => WsSafe.skip _ _)
    refine WsSafe.decCall_ro hs1_env (by decide) fun vp cpost_p hs2_env _ _ => ?_
    set s2 := setVarHOLFinite (ofString "p") vp { cpost_p with locals := s1.locals }
    refine WsSafe.seq
      (WsSafe.ite
        (fun _ _ _ => WsSafe.call_tail fun _ _ _ _ _ hl _ => call_u256_mod_wsSafe hs2_env hl)
        (fun _ => WsSafe.skip _ _)) ?_
    intro hn_p1 _
    rw [ite_tail_skip_none hn_p1]
    have hu_s2 : s2.locals.lookup (ofString "u") =
        some (.val (.word (BitVec.ofNat 64 (globN s "u256_ws") + BitVec.ofNat 64 424))) := by
      simp [s2, setVarHOLFinite, FUPDATE, show ofString "p" ≠ ofString "u" by decide, hu_s1]
    have htd_p := call_void_u256_to_digits_wsSafe hs2_env
      (pExp := .var .local (ofString "u"))
      (aExp := .rstruct [.rfield 0 (.var .local (ofString "p")), .rfield 1 (.var .local (ofString "p")), .const 0#64, .const 0#64])
      (off := 424) (by omega) (fun v hv => by simpa [evalHOLExact, hu_s2] using hv.symm)
    refine WsSafe.seq htd_p.1 fun hn_tdp heff_tdp => ?_
    set s3 := (evaluateHOLFiniteState s2
      (.call (some (none, none)) (ofString "u256_to_digits")
        [.var .local (ofString "u"),
         .rstruct [.rfield 0 (.var .local (ofString "p")), .rfield 1 (.var .local (ofString "p")), .const 0#64, .const 0#64]])).2
    have hs3_env : WsEnv s s3 := hs2_env.step heff_tdp
    have hm_s3 : s3.locals.lookup (ofString "m") =
        some (.rStruct [.val (.word m0), .val (.word m1), .val (.word m2), .val (.word m3)]) := by
      rw [htd_p.2 hn_tdp]
      simp [s2, setVarHOLFinite, FUPDATE, show ofString "p" ≠ ofString "m" by decide, hm_s1]
    exact call_tail_digits_divmod_wsSafe hs3_env (by omega)
      (by simp only [evalHOLExact]; exact hm_s3) hm_nz
  -- Continuation when fast-path `ite` finishes with `none`: fast-path ends in tail-call `digits_divmod`, so `.1 = none` implies `s1`!
  intro hn_fast _
  have hs_fast := by
    let p_fast : ProgHOL 64 :=
      .ite (.cmp .equal (.op .or [.rfield 1 (.var .local (ofString "a")),
                                  .rfield 2 (.var .local (ofString "a")),
                                  .rfield 3 (.var .local (ofString "a")),
                                  .rfield 1 (.var .local (ofString "b")),
                                  .rfield 2 (.var .local (ofString "b")),
                                  .rfield 3 (.var .local (ofString "b"))]) (.const 0#64))
        (.decCall (ofString "p") (.comb [.one, .one]) (ofString "mul64x64")
          [.rfield 0 (.var .local (ofString "a")), .rfield 0 (.var .local (ofString "b"))]
          (.seq
            (.ite (.cmp .equal (.rfield 1 (.var .local (ofString "p"))) (.const 0#64))
              (.call none (ofString "u256_mod")
                [.rstruct [.rfield 0 (.var .local (ofString "p")), .const 0#64, .const 0#64, .const 0#64],
                 .var .local (ofString "m")])
              .skip)
            (.seq
              (.call (some (none, none)) (ofString "u256_to_digits")
                [.var .local (ofString "u"),
                 .rstruct [.rfield 0 (.var .local (ofString "p")), .rfield 1 (.var .local (ofString "p")), .const 0#64, .const 0#64]])
              (.call none (ofString "digits_divmod")
                [.var .local (ofString "u"), .const 4#64, .var .local (ofString "m")]))))
        .skip
    show (evaluateHOLFiniteState s1 p_fast).2 = s1
    change (evaluateHOLFiniteState s1 p_fast).1 = none at hn_fast
    dsimp only [p_fast] at hn_fast ⊢
    rw [evaluateHOLFiniteState_ite] at hn_fast ⊢
    rcases hcond : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
      (.cmp .equal (.op .or [.rfield 1 (.var .local (ofString "a")),
                             .rfield 2 (.var .local (ofString "a")),
                             .rfield 3 (.var .local (ofString "a")),
                             .rfield 1 (.var .local (ofString "b")),
                             .rfield 2 (.var .local (ofString "b")),
                             .rfield 3 (.var .local (ofString "b"))]) (.const 0#64)) with _ | v
    · simp [hcond] at hn_fast
    · cases v with
      | val hl =>
        cases hl with
        | word w =>
          simp only [hcond] at hn_fast ⊢
          by_cases hw0 : w = 0
          · subst hw0; simp [evaluateHOLFiniteState_skip]
          · simp only [hw0, ↓reduceIte, Bool.false_eq_true, evaluateHOLFiniteState_decCall_fixClockRewrite] at hn_fast
            exfalso; revert hn_fast
            rcases evalListHOLFinite s1 (h := fun a => Classical.propDecidable (s1.memaddrs a)) _ with _ | vals
            · simp
            · dsimp only
              rcases lookupCodeHOLFinite s1.code.lookup (ofString "mul64x64") vals with _ | ⟨bd, cal, rs⟩
              · simp
              · dsimp only; split
                · simp
                · rcases evaluateHOLFiniteState (callEntryStateHOLFinite s1 cal) bd with ⟨rb, cp⟩
                  cases rb with
                  | none => simp
                  | some r0 =>
                    cases r0 with
                    | returned rv =>
                      dsimp only; split
                      · rw [evaluateHOLFiniteState_seq_line780]
                        rcases evaluateHOLFiniteState _ (.ite _ _ _) with ⟨ri, si⟩
                        cases ri; swap; · simp
                        dsimp only
                        rw [evaluateHOLFiniteState_seq_line780]
                        rcases evaluateHOLFiniteState si (.call (some (none, none)) _ _) with ⟨rc1, sc1⟩
                        cases rc1; swap; · simp
                        dsimp only
                        rw [evaluateHOLFiniteState_call]
                        rcases evalListHOLFinite sc1 (h := fun a => Classical.propDecidable (sc1.memaddrs a)) _ with _ | vals2
                        · simp
                        · dsimp only
                          rcases lookupCodeHOLFinite sc1.code.lookup (ofString "digits_divmod") vals2 with _ | ⟨bd2, cal2, rs2⟩
                          · simp
                          · dsimp only; split
                            · simp
                            · rcases evaluateHOLFiniteState (callEntryStateHOLFinite sc1 cal2) bd2 with ⟨rb2, cp2⟩
                              cases rb2 with
                              | none => simp
                              | some r2 =>
                                cases r2 with
                                | returned _ => dsimp only; split <;> simp
                                | exception _ _ | timeOut | error | «break» | «continue» | finalFfi _ => simp
                      · simp
                    | exception _ _ | timeOut | error | «break» | «continue» | finalFfi _ => simp
      | rStruct _ => simp [hcond] at hn_fast
      | nStruct _ _ => simp [hcond] at hn_fast
  rw [hs_fast]
  -- 4. Full path: `decCall "f" .comb8 "u256_mul_full" [a, b]`
  refine WsSafe.decCall_ro hs1_env (by decide) fun vf cpost_f hs4_env _ _ => ?_
  set s4 := setVarHOLFinite (ofString "f") vf { cpost_f with locals := s1.locals }
  have hu_s4 : s4.locals.lookup (ofString "u") =
      some (.val (.word (BitVec.ofNat 64 (globN s "u256_ws") + BitVec.ofNat 64 424))) := by
    simp [s4, setVarHOLFinite, FUPDATE, show ofString "f" ≠ ofString "u" by decide, hu_s1]
  have htd_lo := call_void_u256_to_digits_wsSafe hs4_env
    (pExp := .var .local (ofString "u"))
    (aExp := .rstruct [.rfield 0 (.var .local (ofString "f")), .rfield 1 (.var .local (ofString "f")),
                       .rfield 2 (.var .local (ofString "f")), .rfield 3 (.var .local (ofString "f"))])
    (off := 424) (by omega) (fun v hv => by simpa [evalHOLExact, hu_s4] using hv.symm)
  refine WsSafe.seq htd_lo.1 fun hn_lo heff_lo => ?_
  set s5 := (evaluateHOLFiniteState s4 _).2
  have hs5_env : WsEnv s s5 := hs4_env.step heff_lo
  have hs5_loc : s5.locals = s4.locals := htd_lo.2 hn_lo
  have hu_s5 : s5.locals.lookup (ofString "u") =
      some (.val (.word (BitVec.ofNat 64 (globN s "u256_ws") + BitVec.ofNat 64 424))) := by
    rw [hs5_loc]; exact hu_s4
  have htd_hi := call_void_u256_to_digits_wsSafe hs5_env
    (pExp := .op .add [.var .local (ofString "u"), .const 64#64])
    (aExp := .rstruct [.rfield 4 (.var .local (ofString "f")), .rfield 5 (.var .local (ofString "f")),
                       .rfield 6 (.var .local (ofString "f")), .rfield 7 (.var .local (ofString "f"))])
    (off := 488) (by omega)
    (fun v hv => by
      simp only [evalHOLExact, evalListHOLExact, hu_s5, wordOpHOL, wordOp, valueIsWord, valueWord,
        List.all, List.map, Bool.and_self, ↓reduceIte, Option.map, List.foldr] at hv
      injection hv with hv'
      rw [← hv']; congr 2
      rw [show (64#64 + 0 : BitVec 64) = 64#64 from BitVec.add_zero _, BitVec.add_assoc]
      congr 1)
  refine WsSafe.seq htd_hi.1 fun hn_hi heff_hi => ?_
  set s6 := (evaluateHOLFiniteState s5 _).2
  have hs6_env : WsEnv s s6 := hs5_env.step heff_hi
  have hm_s6 : s6.locals.lookup (ofString "m") =
      some (.rStruct [.val (.word m0), .val (.word m1), .val (.word m2), .val (.word m3)]) := by
    rw [htd_hi.2 hn_hi, hs5_loc]
    simp [s4, setVarHOLFinite, FUPDATE, show ofString "f" ≠ ofString "m" by decide, hm_s1]
  exact call_tail_digits_divmod_wsSafe hs6_env (by omega)
    (by simp only [evalHOLExact]; exact hm_s6) hm_nz

end InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers
