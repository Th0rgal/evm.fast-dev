import InitECandidate.Solver.Wave8GuestInv.Shards.S13.Walk

/- Shared-load result lemma reused from GuestBoundMain.lean at base 7640c93ae. -/
set_option autoImplicit false
set_option maxRecDepth 100000

namespace InitECandidate.Solver.Wave8Leaves.S13

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8Leaves.S13.Spec

variable {GuestInv : ∀ {F : Type}, Flapjack.PanSemStateFiniteExact 64 F → Prop}
  [IsGuestInv GuestInv]
variable [HasOrdinaryDomain GuestInv]


theorem evaluate_shMemLoad_local_none {F : Type}
    (state : PanSemStateFiniteExact 64 F) (operator : OpSize) (name : MlS) (address : ExpHOL 64)
    {post : PanSemStateFiniteExact 64 F}
    (hrun : evaluateHOLFiniteState state (.shMemLoad operator .local name address) = (none, post)) :
    ∃ val : BitVec 64,
      post.locals = state.locals.update (name, .val (.word val)) ∧
      post.code = state.code ∧
      post.clock = state.clock := by
  classical
  rw [evaluateHOLFiniteState_shMemLoad_source] at hrun
  split at hrun
  · rename_i addr haddr
    split at hrun
    · rename_i old hlookup
      unfold shMemLoadHOLFiniteExact at hrun
      split at hrun
      · split at hrun
        · split at hrun
          · simp at hrun
          · obtain ⟨_, rfl⟩ := Prod.mk.inj hrun
            exact ⟨_, rfl, rfl, rfl⟩
        · simp at hrun
      · split at hrun
        · split at hrun
          · simp at hrun
          · obtain ⟨_, rfl⟩ := Prod.mk.inj hrun
            exact ⟨_, rfl, rfl, rfl⟩
        · simp at hrun
    · simp at hrun
  · simp at hrun



def inputLoad : ProgHOL 64 :=
  .shMemLoad .opW .local (ofString "w")
    (.op .add [.const 1073741840, .var .local (ofString "i")])
def inputStore : ProgHOL 64 :=
  .store (.op .add [.var .local (ofString "p"), .var .local (ofString "i")])
    (.var .local (ofString "w"))
def inputTick : ProgHOL 64 :=
  .assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 8])
def inputBody : ProgHOL 64 := .seq inputLoad (.seq inputStore inputTick)

theorem inputBody_access : FirstAccess (GuestInv := GuestInv) (ofString "p") (ofString "i") inputBody := by
  intro F s hP h
  change (evaluateHOLFiniteState s (.seq inputLoad (.seq inputStore inputTick))).1 = none at h
  rw [evaluateHOLFiniteState_seq_line780] at h
  rcases hr : evaluateHOLFiniteState s inputLoad with ⟨r, mid⟩
  rw [hr] at h
  cases r with
  | some r => simp at h
  | none =>
    dsimp only at h
    have hm : GuestInv mid := by
      have hg := guestInv_evaluate s inputLoad hP
      rw [hr] at hg
      exact hg
    obtain ⟨w, hl, _, _⟩ := evaluate_shMemLoad_local_none s .opW (ofString "w") _ hr
    have hs := seq_none_first mid inputStore inputTick h
    have hv : ∀ (hd : DecidablePred mid.memaddrs) (val : ValueHOL 64),
        @evalHOLExact 64 F _ mid.toExact hd (.var .local (ofString "w")) = some val →
        ∃ v, val = .val v := by
      intro hd val hv
      simp only [evalHOLExact] at hv
      simp [hl, HolFiniteMapExact.lookup_update, FUPDATE] at hv
      exact ⟨_, hv.symm⟩
    obtain ⟨x, y, hx, hy, hlo, hhi⟩ :=
      storeAccess_at (ofString "p") (ofString "i") (.var .local (ofString "w")) mid hm hv hs
    refine ⟨x, y, ?_, ?_, hlo, hhi⟩
    · simpa [hl, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "w" ≠ ofString "p" by decide] using hx
    · simpa [hl, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "w" ≠ ofString "i" by decide] using hy

/-- A successful shared load changes only `w`; the store/tick suffix advances `i`.
The generic `avoidsLocal` recognizer intentionally does not cover shared loads. -/
theorem inputBody_progress {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) (x y : BitVec 64)
    (hp : s.locals.lookup (ofString "p") = some (.val (.word x)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word y)))
    (hnone : (evaluateHOLFiniteState s inputBody).1 = none) :
    (evaluateHOLFiniteState s inputBody).2.locals.lookup (ofString "p") = some (.val (.word x)) ∧
    (evaluateHOLFiniteState s inputBody).2.locals.lookup (ofString "i") = some (.val (.word (y + 8))) := by
  unfold inputBody at hnone ⊢
  rw [evaluateHOLFiniteState_seq_line780] at hnone ⊢
  rcases hr : evaluateHOLFiniteState s inputLoad with ⟨r, mid⟩
  simp only [hr] at hnone
  cases r with
  | some r => simp at hnone
  | none =>
    dsimp only at hnone ⊢
    obtain ⟨w, hl, hc, _⟩ := evaluate_shMemLoad_local_none s .opW (ofString "w") _ hr
    have hp' : mid.locals.lookup (ofString "p") = some (.val (.word x)) := by
      simpa [hl, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "w" ≠ ofString "p" by decide] using hp
    have hi' : mid.locals.lookup (ofString "i") = some (.val (.word y)) := by
      simpa [hl, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "w" ≠ ofString "i" by decide] using hi
    have hcount : CountedBody (ofString "i") 8 (.seq inputStore inputTick) 0 :=
      CountedBody.seq inputStore (ProgBounded.straight _ rfl) rfl rfl CountedBody.incr
    obtain ⟨_, _, _, _, hlast⟩ := hcount.run mid (hc.trans hcode) y hi' (Nat.zero_le _)
    obtain ⟨hiy, _⟩ := hlast hnone
    have hkeep := evaluate_avoidsLocal_flowing (ofString "p") (.seq inputStore inputTick)
      rfl mid (Or.inl hnone)
    exact ⟨hkeep.trans hp', hiy⟩

theorem input_loop (cond : ExpHOL 64) :
    TerminatingProgBoundedOn GuestInv (.while cond inputBody)
      ((domainBytes + 1 + 1) * (0 + 1)) := by
  refine TerminatingProgBoundedOn.while_rank (walkMu (ofString "p") (ofString "i"))
    (fun s hs => guestInv_decClock s hs) (straightOn _ rfl)
    (fun s _ _ _ => walkMu_le (ofString "p") (ofString "i") s) ?_
  intro F s hcode hP _ hflow
  have hPd := guestInv_decClock s hP
  have hnone : (evaluateHOLFiniteState (decClockHOLFinite s) inputBody).1 = none := by
    rcases hflow with h | h
    · exact h
    · exact False.elim ((evaluate_noTopContinue inputBody rfl (decClockHOLFinite s)) h)
  obtain ⟨x, y, hx, hy, hlo, hhi⟩ := inputBody_access (decClockHOLFinite s) hPd hnone
  obtain ⟨hp', hi'⟩ := inputBody_progress (decClockHOLFinite s) hcode x y hx hy hnone
  refine ⟨guestInv_evaluate _ _ hPd, ?_⟩
  have hx' : s.locals.lookup (ofString "p") = some (.val (.word x)) := hx
  have hy' : s.locals.lookup (ofString "i") = some (.val (.word y)) := hy
  unfold walkMu
  rw [hp', hi', hx', hy']
  dsimp only
  rw [← BitVec.add_assoc]
  exact walkRank_step _ 8 (by decide) (by decide) hlo hhi

end InitECandidate.Solver.Wave8Leaves.S13
