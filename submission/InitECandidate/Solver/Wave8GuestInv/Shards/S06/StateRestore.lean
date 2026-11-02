import InitECandidate.Solver.Wave8GuestInv.Shards.S06.Base

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-!
# Wave 8 Shard `s06` — `state_restore` and `frame_epilogue`

Proves:
- `fb_state_restore` (idx 359): loop decreasing `journal_n` on every active iteration, preserved across `stateRestoreTail` via `GuestGlobalKeep.evaluate_keepsG`.
- `fb_frame_epilogue` (idx 582): conditional call to `state_restore`.
-/

namespace InitECandidate.Solver.Wave8GuestInv.S06

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open Guest.Software
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestGlobalKeep
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.PanTerminatingBounded

variable {GuestInv : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop} [GuestInvLike GuestInv]

/-! ## 1. Transitive call cone of `stateRestoreTail` does not modify `journal_n` -/

def goodJournalN (f : MlS) : Bool :=
  f == ofString "htab_set" || f == ofString "htab_del" ||
  f == ofString "htab_find_leaf" || f == ofString "htab_new_leaf" ||
  f == ofString "memeq" || f == ofString "htab_first_diff" ||
  f == ofString "htab_new_internal" || f == ofString "htab_new_node" ||
  f == ofString "memcpy" || f == ofString "htab_grow" ||
  f == ofString "alloc" || f == ofString "trap_with"

private theorem keeps_of_idx {f : MlS} {values : List (ValueHOL 64)} {body : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {rs : ShapeHOL}
    (i : Nat) (hi : i < guestAst.length) (fn : FunDecl (BitVec 64))
    (hd : guestAst[i] = .function fn) (hname : f = ofString fn.name)
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup f values = some (body, callee, rs))
    (hk : keepsG (ofString "journal_n") goodJournalN
      (FrontendCodecComputation.progToHOLStructural fn.body) = true) :
    keepsG (ofString "journal_n") goodJournalN body = true := by
  subst hname
  have hcode := lookup_of_guestAst_getElem i hi fn hd
  obtain ⟨params', rs', hc⟩ := lookupCode_installed hl
  rw [hcode] at hc
  injection hc with h1
  injection h1 with _ h2
  injection h2 with hbody _
  rw [← hbody]
  exact hk

theorem goodJournalN_bodies :
    ∀ function, goodJournalN function = true → ∀ values body callee rs,
      lookupCodeHOLFinite originalRuntimeCode.lookup function values = some (body, callee, rs) →
      keepsG (ofString "journal_n") goodJournalN body = true := by
  intro f hf values body callee rs hl
  simp only [goodJournalN, Bool.or_eq_true, beq_iff_eq] at hf
  rcases hf with ((((((((((h | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h
  · exact keeps_of_idx 138 (by rw [guestAst_len]; decide) (extractFn guestFn_htab_set) rfl h hl rfl
  · exact keeps_of_idx 139 (by rw [guestAst_len]; decide) (extractFn guestFn_htab_del) rfl h hl rfl
  · exact keeps_of_idx 131 (by rw [guestAst_len]; decide) (extractFn guestFn_htab_find_leaf) rfl h hl rfl
  · exact keeps_of_idx 135 (by rw [guestAst_len]; decide) (extractFn guestFn_htab_new_leaf) rfl h hl rfl
  · exact keeps_of_idx 18 (by rw [guestAst_len]; decide) (extractFn guestFn_memeq) rfl h hl rfl
  · exact keeps_of_idx 130 (by rw [guestAst_len]; decide) (extractFn guestFn_htab_first_diff) rfl h hl rfl
  · exact keeps_of_idx 136 (by rw [guestAst_len]; decide) (extractFn guestFn_htab_new_internal) rfl h hl rfl
  · exact keeps_of_idx 134 (by rw [guestAst_len]; decide) (extractFn guestFn_htab_new_node) rfl h hl rfl
  · exact keeps_of_idx 16 (by rw [guestAst_len]; decide) (extractFn guestFn_memcpy) rfl h hl rfl
  · exact keeps_of_idx 137 (by rw [guestAst_len]; decide) (extractFn guestFn_htab_grow) rfl h hl rfl
  · exact keeps_of_idx 7 (by rw [guestAst_len]; decide) (extractFn guestFn_alloc) rfl h hl rfl
  · exact keeps_of_idx 3 (by rw [guestAst_len]; decide) (extractFn guestFn_trap_with) rfl h hl rfl

abbrev stateRestoreCond : ExpHOL 64 :=
  .cmp .lower (.var .local (ofString "snap")) (.var .global (ofString "journal_n"))

abbrev stateRestoreAssign : ProgHOL 64 :=
  .assign .global (ofString "journal_n")
    (.op .sub [.var .global (ofString "journal_n"), .const (BitVec.ofNat 64 1)])

abbrev stateRestoreTail : ProgHOL 64 :=
  .dec (ofString "r") .one
    (.op .add [.var .global (ofString "journal"),
      .panop .mul [.var .global (ofString "journal_n"), .const (BitVec.ofNat 64 32)]])
    (.dec (ofString "t") .one (.load .one (.var .local (ofString "r")))
      (.dec (ofString "key") .one
        (.load .one (.op .add [.var .local (ofString "r"), .const (BitVec.ofNat 64 8)]))
        (.ite (.cmp .notEqual
            (.load .one (.op .add [.var .local (ofString "r"), .const (BitVec.ofNat 64 16)]))
            (.const (BitVec.ofNat 64 0)))
          (.call (some (none, none)) (ofString "htab_set")
            [.var .local (ofString "t"), .var .local (ofString "key"),
             .load .one (.op .add [.var .local (ofString "r"), .const (BitVec.ofNat 64 24)])])
          (.call (some (none, none)) (ofString "htab_del")
            [.var .local (ofString "t"), .var .local (ofString "key")]))))

theorem stateRestore_journal_step {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode)
    (hact : LoopActive stateRestoreCond s) :
    globN (evaluateHOLFiniteState (decClockHOLFinite s) (.seq stateRestoreAssign stateRestoreTail)).2
      "journal_n" < globN s "journal_n" := by
  obtain ⟨word, hw, hnz⟩ := hact
  change evalAt s _ = _ at hw
  obtain ⟨a, b, ha, hb, hword⟩ := evalAt_cmp s .lower _ _ word hw
  simp only [evalAt, evalHOLExact] at hb
  have hjb : s.globals.lookup (ofString "journal_n") = some (.val (.word b)) := by simpa using hb
  have hcmp : Flapjack.Compiler.Encoders.Asm.wordCmpHOL .lower a b = true := by
    by_contra hc
    simp [hc] at hword
    exact hnz hword
  have hlt : a.toNat < b.toNat := by
    simpa [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, decide_eq_true_eq, BitVec.lt_def] using hcmp
  have hassign : evaluateHOLFiniteState (decClockHOLFinite s) stateRestoreAssign =
      (none, setGlobalHOLFinite (ofString "journal_n") (.val (.word (b - 1))) (decClockHOLFinite s)) := by
    simp [stateRestoreAssign, evaluateHOLFiniteState_assign, decClockHOLFinite, evalHOLExact,
      evalListHOLExact, hjb, wordOpHOL, wordOp, valueIsWord, valueWord, lookupKvarHOLExact,
      isValidValueHOLExact, setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL]
  rw [evaluateHOLFiniteState_seq_line780, hassign]
  dsimp only
  have hkeep := evaluate_keepsG (ofString "journal_n") goodJournalN goodJournalN_bodies
    stateRestoreTail rfl
    (setGlobalHOLFinite (ofString "journal_n") (.val (.word (b - 1))) (decClockHOLFinite s))
    hcode
  have hmid : (setGlobalHOLFinite (ofString "journal_n") (.val (.word (b - 1)))
      (decClockHOLFinite s)).globals.lookup (ofString "journal_n") =
      some (.val (.word (b - 1))) := by
    simp [setGlobalHOLFinite, decClockHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hpost := hkeep.trans hmid
  have hsub : (b - 1).toNat < b.toNat := by
    have := b.isLt
    simp [BitVec.toNat_sub]
    omega
  simp only [globN, hpost, hjb]
  exact hsub

/-! ## 2. Leaf #6: `fb_state_restore` (idx 359) -/

attribute [local irreducible] TerminatingProgBoundedOn

theorem fb_state_restore_of
    (h_htab_set : TerminatingFunBoundedOn GuestInv (ofString "htab_set") K.«htab_set»)
    (h_htab_del : TerminatingFunBoundedOn GuestInv (ofString "htab_del") K.«htab_del») :
    TerminatingFunBoundedOn GuestInv (ofString "state_restore") K.«state_restore» := by
  apply onFun_le 359 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_state_restore _ rfl
  · htab_unfold Guest.Software.guestFn_state_restore
    apply TerminatingProgBoundedOn.seq_guestInv
    · apply TerminatingProgBoundedOn.while_rank (N := 2 ^ 64) (fun s => globN s "journal_n")
        (fun s hs => guestInv_decClock s hs)
      · htab_walk
      · intro F s _ _ _
        simp only [globN]
        split
        · rename_i w _
          exact Nat.le_of_lt w.isLt
        · omega
      · intro F s hcode hs hact _
        exact ⟨guestInv_evaluate _ _ (guestInv_decClock s hs), stateRestore_journal_step s hcode hact⟩
    · exact straightOn _ rfl
  · htab_bound K.«state_restore»

/-! ## 3. Leaf #7: `fb_frame_epilogue` (idx 582) -/

theorem fb_frame_epilogue_of
    (h_state_restore : TerminatingFunBoundedOn GuestInv (ofString "state_restore") K.«state_restore») :
    TerminatingFunBoundedOn GuestInv (ofString "frame_epilogue") K.«frame_epilogue» := by
  apply onFun_le 582 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_frame_epilogue _ rfl
  · htab_unfold Guest.Software.guestFn_frame_epilogue
    htab_walk
  · htab_bound K.«frame_epilogue»

end InitECandidate.Solver.Wave8GuestInv.S06
