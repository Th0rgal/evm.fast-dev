import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.MsB2dExtCodeChainNz

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 200000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.EvmBase
open InitECandidate.Solver.Wave8GuestInv.EvmStepLemmas
open InitECandidate.Solver.Wave8GuestInv.EvmFrameSpecs
open InitECandidate.Solver.Wave8GuestInv.R16Shards
open InitECandidate.Solver.Wave8M19.Htab
open InitECandidate.Solver.Wave8GuestInv.HtabC00Ports
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.HeadMemBridge
open R10Shards.GbodyProcessMsg
open InitECandidate.Solver.Wave8GuestInv.R16WkAcctWs
open InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28

section CodeBounded

/-- Live code-database values designate aligned two-word records with bounded code length `< 2^40`.
Unlike `NodeDbEntriesStrong`, the code pointer `[p]` may lie outside `[sourceBase, heap_ptr)`
(e.g., `null_address` with `code_len = 0` in `set_delegation` clear). -/
def NodeDbEntriesBounded {F : Type} (s : PanSemStateFiniteExact 64 F) (db : Nat) : Prop :=
  ∀ p ∈ htabValues s db, WordsOK s (p, 16) ∧ memW s (p + 8) < 2 ^ 40

/-- Protected 16-byte code-DB payload records in old heap, with bounded code length `< 2^40`. -/
def CodeDbPayloadBounded {F : Type} (s : PanSemStateFiniteExact 64 F)
    (S : List Nat) (db : Nat) : Prop :=
  NodeDbEntriesBounded s db ∧ ∀ p ∈ htabValues s db,
    Inside (p, 16) sourceBase (globN s "heap_ptr") ∧ p + 16 ≤ 2 ^ 64 ∧
    (∀ t ∈ S, ∀ i ∈ htabFootprint s t, Disj (p, 16) i) ∧
    ∀ i ∈ fixedObjects s, Disj (p, 16) i

/-- Nonzero-root code-DB payload boundedness across `ws+16`, `bs+48`, `ts+48`. -/
def CodeDbPayloadBoundedNz {F : Type} (s : PanSemStateFiniteExact 64 F)
    (S : List Nat) : Prop :=
  ∀ g k, (g, k) ∈ ([("ws", 16), ("bs", 48), ("ts", 48)] : List (String × Nat)) →
    globN s g ≠ 0 → memW s (globN s g + k) ≠ 0 →
    CodeDbPayloadBounded s S (memW s (globN s g + k))

/-- Execution context for code/account/storage callees carrying `CodeDbPayloadBoundedNz`. -/
def CodeBoundedCtxNz {F : Type} (s : PanSemStateFiniteExact 64 F)
    (S Nd : List Nat) : Prop :=
  ArenaReady s ∧ WorldTypedWith s S Nd ∧ CodeDbPayloadBoundedNz s S ∧
    s.code = originalRuntimeCode ∧ s.eshapes.lookup (ofString "StateErr") = some .one

/-- Strengthened `EvmMsgReady` carrying `CodeDbPayloadBoundedNz` (preserved across `set_code`). -/
def EvmMsgReadyBounded : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ ∃ S, EvmInvAt s S ∧
    MsgOwned s S (memW s (globN s "ev" + 112)) ∧ CodeDbPayloadBoundedNz s S

theorem nodeDbEntriesBounded_of_strong {F : Type} {s : PanSemStateFiniteExact 64 F} {db : Nat}
    (hA : ArenaReady s) (h : NodeDbEntriesStrong s db) : NodeDbEntriesBounded s db := by
  intro p hp
  obtain ⟨hw, hin⟩ := h p hp
  exact ⟨hw, dispatch_code_length_lt hA hin⟩

theorem codeDbPayloadBounded_of_strong {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S : List Nat} {db : Nat} (hA : ArenaReady s) (h : CodeDbPayloadStrong s S db) :
    CodeDbPayloadBounded s S db :=
  ⟨nodeDbEntriesBounded_of_strong hA h.1, h.2⟩

theorem codeDbPayloadBoundedNz_of_nonzero {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S : List Nat} (hA : ArenaReady s) (h : CodeDbPayloadNonzero s S) :
    CodeDbPayloadBoundedNz s S :=
  fun g k hgk hgnz hdb => codeDbPayloadBounded_of_strong hA (h g k hgk hgnz hdb)

theorem evmMsgReadyBounded_of_codeStrong {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : EvmMsgReadyCodeStrong s) : EvmMsgReadyBounded s := by
  obtain ⟨hA, S, hI, hm, hC⟩ := h
  exact ⟨hA, S, hI, hm, codeDbPayloadBoundedNz_of_nonzero hA hC⟩

theorem evmMsgReady_of_bounded {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : EvmMsgReadyBounded s) : EvmMsgReady s := by
  obtain ⟨hA, S, hI, hm, _⟩ := h
  exact ⟨hA, S, hI, hm⟩

theorem evmInv_of_bounded {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : EvmMsgReadyBounded s) : EvmInv s :=
  evmInv_of_evmMsgReady s (evmMsgReady_of_bounded h)

theorem fk_frame_open_boundedNz :
    KeepsOn FrameOpenReadyCodeStrong EvmMsgReadyBounded (ofString "frame_open") := by
  obtain ⟨ps, b, rs, hl, hk⟩ := fk_frame_open_codeStrong
  exact ⟨ps, b, rs, hl, fun s hcode hP hex hnt hr =>
    evmMsgReadyBounded_of_codeStrong (hk s hcode hP hex hnt hr)⟩

theorem codeDbPayloadBounded_with_locals_clock {F : Type}
    (s : PanSemStateFiniteExact 64 F) (S : List Nat) (db : Nat)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    CodeDbPayloadBounded {s with locals := L, clock := k} S db ↔
      CodeDbPayloadBounded s S db := Iff.rfl

theorem codeDbPayloadBoundedNz_with_locals_clock {F : Type}
    (s : PanSemStateFiniteExact 64 F) (S : List Nat)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    CodeDbPayloadBoundedNz {s with locals := L, clock := k} S ↔
      CodeDbPayloadBoundedNz s S := Iff.rfl

theorem localsFree_evmMsgReadyBounded : LocalsFree EvmMsgReadyBounded := by
  intro F s locals k ⟨hA, S, hI, hm, hC⟩
  exact ⟨localsFree_arenaReady s locals k hA, S,
    (evmInvAt_with_locals s locals k S).2 hI,
    (msgOwned_with_locals s locals k S _).2 hm,
    (codeDbPayloadBoundedNz_with_locals_clock s S locals k).2 hC⟩

theorem codeBoundedCtxNz_with_locals_clock {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat)
    (h : CodeBoundedCtxNz s S Nd) :
    CodeBoundedCtxNz {s with locals := L, clock := k} S Nd :=
  ⟨localsFree_arenaReady s L k h.1,
   ⟨(tablesTyped_with_locals s L k S).2 h.2.1.1, h.2.1.2.1, h.2.1.2.2.1, h.2.1.2.2.2⟩,
   (codeDbPayloadBoundedNz_with_locals_clock s S L k).2 h.2.2.1,
   h.2.2.2.1, h.2.2.2.2⟩

theorem codeBoundedCtxNz_setVar {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (x : MlS) (v : ValueHOL 64) (h : CodeBoundedCtxNz s S Nd) :
    CodeBoundedCtxNz (setVarHOLFinite x v s) S Nd := by
  have heq : setVarHOLFinite x v s = {s with locals := (setVarHOLFinite x v s).locals, clock := s.clock} := by
    cases s; rfl
  rw [heq]; exact codeBoundedCtxNz_with_locals_clock _ _ h

theorem codeBoundedCtxNz_emptyLocals {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (h : CodeBoundedCtxNz s S Nd) :
    CodeBoundedCtxNz (emptyLocalsHOLFinite s) S Nd := by
  have heq : emptyLocalsHOLFinite s = {s with locals := (emptyLocalsHOLFinite s).locals, clock := s.clock} := by
    cases s; rfl
  rw [heq]; exact codeBoundedCtxNz_with_locals_clock _ _ h

theorem codeBoundedCtxNz_resVar {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (h : CodeBoundedCtxNz s S Nd) :
    CodeBoundedCtxNz {s with locals := L} S Nd := by
  have heq : ({s with locals := L} : PanSemStateFiniteExact 64 F) = {s with locals := L, clock := s.clock} := by
    cases s; rfl
  rw [heq]; exact codeBoundedCtxNz_with_locals_clock _ _ h

theorem code_record_words_bounded {F : Type} {s : PanSemStateFiniteExact 64 F}
    {v : Nat} (hwords : WordsOK s (v, 16)) (hb : memW s (v + 8) < 2 ^ 40) :
    ∃ code code_n : BitVec 64,
      s.memory (BitVec.ofNat 64 v) = .word code ∧
      s.memory (BitVec.ofNat 64 (v + 8)) = .word code_n ∧
      code_n.toNat < 2 ^ 40 := by
  obtain ⟨_, _, hw⟩ := hwords
  obtain ⟨code, hc⟩ := hw 0 (by omega)
  obtain ⟨code_n, hn⟩ := hw 1 (by omega)
  simp only [Nat.mul_zero, Nat.add_zero] at hc
  simp only [Nat.mul_one] at hn
  refine ⟨code, code_n, hc.2, hn.2, ?_⟩
  simpa [memW, hn.2] using hb

theorem nodedb_code_record_return_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
    (found ptr : BitVec 64)
    (hr : s.locals.lookup (ofString "r") =
      some (.rStruct [.val (.word found), .val (.word ptr)]))
    (hw : WordsOK s (ptr.toNat, 16)) (hb : memW s (ptr.toNat + 8) < 2 ^ 40) :
    Ret s (.return (.rstruct [.const 1,
      .load .one (.rfield 1 (.var .local (ofString "r"))),
      .load .one (.op .add [.rfield 1 (.var .local (ofString "r")), .const 8])]))
      (fun v post => ∃ code code_n : BitVec 64,
        v = .rStruct [.val (.word 1), .val (.word code), .val (.word code_n)] ∧
        code_n.toNat < 2 ^ 40 ∧ post = {s with locals := post.locals, clock := post.clock}) := by
  obtain ⟨code, code_n, hc, hn, hlt⟩ := code_record_words_bounded hw hb
  have hd0 := (hw.2.2 0 (by omega)).choose_spec.1
  have hd8 := (hw.2.2 1 (by omega)).choose_spec.1
  simp only [Nat.mul_zero, Nat.add_zero] at hd0
  simp only [Nat.mul_one] at hd8
  have hc' : s.memory ptr = .word code := by simpa using hc
  have hd0' : s.memaddrs ptr := by simpa using hd0
  have haddr : ptr + 8#64 = BitVec.ofNat 64 (ptr.toNat + 8) := by
    rw [BitVec.ofNat_add]; simp
  have he : ev s (.rstruct [.const 1,
      .load .one (.rfield 1 (.var .local (ofString "r"))),
      .load .one (.op .add [.rfield 1 (.var .local (ofString "r")), .const 8])]) =
      some (.rStruct [.val (.word 1), .val (.word code), .val (.word code_n)]) := by
    simp [ev, evalHOLExact, evalListHOLExact, hr, memLoadHOLExact,
      isWfShapeExactHOL, wordOpHOL, wordOp, valueIsWord, valueWord,
      haddr, hd0', hd8, hc', hn]
  apply Ret.ret
  intro v hv
  rw [he] at hv
  cases hv
  exact ⟨code, code_n, rfl, hlt, rfl⟩

theorem get_code_cache_record_return_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
    (found ptr : BitVec 64)
    (hwlocal : s.locals.lookup (ofString "w") =
      some (.rStruct [.val (.word found), .val (.word ptr)]))
    (hw : WordsOK s (ptr.toNat, 16)) (hb : memW s (ptr.toNat + 8) < 2 ^ 40) :
    Ret s (.return (.rstruct [
      .load .one (.rfield 1 (.var .local (ofString "w"))),
      .load .one (.op .add [.rfield 1 (.var .local (ofString "w")), .const 8])]))
      (fun v post => ∃ code code_n : BitVec 64,
        v = .rStruct [.val (.word code), .val (.word code_n)] ∧
        code_n.toNat < 2 ^ 40 ∧ post = {s with locals := post.locals, clock := post.clock}) := by
  obtain ⟨code, code_n, hc, hn, hlt⟩ := code_record_words_bounded hw hb
  have hd0 := (hw.2.2 0 (by omega)).choose_spec.1
  have hd8 := (hw.2.2 1 (by omega)).choose_spec.1
  simp only [Nat.mul_zero, Nat.add_zero] at hd0
  simp only [Nat.mul_one] at hd8
  have hc' : s.memory ptr = .word code := by simpa using hc
  have hd0' : s.memaddrs ptr := by simpa using hd0
  have haddr : ptr + 8#64 = BitVec.ofNat 64 (ptr.toNat + 8) := by
    rw [BitVec.ofNat_add]; simp
  have he : ev s (.rstruct [
      .load .one (.rfield 1 (.var .local (ofString "w"))),
      .load .one (.op .add [.rfield 1 (.var .local (ofString "w")), .const 8])]) =
      some (.rStruct [.val (.word code), .val (.word code_n)]) := by
    simp [ev, evalHOLExact, evalListHOLExact, hwlocal, memLoadHOLExact,
      isWfShapeExactHOL, wordOpHOL, wordOp, valueIsWord, valueWord,
      haddr, hd0', hd8, hc', hn]
  apply Ret.ret
  intro v hv
  rw [he] at hv
  cases hv
  exact ⟨code, code_n, rfl, hlt, rfl⟩

theorem get_code_cache_branch_return_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
    (found ptr : BitVec 64) (tail : ProgHOL 64)
    (hwlocal : s.locals.lookup (ofString "w") =
      some (.rStruct [.val (.word found), .val (.word ptr)]))
    (hrecord : found ≠ 0 → WordsOK s (ptr.toNat, 16) ∧ memW s (ptr.toNat + 8) < 2 ^ 40)
    (hmiss : found = 0 → Ret s tail (fun v _ => ∃ code code_n : BitVec 64,
      v = .rStruct [.val (.word code), .val (.word code_n)] ∧ code_n.toNat < 2 ^ 40)) :
    Ret s (.seq (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "w"))) (.const 0))
      (.return (.rstruct [
        .load .one (.rfield 1 (.var .local (ofString "w"))),
        .load .one (.op .add [.rfield 1 (.var .local (ofString "w")), .const 8])])) .skip) tail)
      (fun v _ => ∃ code code_n : BitVec 64,
        v = .rStruct [.val (.word code), .val (.word code_n)] ∧ code_n.toNat < 2 ^ 40) := by
  by_cases hz : found = 0
  · have he : ev s (.cmp .notEqual (.rfield 0 (.var .local (ofString "w"))) (.const 0)) =
        some (.val (.word 0)) := by
      simp [ev, evalHOLExact, hwlocal, hz, Compiler.Encoders.Asm.wordCmpHOL]
    have hi : evaluateHOLFiniteState s
        (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "w"))) (.const 0))
          (.return (.rstruct [
            .load .one (.rfield 1 (.var .local (ofString "w"))),
            .load .one (.op .add [.rfield 1 (.var .local (ofString "w")), .const 8])])) .skip) = (none, s) := by
      rw [evaluateHOLFiniteState_ite]
      unfold ev at he; rw [he]
      exact evaluateHOLFiniteState_skip s
    intro v hv
    rw [evaluateHOLFiniteState_seq_line780, hi] at hv
    exact hmiss hz v hv
  · have he : ev s (.cmp .notEqual (.rfield 0 (.var .local (ofString "w"))) (.const 0)) =
        some (.val (.word 1)) := by
      simp [ev, evalHOLExact, hwlocal, Compiler.Encoders.Asm.wordCmpHOL]; exact hz
    intro v hv
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hv
    unfold ev at he; rw [he] at hv
    simp only [show (1 : BitVec 64) ≠ 0 by decide, ↓reduceIte] at hv
    split at hv
    · rename_i hn
      rw [evaluateHOLFiniteState_return] at hn
      split at hn <;> simp_all
      split at hn <;> simp_all
    · obtain ⟨hw, hb⟩ := hrecord hz
      obtain ⟨code, code_n, hv', hn, _⟩ := get_code_cache_record_return_bounded s found ptr hwlocal hw hb v hv
      exact ⟨code, code_n, hv', hn⟩

end CodeBounded
end InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk
