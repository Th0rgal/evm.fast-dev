import InitECandidate.Solver.Wave8GuestInv.Deliveries.M23.Common

/-! `iz_node_invalidate`: `node_invalidate(nd)` zeroes `nd+8`, `nd+16`, `nd+24` and changes
nothing else (globals, other memory, endianness, domains).
Checked against frozen spec revision 9 (`8a79d9f28`, tag `wave8-spec-frozen-r9`). -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace InitECandidate.Solver.Wave8Contracts.M23

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

def NodeArgs (names : List String)
    (req : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Nat → Prop) :
    ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ArenaReady s ∧ ∃ Nd, NodeHeap s Nd ∧ (∀ n ∈ names, RootIn Nd (locN s n)) ∧ req s Nd

def InvalidatesCache (fname : MlS) : Prop :=
  FunSpec (NodeArgs ["nd"] (fun _ _ => True)) (fun s r post => Resumes r →
    post = { s with
      memory := fun a => if a = BitVec.ofNat 64 (locN s "nd" + 8) ∨ a = BitVec.ofNat 64 (locN s "nd" + 16) ∨
          a = BitVec.ofNat 64 (locN s "nd" + 24) then HolWordLab.word 0 else s.memory a,
      locals := post.locals, clock := post.clock }) fname

private theorem lookup_node_invalidate :
    originalRuntimeCode.lookup (ofString "node_invalidate") =
      some ([(ofString "nd", .one)], sourceFnBody Guest.Software.guestFn_node_invalidate, .one) :=
  lookup_of_guestAst_getElem 259 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_node_invalidate) rfl

private theorem not_resumes_error : ¬ Resumes (some (.error : PanSemResultExact 64)) := by
  rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> cases h

private theorem eval_store_const_zero {F : Type} (s : PanSemStateFiniteExact 64 F)
    (nd : BitVec 64) (hnd : s.locals.lookup (ofString "nd") = some (.val (.word nd)))
    (off : BitVec 64) :
    (evaluateHOLFiniteState s (.store (.op .add [.var .local (ofString "nd"), .const off]) (.const 0)) =
      (some .error, s)) ∨
    (evaluateHOLFiniteState s (.store (.op .add [.var .local (ofString "nd"), .const off]) (.const 0)) =
      (none, { s with memory := fun a => if a = nd + off then .word 0 else s.memory a })) := by
  rw [evaluateHOLFiniteState_store]
  have hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .local (ofString "nd"), .const off]) = some (.val (.word (nd + off))) := by
    simp [evalHOLExact, evalListHOLExact, hnd, valueIsWord, valueWord, wordOpHOL, wordOp]
  have hsrc : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.const 0) = some (.val (.word 0)) := rfl
  rw [hdst, hsrc]
  simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL]
  by_cases hdom : s.memaddrs (nd + off)
  · simp [hdom]
  · simp [hdom]

private theorem ofNat_add_toNat_eq (nd : BitVec 64) (k : Nat) :
    BitVec.ofNat 64 (nd.toNat + k) = nd + BitVec.ofNat 64 k := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, BitVec.toNat_ofNat]

/-- `node_invalidate` (AST line 10061): zeroes the cache words `nd+8/+16/+24` and nothing else. -/
theorem «iz_node_invalidate» : InvalidatesCache (ofString "node_invalidate") := by
  refine ⟨_, _, _, lookup_node_invalidate, ?_⟩
  intro F s _hcode _hP _hlookup _hnt hres
  have hb : sourceFnBody Guest.Software.guestFn_node_invalidate =
      .seq (.store (.op .add [.var .local (ofString "nd"), .const 8]) (.const 0))
        (.seq (.store (.op .add [.var .local (ofString "nd"), .const 16]) (.const 0))
          (.seq (.store (.op .add [.var .local (ofString "nd"), .const 24]) (.const 0))
            (.return (.const 0)))) := rfl
  rw [hb] at hres ⊢
  rcases hnd : s.locals.lookup (ofString "nd") with _ | vnd
  · rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_store] at hres
    simp [evalHOLExact, evalListHOLExact, hnd] at hres
    exact absurd hres not_resumes_error
  · rcases vnd with ⟨⟨nd⟩⟩ | fs | ⟨nm, fs⟩
    · have hloc : locN s "nd" = nd.toNat := by simp [locN, hnd]
      rw [evaluateHOLFiniteState_seq_line780] at hres ⊢
      rcases eval_store_const_zero s nd hnd 8 with h1 | h1
      · rw [h1] at hres; exact absurd hres not_resumes_error
      · rw [h1] at hres ⊢
        dsimp only at hres ⊢
        set s1 : PanSemStateFiniteExact 64 F :=
          { s with memory := fun a => if a = nd + 8 then .word 0 else s.memory a }
        rw [evaluateHOLFiniteState_seq_line780] at hres ⊢
        rcases eval_store_const_zero s1 nd (by simp [s1, hnd]) 16 with h2 | h2
        · rw [h2] at hres; exact absurd hres not_resumes_error
        · rw [h2] at hres ⊢
          dsimp only at hres ⊢
          set s2 : PanSemStateFiniteExact 64 F :=
            { s1 with memory := fun a => if a = nd + 16 then .word 0 else s1.memory a }
          rw [evaluateHOLFiniteState_seq_line780] at hres ⊢
          rcases eval_store_const_zero s2 nd (by simp [s2, s1, hnd]) 24 with h3 | h3
          · rw [h3] at hres; exact absurd hres not_resumes_error
          · rw [h3] at hres ⊢
            dsimp only at hres ⊢
            set s3 : PanSemStateFiniteExact 64 F :=
              { s2 with memory := fun a => if a = nd + 24 then .word 0 else s2.memory a }
            rw [evaluateHOLFiniteState_return]
            have hret : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
                (.const 0) = some (.val (.word 0)) := rfl
            rw [hret]
            have hmem : (fun a : BitVec 64 =>
                if a = nd + 24 then HolWordLab.word 0
                else if a = nd + 16 then HolWordLab.word 0
                else if a = nd + 8 then HolWordLab.word 0
                else s.memory a) =
              (fun a : BitVec 64 =>
                if a = nd + 8#64 ∨ a = nd + 16#64 ∨ a = nd + 24#64 then HolWordLab.word 0
                else s.memory a) := by
              funext a
              change (if a = nd + 24#64 then HolWordLab.word 0
                else if a = nd + 16#64 then HolWordLab.word 0
                else if a = nd + 8#64 then HolWordLab.word 0
                else s.memory a) = _
              by_cases c24 : a = nd + 24#64
              · simp [c24]
              · by_cases c16 : a = nd + 16#64
                · simp [c24, c16]
                · by_cases c8 : a = nd + 8#64
                  · simp [c24, c16, c8]
                  · simp [c24, c16, c8]
            have hsz : sizeOfShapeWithContextHOL s.structs (shapeOfHOLExact (ValueHOL.val (HolWordLab.word (0 : BitVec 64)))) ≤ 32 := by
              simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
            dsimp only [s3, s2, s1]
            rw [if_pos hsz, hloc, ofNat_add_toNat_eq nd 8, ofNat_add_toNat_eq nd 16, ofNat_add_toNat_eq nd 24]
            dsimp only [emptyLocalsHOLFinite]
            rw [hmem]
    · rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_store] at hres
      simp [evalHOLExact, evalListHOLExact, hnd, valueIsWord] at hres
      exact absurd hres not_resumes_error
    · rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_store] at hres
      simp [evalHOLExact, evalListHOLExact, hnd, valueIsWord] at hres
      exact absurd hres not_resumes_error

end InitECandidate.Solver.Wave8Contracts.M23
