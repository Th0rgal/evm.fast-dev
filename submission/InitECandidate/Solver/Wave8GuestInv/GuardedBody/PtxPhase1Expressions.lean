import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxPhase1Stores
import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxPhase1Steps
import InitECandidate.Solver.Wave8GuestInv.Expressions
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody.R10.Phase1
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded

open Flapjack.Compiler.Encoders.Asm
theorem evalAt_loadG' {F : Type} (t : PanSemStateFiniteExact 64 F) (g : String) (k a : BitVec 64)
    (h : evalAt t (.load .one (.op .add [.var .global (ofString g), .const k])) =
      some (.val (.word a))) :
    a.toNat = memW t (globN t g + k.toNat) := by
  simp [evalAt, evalHOLExact, evalListHOLExact] at h
  rcases hg : t.globals.lookup (ofString g) with _ | v
  · simp [hg] at h
  · rcases v with x | fs | ⟨nm, fs⟩
    · cases x with
      | word x =>
        simp [hg, valueIsWord, valueWord, wordOpHOL, wordOp, memLoadHOLExact] at h
        have hadd : BitVec.ofNat 64 (x.toNat + k.toNat) = x + k := by
          rw [BitVec.add_def]
        simp only [globN, memW, hg, hadd, h.2]
    · simp [hg, valueIsWord] at h
    · simp [hg, valueIsWord] at h

/-- A one-word load from `global + k` that succeeds yields the word `memW t (globN t g + k)`. -/
theorem evalAt_loadG {F : Type} (t : PanSemStateFiniteExact 64 F) (g : String) (k : BitVec 64)
    (v : ValueHOL 64)
    (h : evalAt t (.load .one (.op .add [.var .global (ofString g), .const k])) = some v) :
    ∃ a : BitVec 64, v = .val (.word a) ∧ a.toNat = memW t (globN t g + k.toNat) := by
  have hv : ∃ a : BitVec 64, v = .val (.word a) := by
    simp [evalAt, evalHOLExact, evalListHOLExact] at h
    rcases hg : t.globals.lookup (ofString g) with _ | w
    · simp [hg] at h
    · rcases w with x | fs | ⟨nm, fs⟩
      · cases x with
        | word x =>
          simp [hg, valueIsWord, valueWord, wordOpHOL, wordOp, memLoadHOLExact] at h
          rcases hm : t.memory (x + k) with ⟨y⟩
          exact ⟨y, by rw [← h.2, hm]⟩
      · simp [hg, valueIsWord] at h
      · simp [hg, valueIsWord] at h
  obtain ⟨a, rfl⟩ := hv
  exact ⟨a, rfl, evalAt_loadG' t g k a h⟩

theorem panMemStoresHOL_word_spec {F : Type} {s : PanSemStateFiniteExact 64 F}
    {x : BitVec 64} {w : HolWordLab 64} {mem' : BitVec 64 → HolWordLab 64}
    (hst : @panMemStoresHOL 64 _ x [w] s.memaddrs
      (fun a => Classical.propDecidable (s.memaddrs a)) s.memory = some mem') :
    s.memaddrs x ∧ mem' x = w ∧ ∀ a : BitVec 64, a ≠ x → mem' a = s.memory a := by
  unfold panMemStoresHOL panMemStoreHOL at hst
  split_ifs at hst with hdom
  · simp only [panMemStoresHOL, Option.some.injEq] at hst
    subst hst
    exact ⟨hdom, if_pos rfl, fun a hne => if_neg hne⟩

theorem Hoare.store_fall {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {dst src : ExpHOL 64}
    (h : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (x : BitVec 64) (v : ValueHOL 64)
      (mem' : BitVec 64 → HolWordLab 64),
      P s → evalAt s dst = some (.val (.word x)) → evalAt s src = some v →
      @panMemStoresHOL 64 _ x (flattenHOL v) s.memaddrs
        (fun a => Classical.propDecidable (s.memaddrs a)) s.memory = some mem' →
      Q { s with memory := mem' }) :
    Hoare P (.store dst src) (fun r t => r = none → Q t) := by
  refine ⟨fun {F} s _ hP _ hr => ?_⟩
  rw [evaluateHOLFiniteState_store] at hr ⊢
  revert hr
  split
  · rename_i x hx
    split
    · rename_i v hv
      rcases hm : @panMemStoresHOL 64 _ x (flattenHOL v) s.memaddrs
          (fun a => Classical.propDecidable (s.memaddrs a)) s.memory with _ | mem'
      · simp
      · intro _
        exact h s x v mem' hP hx hv hm
    · simp
  · simp

def encDst (off : Bool) : ExpHOL 64 :=
  .op .add ([.load .one (.op .add [.var .global (ofString "bo"), .const 24]),
    .panop .mul [.var .local (ofString "index"), .const 16]] ++ if off then [.const 8] else [])

theorem encDst0_inside {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : TxReadyStrong s) {x : BitVec 64}
    (hx : evalAt s (encDst false) = some (.val (.word x))) :
    Inside (x.toNat, 8) (encArray s).1 ((encArray s).1 + (encArray s).2) := by
  have hE := txEnv_of_ready h
  obtain ⟨S, Nd, hW, _⟩ := h.2.2.2.2.2
  have hhi := (ivl_allocated_bound h.1.1.1.2 (encArray_words hW.2.2.1 hE).1).2
  dsimp only [encArray] at hhi ⊢
  change evalAt s (.op .add
    [.load .one (.op .add [.var .global (ofString "bo"), .const 24]),
      .panop .mul [.var .local (ofString "index"), .const 16]]) = _ at hx
  rcases hld : evalAt s (.load .one (.op .add [.var .global (ofString "bo"), .const 24])) with _ | vbase
  · simp only [evalAt, evalHOLExact, evalListHOLExact] at hx hld
    rw [hld] at hx; simp at hx
  obtain ⟨abase, rfl, habase_nat⟩ := evalAt_loadG s "bo" 24 vbase hld
  have habase : abase.toNat = memW s (globN s "bo" + 24) := habase_nat
  simp only [evalAt, evalHOLExact, evalListHOLExact] at hx hld
  rw [hld] at hx
  rcases hidx_v : s.locals.lookup (ofString "index") with _ | vidx
  · simp [hidx_v] at hx
  rcases vidx with widx | _ | _
  · cases widx with
    | word idx_bv =>
      simp only [hidx_v, valueIsWord, valueWord, List.all, List.map, Option.map, Bool.and_self,
        ↓reduceIte, panOpHOL, wordOpHOL, wordOp, List.foldr, Option.some.injEq,
        ValueHOL.val.injEq, HolWordLab.word.injEq] at hx
      have hidx_nat : locN s "index" = idx_bv.toNat := by simp [locN, hidx_v]
      have hidx_lt : idx_bv.toNat < memW s (globN s "bo" + 80) := hidx_nat ▸ hE.idx_lt
      have hx' : x = abase + (idx_bv * 16#64 + 0) := hx.symm
      have hx_nat : x.toNat = abase.toNat + idx_bv.toNat * 16 := by
        rw [hx']
        simp only [BitVec.toNat_add, BitVec.toNat_mul]
        have hz0 : (0 : BitVec 64).toNat = 0 := by decide
        rw [hz0]
        norm_num only [BitVec.toNat_ofNat] at *
        omega
      unfold Inside
      dsimp only
      omega
  · simp [hidx_v, valueIsWord] at hx
  · simp [hidx_v, valueIsWord] at hx

theorem encDst8_inside {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : TxReadyStrong s) {x : BitVec 64}
    (hx : evalAt s (encDst true) = some (.val (.word x))) :
    Inside (x.toNat, 8) (encArray s).1 ((encArray s).1 + (encArray s).2) := by
  have hE := txEnv_of_ready h
  obtain ⟨S, Nd, hW, _⟩ := h.2.2.2.2.2
  have hhi := (ivl_allocated_bound h.1.1.1.2 (encArray_words hW.2.2.1 hE).1).2
  dsimp only [encArray] at hhi ⊢
  change evalAt s (.op .add
    [.load .one (.op .add [.var .global (ofString "bo"), .const 24]),
      .panop .mul [.var .local (ofString "index"), .const 16], .const 8]) = _ at hx
  rcases hld : evalAt s (.load .one (.op .add [.var .global (ofString "bo"), .const 24])) with _ | vbase
  · simp only [evalAt, evalHOLExact, evalListHOLExact] at hx hld
    rw [hld] at hx; simp at hx
  obtain ⟨abase, rfl, habase_nat⟩ := evalAt_loadG s "bo" 24 vbase hld
  have habase : abase.toNat = memW s (globN s "bo" + 24) := habase_nat
  simp only [evalAt, evalHOLExact, evalListHOLExact] at hx hld
  rw [hld] at hx
  rcases hidx_v : s.locals.lookup (ofString "index") with _ | vidx
  · simp [hidx_v] at hx
  rcases vidx with widx | _ | _
  · cases widx with
    | word idx_bv =>
      simp only [hidx_v, valueIsWord, valueWord, List.all, List.map, Option.map, Bool.and_self,
        ↓reduceIte, panOpHOL, wordOpHOL, wordOp, List.foldr, Option.some.injEq,
        ValueHOL.val.injEq, HolWordLab.word.injEq] at hx
      have hidx_nat : locN s "index" = idx_bv.toNat := by simp [locN, hidx_v]
      have hidx_lt : idx_bv.toNat < memW s (globN s "bo" + 80) := hidx_nat ▸ hE.idx_lt
      have hx' : x = abase + (idx_bv * 16#64 + (8#64 + 0)) := hx.symm
      have hx_nat : x.toNat = abase.toNat + idx_bv.toNat * 16 + 8 := by
        rw [hx']
        simp only [BitVec.toNat_add, BitVec.toNat_mul]
        have hz0 : (0 : BitVec 64).toNat = 0 := by decide
        rw [hz0]
        norm_num only [BitVec.toNat_ofNat] at *
        omega
      unfold Inside
      dsimp only
      omega
  · simp [hidx_v, valueIsWord] at hx
  · simp [hidx_v, valueIsWord] at hx

def EncReady {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  TxReadyStrong s ∧ ∃ a b : BitVec 64,
    s.locals.lookup (ofString "enc") = some (.rStruct [.val (.word a), .val (.word b)])

theorem store_encSlot (off : Bool) :
    Hoare EncReady (.store (encDst off) (.rfield (if off then 1 else 0) (.var .local (ofString "enc"))))
      (fun r t => r = none → EncReady t) := by
  refine Hoare.store_fall fun s x v mem' h hx hv hst => ?_
  obtain ⟨a, b, he⟩ := h.2
  have hvw : ∃ w : HolWordLab 64, v = .val w := by
    cases off <;> simp [evalAt, evalHOLExact, he] at hv <;> subst v
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  obtain ⟨w, rfl⟩ := hvw
  obtain ⟨hdom, _, hmem⟩ := panMemStoresHOL_word_spec (by simpa only [flattenHOL] using hst)
  have hin : Inside (x.toNat, 8) (encArray s).1 ((encArray s).1 + (encArray s).2) := by
    cases off
    · exact encDst0_inside h.1 hx
    · exact encDst8_inside h.1 hx
  exact ⟨txReadyStrong_store_encArray h.1 hdom hin hmem, a, b, he⟩

end InitECandidate.Solver.Wave8GuestInv.GuardedBody.R10.Phase1
