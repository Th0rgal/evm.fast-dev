import InitECandidate.Solver.Wave8GuestInv.MemoryViews
import InitECandidate.Solver.HeapPotential
import Guest.SoftwareAst

/-! Shared definitions and allocator/memory lemmas for contract micro-shard `m26`
(`wave8/contracts-m26`), checked against frozen revision 9 (`8a79d9f28`, tag `wave8-spec-frozen-r9`).

Imports only the light split module `InitECandidate.Solver.Wave8GuestInv.MemoryViews`,
`InitECandidate.Solver.HeapPotential`, and `Guest.SoftwareAst`.
Restates `FunSpec`, `RetWord`, `Returns`, `FreshBlock`, and `FreshScratch` verbatim from
`campaign/specs-proposed/GuestInv.lean` @ `8a79d9f28` so every proved theorem in `m26` is
definitionally (`rfl`) equal to its spec statement in `Axioms.lean`.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8Contracts.M26

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

/-! ## 1. Verbatim contract definitions from frozen rev9 `GuestInv.lean` (`8a79d9f28`) -/

def FunSpec (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → Prop)
    (fname : MlS) : Prop :=
  ∃ (params : List (MlS × ShapeHOL)) (body : ProgHOL 64) (retShape : ShapeHOL),
    originalRuntimeCode.lookup fname = some (params, body, retShape) ∧
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode → P s →
      (∃ values, lookupCodeHOLFinite originalRuntimeCode.lookup fname values =
        some (body, s.locals, retShape)) →
      (evaluateHOLFiniteState s body).1 ≠ some .timeOut →
      Q s (evaluateHOLFiniteState s body).1 (evaluateHOLFiniteState s body).2

def FreshBlock {F : Type} (s post : PanSemStateFiniteExact 64 F) (p n : Nat) : Prop :=
  p % 8 = 0 ∧ Inside (p, (n + 7) / 8 * 8) (globN s "heap_ptr") (globN post "heap_ptr") ∧
    WordsOK post (p, (n + 7) / 8 * 8)

def RetWord (Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F → Nat →
    Prop) : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → Prop :=
  fun s r post => ∀ v, r = some (.returned v) → ∃ w : BitVec 64, v = .val (.word w) ∧ Q s post w.toNat

def Returns (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F → Nat → Prop)
    (fname : MlS) : Prop :=
  FunSpec P (RetWord (fun s post p => ArenaReady post ∧ AllocatorGrows s post ∧ Q s post p)) fname

def FreshScratch {F : Type} (s post : PanSemStateFiniteExact 64 F) (p n : Nat) : Prop :=
  p % 8 = 0 ∧ globN s "frame_mem_ptr" ≤ p ∧
    Inside (p, (n + 7) / 8 * 8) (globN post "scratch_ptr") (globN s "scratch_ptr") ∧
    WordsOK post (p, (n + 7) / 8 * 8)

/-! ## 2. Ordinary domain and `WordsOK` helpers -/

theorem addresses_iff (b : BitVec 64) (n : Nat) (x : BitVec 64) :
    Flapjack.Compiler.Backend.StackRemove.addresses b n x ↔
      ∃ i, i < n ∧ x = b + BitVec.ofNat 64 (8 * i) := by
  induction n generalizing b with
  | zero => simp [Flapjack.Compiler.Backend.StackRemove.addresses]
  | succ n ih =>
    simp only [Flapjack.Compiler.Backend.StackRemove.addresses,
      Flapjack.Compiler.Backend.StackRemove.bytesInWord]
    rw [ih]
    constructor
    · rintro (rfl | ⟨i, hi, rfl⟩)
      · exact ⟨0, by omega, by simp⟩
      · refine ⟨i + 1, by omega, ?_⟩
        rw [BitVec.add_assoc]
        congr 1
        apply BitVec.eq_of_toNat_eq
        simp [BitVec.toNat_add]
        omega
    · rintro ⟨i, hi, rfl⟩
      rcases i with _ | i
      · left; simp
      · right
        refine ⟨i, by omega, ?_⟩
        rw [BitVec.add_assoc]
        congr 1
        apply BitVec.eq_of_toNat_eq
        simp [BitVec.toNat_add]
        omega

theorem ordinaryDomain_eq : ordinaryDomain =
    Flapjack.Compiler.Backend.StackRemove.addresses (BitVec.ofNat 64 2701131776) 3888119741 := by
  have h1 : (BitVec.ofNat 64 sourceBase) = BitVec.ofNat 64 2701131776 := rfl
  have h2 : (stackStart - sourceBase) / 8 - globalsWords = 3888119741 := by decide
  unfold ordinaryDomain
  rw [h1, h2]

theorem addresses_iff_nat (b : BitVec 64) (n : Nat) (hb : b.toNat + 8 * n ≤ 2 ^ 64)
    (x : BitVec 64) :
    Flapjack.Compiler.Backend.StackRemove.addresses b n x ↔
      b.toNat ≤ x.toNat ∧ x.toNat < b.toNat + 8 * n ∧ (x.toNat - b.toNat) % 8 = 0 := by
  rw [addresses_iff]
  constructor
  · rintro ⟨i, hi, rfl⟩
    have : (b + BitVec.ofNat 64 (8 * i)).toNat = b.toNat + 8 * i := by
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    rw [this]
    omega
  · rintro ⟨h1, h2, h3⟩
    refine ⟨(x.toNat - b.toNat) / 8, by omega, ?_⟩
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega

theorem ordinaryDomain_iff (x : BitVec 64) :
    ordinaryDomain x ↔ sourceBase ≤ x.toNat ∧ x.toNat < heapEnd ∧ x.toNat % 8 = 0 := by
  have hb : (BitVec.ofNat 64 2701131776).toNat = 2701131776 := rfl
  have hsb : sourceBase = 2701131776 := by decide
  have hhe : heapEnd = 2701131776 + 8 * 3888119741 := by decide
  rw [ordinaryDomain_eq, addresses_iff_nat _ _ (by rw [hb]; norm_num), hb, hsb, hhe]
  omega

theorem ordinaryDomain_of_nat (a : Nat) (hlo : sourceBase ≤ a) (hhi : a < heapEnd)
    (hal : a % 8 = 0) : ordinaryDomain (BitVec.ofNat 64 a) := by
  have hlt : a < 2 ^ 64 := by
    have : heapEnd < 2 ^ 64 := by decide
    omega
  have hbv : (BitVec.ofNat 64 a).toNat = a := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  rw [ordinaryDomain_iff, hbv]
  exact ⟨hlo, hhi, hal⟩

theorem wordsOK_of_guestInv {F : Type} (s : PanSemStateFiniteExact 64 F) (hG : GuestInv s)
    (p len : Nat) (hp : p % 8 = 0) (hlen : len % 8 = 0)
    (hlo : sourceBase ≤ p) (hhi : p + len ≤ heapEnd) :
    WordsOK s (p, len) := by
  refine ⟨hp, hlen, ?_⟩
  intro k hk
  rcases hmem : s.memory (BitVec.ofNat 64 (p + 8 * k)) with ⟨w⟩
  refine ⟨w, ?_, hmem⟩
  rw [hG.memaddrs]
  exact ordinaryDomain_of_nat (p + 8 * k) (by omega) (by omega) (by omega)

theorem globWord_of_pos {F : Type} (s : PanSemStateFiniteExact 64 F) (name : String)
    (hpos : 0 < globN s name) :
    ∃ w : BitVec 64, s.globals.lookup (ofString name) = some (.val (.word w)) ∧
      w.toNat = globN s name := by
  unfold globN at hpos ⊢
  rcases hg : s.globals.lookup (ofString name) with _ | v
  · simp [hg] at hpos
  · rcases v with ⟨⟨w⟩⟩ | _ | _
    · exact ⟨w, rfl, by simp [hg]⟩
    · simp [hg] at hpos
    · simp [hg] at hpos

theorem arenaOK_globals {F : Type} (s : PanSemStateFiniteExact 64 F) (hA : ArenaOK s) :
    ∃ hp fp sp : BitVec 64,
      s.globals.lookup (ofString "heap_ptr") = some (.val (.word hp)) ∧
      hp.toNat = globN s "heap_ptr" ∧
      s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word fp)) ∧
      fp.toNat = globN s "frame_mem_ptr" ∧
      s.globals.lookup (ofString "scratch_ptr") = some (.val (.word sp)) ∧
      sp.toNat = globN s "scratch_ptr" := by
  have hsb : 0 < sourceBase := by decide
  have hss : 0 < scratchStart := by decide
  obtain ⟨hp, hhp, hhp_eq⟩ := globWord_of_pos s "heap_ptr" (by have := hA.1; omega)
  obtain ⟨fp, hfp, hfp_eq⟩ := globWord_of_pos s "frame_mem_ptr" (by have := hA.2.2.1; omega)
  obtain ⟨sp, hsp, hsp_eq⟩ := globWord_of_pos s "scratch_ptr"
    (by have := hA.2.2.1; have := hA.2.2.2.1; omega)
  exact ⟨hp, fp, sp, hhp, hhp_eq, hfp, hfp_eq, hsp, hsp_eq⟩

/-! ## 3. Exact body semantics for `alloc` and `scratch_alloc` -/

theorem alloc_body_run {F : Type}
    (state : PanSemStateFiniteExact 64 F) (p n : BitVec 64)
    (hcode : state.code = originalRuntimeCode)
    (hp_lookup : state.globals.lookup (ofString "heap_ptr") = some (.val (.word p)))
    (hn : state.locals.lookup (ofString "n") = some (.val (.word n))) :
    let out := evaluateHOLFiniteState state (sourceFnBody Guest.Software.guestFn_alloc)
    let q := (p + (n + 7)) &&& ((0 : BitVec 64) - 8)
    ∀ retVal : ValueHOL 64, out.1 = some (.returned retVal) →
      retVal = .val (.word p) ∧ ¬ ((cMax - p).toNat < n.toNat) ∧ ¬ (cMax.toNat < q.toNat) ∧
      out.2 = { state with
        globals := (state.globals.update (ofString "heap_ptr", .val (.word q)))
        locals := out.2.locals } := by
  dsimp only
  have hbody_eq : sourceFnBody Guest.Software.guestFn_alloc =
      .dec (ofString "p") .one (.var .global (ofString "heap_ptr"))
        (.seq
          (.ite (.cmp .lower (.op .sub [.const cMax, .var .local (ofString "p")])
              (.var .local (ofString "n")))
            (.call (some (none, none)) (ofString "trap_with") [.const 1])
            .skip)
          (.dec (ofString "q") .one
            (.op .and [.op .add [.var .local (ofString "p"), .var .local (ofString "n"), .const 7],
              .op .sub [.const 0, .const 8]])
            (.seq
              (.ite (.cmp .lower (.const cMax) (.var .local (ofString "q")))
                (.call (some (none, none)) (ofString "trap_with") [.const 1])
                .skip)
              (.seq
                (.assign .global (ofString "heap_ptr") (.var .local (ofString "q")))
                (.return (.var .local (ofString "p"))))))) := rfl
  rw [hbody_eq, evaluateHOLFiniteState_dec_total]
  have hp_eval : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a))
      (.var .global (ofString "heap_ptr")) = some (.val (.word p)) := hp_lookup
  dsimp only
  rw [hp_eval]
  have hsh_p : shapeEqHOL .one (shapeOfHOLExact (.val (.word p))) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  dsimp only
  rw [if_pos hsh_p]
  dsimp only
  let pState := setVarHOLFinite (ofString "p") (.val (.word p)) state
  have hp_loc : pState.locals.lookup (ofString "p") = some (.val (.word p)) := by
    simp [pState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hn_loc : pState.locals.lookup (ofString "n") = some (.val (.word n)) := by
    simp [pState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn,
      show ofString "p" ≠ ofString "n" by decide]
  have hcode_p : pState.code = originalRuntimeCode := hcode
  rw [evaluateHOLFiniteState_seq_line780]
  have hev1 : @evalHOLExact 64 F _ pState.toExact
      (fun a => Classical.propDecidable (pState.memaddrs a))
      (.cmp .lower (.op .sub [.const cMax, .var .local (ofString "p")])
        (.var .local (ofString "n"))) =
      some (.val (.word (if (cMax - p).toNat < n.toNat then 1 else 0))) := by
    simp only [evalHOLExact, evalListHOLExact, hp_loc, hn_loc,
      Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, decide_eq_true_eq]
    rfl
  by_cases hcmp1 : (cMax - p).toNat < n.toNat
  · have hite1 : evaluateHOLFiniteState pState
        (.ite (.cmp .lower (.op .sub [.const cMax, .var .local (ofString "p")])
            (.var .local (ofString "n")))
          (.call (some (none, none)) (ofString "trap_with") [.const 1])
          .skip) =
        evaluateHOLFiniteState pState (.call (some (none, none)) (ofString "trap_with") [.const 1]) := by
      rw [evaluateHOLFiniteState_ite, hev1, if_pos hcmp1]; simp
    rw [hite1]
    have hno_none := evaluate_call_trap_with_no_none pState 1 hcode_p
    have hno_ret := fun w => evaluate_call_trap_with_no_return pState 1 w hcode_p
    rcases htr : evaluateHOLFiniteState pState (.call (some (none, none)) (ofString "trap_with") [.const 1]) with ⟨r1, s1⟩
    rw [htr] at hno_none hno_ret
    cases r1 with
    | none => exact absurd rfl hno_none
    | some r1' =>
      intro retVal hret
      exact False.elim (hno_ret retVal hret)
  · have hite1 : evaluateHOLFiniteState pState
        (.ite (.cmp .lower (.op .sub [.const cMax, .var .local (ofString "p")])
            (.var .local (ofString "n")))
          (.call (some (none, none)) (ofString "trap_with") [.const 1])
          .skip) = (none, pState) := by
      rw [evaluateHOLFiniteState_ite, hev1, if_neg hcmp1]; simp [evaluateHOLFiniteState_skip]
    rw [hite1]
    dsimp only
    rw [evaluateHOLFiniteState_dec_total]
    let q : BitVec 64 := (p + (n + 7)) &&& ((0 : BitVec 64) - 8)
    have hq_eval : @evalHOLExact 64 F _ pState.toExact
        (fun a => Classical.propDecidable (pState.memaddrs a))
        (.op .and [.op .add [.var .local (ofString "p"), .var .local (ofString "n"), .const 7],
          .op .sub [.const 0, .const 8]]) = some (.val (.word q)) := by
      simp only [evalHOLExact, evalListHOLExact, hp_loc, hn_loc,
        wordOpHOL, wordOp, valueIsWord, valueWord, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr]
      exact congrArg (fun w => some (ValueHOL.val (HolWordLab.word w))) (alloc_q_word_eq p n)
    dsimp only
    rw [hq_eval]
    have hsh_q : shapeEqHOL .one (shapeOfHOLExact (.val (.word q))) = true := by
      simp [shapeEqHOL, shapeOfHOLExact]
    dsimp only
    rw [if_pos hsh_q]
    dsimp only
    let qState := setVarHOLFinite (ofString "q") (.val (.word q)) pState
    have hq_loc : qState.locals.lookup (ofString "q") = some (.val (.word q)) := by
      simp [qState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hp_loc_q : qState.locals.lookup (ofString "p") = some (.val (.word p)) := by
      simp [qState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hp_loc,
        show ofString "q" ≠ ofString "p" by decide]
    have hcode_q : qState.code = originalRuntimeCode := hcode
    rw [evaluateHOLFiniteState_seq_line780]
    have hev2 : @evalHOLExact 64 F _ qState.toExact
        (fun a => Classical.propDecidable (qState.memaddrs a))
        (.cmp .lower (.const cMax) (.var .local (ofString "q"))) =
        some (.val (.word (if cMax.toNat < q.toNat then 1 else 0))) := by
      simp only [evalHOLExact, hq_loc, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, decide_eq_true_eq]
    by_cases hcmp2 : cMax.toNat < q.toNat
    · have hite2 : evaluateHOLFiniteState qState
          (.ite (.cmp .lower (.const cMax) (.var .local (ofString "q")))
            (.call (some (none, none)) (ofString "trap_with") [.const 1])
            .skip) =
          evaluateHOLFiniteState qState (.call (some (none, none)) (ofString "trap_with") [.const 1]) := by
        rw [evaluateHOLFiniteState_ite, hev2, if_pos hcmp2]; simp
      rw [hite2]
      have hno_none := evaluate_call_trap_with_no_none qState 1 hcode_q
      have hno_ret := fun w => evaluate_call_trap_with_no_return qState 1 w hcode_q
      rcases htr : evaluateHOLFiniteState qState (.call (some (none, none)) (ofString "trap_with") [.const 1]) with ⟨r2, s2⟩
      rw [htr] at hno_none hno_ret
      cases r2 with
      | none => exact absurd rfl hno_none
      | some r2' =>
        intro retVal hret
        exact False.elim (hno_ret retVal hret)
    · have hite2 : evaluateHOLFiniteState qState
          (.ite (.cmp .lower (.const cMax) (.var .local (ofString "q")))
            (.call (some (none, none)) (ofString "trap_with") [.const 1])
            .skip) = (none, qState) := by
        rw [evaluateHOLFiniteState_ite, hev2, if_neg hcmp2]; simp [evaluateHOLFiniteState_skip]
      rw [hite2]
      dsimp only
      have hp_g : qState.globals.lookup (ofString "heap_ptr") = some (.val (.word p)) := hp_lookup
      have heval_end : evaluateHOLFiniteState qState
          (.seq (.assign .global (ofString "heap_ptr") (.var .local (ofString "q")))
            (.return (.var .local (ofString "p")))) =
          (some (.returned (.val (.word p))),
            emptyLocalsHOLFinite (setGlobalHOLFinite (ofString "heap_ptr") (.val (.word q)) qState)) := by
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
        simp [evalHOLExact, hq_loc, hp_loc_q, isValidValueHOLExact, lookupKvarHOLExact, hp_g,
          shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite, setGlobalHOLFinite,
          evaluateHOLFiniteState_return, sizeOfShapeWithContextHOL]
      rw [heval_end]
      intro retVal hret
      injection hret with hr
      injection hr with hr'
      exact ⟨hr'.symm, hcmp1, hcmp2, rfl⟩

theorem alloc_arith (p n : BitVec 64)
    (hp_hi : p.toNat ≤ heapLimit) (hp_al : p.toNat % 8 = 0)
    (hcmp1 : ¬ ((cMax - p).toNat < n.toNat))
    (hcmp2 : ¬ (cMax.toNat < ((p + (n + 7)) &&& ((0 : BitVec 64) - 8)).toNat)) :
    let q := (p + (n + 7)) &&& ((0 : BitVec 64) - 8)
    q.toNat = p.toNat + (n.toNat + 7) / 8 * 8 ∧
    q.toNat ≤ heapLimit ∧ q.toNat % 8 = 0 ∧ p.toNat ≤ q.toNat := by
  intro q
  have hcMax : cMax.toNat = 2952790016 := rfl
  have hlim : heapLimit = 2952790016 := by decide
  have hsub : (cMax - p).toNat = 2952790016 - p.toNat := by
    rw [BitVec.toNat_sub]; omega
  have hn_le : n.toNat ≤ 2952790016 - p.toNat := by omega
  have h7 : (7 : BitVec 64).toNat = 7 := rfl
  have hn7 : (n + 7).toNat = n.toNat + 7 := by
    rw [BitVec.toNat_add, h7]; omega
  have hsum : (p + (n + 7)).toNat = p.toNat + n.toNat + 7 := by
    rw [BitVec.toNat_add, hn7]; omega
  have hq_nat : q.toNat = (p + (n + 7)).toNat / 8 * 8 := and_neg8_toNat (p + (n + 7))
  rw [hsum] at hq_nat
  have hq_le : q.toNat ≤ cMax.toNat := Nat.le_of_not_lt hcmp2
  exact ⟨by omega, by omega, by omega, by omega⟩

theorem scratch_alloc_body_run {F : Type}
    (state : PanSemStateFiniteExact 64 F) (p f n : BitVec 64)
    (hcode : state.code = originalRuntimeCode)
    (hp_lookup : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word p)))
    (hf_lookup : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word f)))
    (hn : state.locals.lookup (ofString "n") = some (.val (.word n))) :
    let out := evaluateHOLFiniteState state (sourceFnBody Guest.Software.guestFn_scratch_alloc)
    let q := (p - n) &&& ((0 : BitVec 64) - 8)
    ∀ retVal : ValueHOL 64, out.1 = some (.returned retVal) →
      retVal = .val (.word q) ∧ ¬ ((p - f).toNat < n.toNat) ∧ ¬ (q.toNat < f.toNat) ∧
      out.2 = { state with
        globals := (state.globals.update (ofString "scratch_ptr", .val (.word q)))
        locals := out.2.locals } := by
  dsimp only
  have hbody_eq : sourceFnBody Guest.Software.guestFn_scratch_alloc =
      .dec (ofString "p") .one (.var .global (ofString "scratch_ptr"))
        (.seq
          (.ite (.cmp .lower (.op .sub [.var .local (ofString "p"), .var .global (ofString "frame_mem_ptr")])
              (.var .local (ofString "n")))
            (.call (some (none, none)) (ofString "trap_with") [.const 7])
            .skip)
          (.dec (ofString "q") .one
            (.op .and [.op .sub [.var .local (ofString "p"), .var .local (ofString "n")],
              .op .sub [.const 0, .const 8]])
            (.seq
              (.ite (.cmp .lower (.var .local (ofString "q")) (.var .global (ofString "frame_mem_ptr")))
                (.call (some (none, none)) (ofString "trap_with") [.const 7])
                .skip)
              (.seq
                (.assign .global (ofString "scratch_ptr") (.var .local (ofString "q")))
                (.return (.var .local (ofString "q"))))))) := rfl
  rw [hbody_eq, evaluateHOLFiniteState_dec_total]
  have hp_eval : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a))
      (.var .global (ofString "scratch_ptr")) = some (.val (.word p)) := hp_lookup
  dsimp only
  rw [hp_eval]
  have hsh_p : shapeEqHOL .one (shapeOfHOLExact (.val (.word p))) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  dsimp only
  rw [if_pos hsh_p]
  dsimp only
  let pState := setVarHOLFinite (ofString "p") (.val (.word p)) state
  have hp_loc : pState.locals.lookup (ofString "p") = some (.val (.word p)) := by
    simp [pState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hn_loc : pState.locals.lookup (ofString "n") = some (.val (.word n)) := by
    simp [pState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn,
      show ofString "p" ≠ ofString "n" by decide]
  have hcode_p : pState.code = originalRuntimeCode := hcode
  rw [evaluateHOLFiniteState_seq_line780]
  have hev1 : @evalHOLExact 64 F _ pState.toExact
      (fun a => Classical.propDecidable (pState.memaddrs a))
      (.cmp .lower (.op .sub [.var .local (ofString "p"), .var .global (ofString "frame_mem_ptr")])
        (.var .local (ofString "n"))) =
      some (.val (.word (if (p - f).toNat < n.toNat then 1 else 0))) := by
    have hf_g : pState.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word f)) :=
      hf_lookup
    simp only [evalHOLExact, evalListHOLExact, hp_loc, hn_loc, hf_g,
      Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, decide_eq_true_eq]
    simp [wordOpHOL, wordOp, valueIsWord, valueWord]
  by_cases hcmp1 : (p - f).toNat < n.toNat
  · have hite1 : evaluateHOLFiniteState pState
        (.ite (.cmp .lower (.op .sub [.var .local (ofString "p"), .var .global (ofString "frame_mem_ptr")])
            (.var .local (ofString "n")))
          (.call (some (none, none)) (ofString "trap_with") [.const 7])
          .skip) =
        evaluateHOLFiniteState pState (.call (some (none, none)) (ofString "trap_with") [.const 7]) := by
      rw [evaluateHOLFiniteState_ite, hev1, if_pos hcmp1]; simp
    rw [hite1]
    have hno_none := evaluate_call_trap_with_no_none pState 7 hcode_p
    have hno_ret := fun w => evaluate_call_trap_with_no_return pState 7 w hcode_p
    rcases htr : evaluateHOLFiniteState pState (.call (some (none, none)) (ofString "trap_with") [.const 7]) with ⟨r1, s1⟩
    rw [htr] at hno_none hno_ret
    cases r1 with
    | none => exact absurd rfl hno_none
    | some r1' =>
      intro retVal hret
      exact False.elim (hno_ret retVal hret)
  · have hite1 : evaluateHOLFiniteState pState
        (.ite (.cmp .lower (.op .sub [.var .local (ofString "p"), .var .global (ofString "frame_mem_ptr")])
            (.var .local (ofString "n")))
          (.call (some (none, none)) (ofString "trap_with") [.const 7])
          .skip) = (none, pState) := by
      rw [evaluateHOLFiniteState_ite, hev1, if_neg hcmp1]; simp [evaluateHOLFiniteState_skip]
    rw [hite1]
    dsimp only
    rw [evaluateHOLFiniteState_dec_total]
    let q : BitVec 64 := (p - n) &&& ((0 : BitVec 64) - 8)
    have hq_eval : @evalHOLExact 64 F _ pState.toExact
        (fun a => Classical.propDecidable (pState.memaddrs a))
        (.op .and [.op .sub [.var .local (ofString "p"), .var .local (ofString "n")],
          .op .sub [.const 0, .const 8]]) = some (.val (.word q)) := by
      simp only [evalHOLExact, evalListHOLExact, hp_loc, hn_loc,
        wordOpHOL, wordOp, valueIsWord, valueWord, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr]
      have h2 : AndOp.and ((0 : BitVec 64) - 8) (~~~0) = (0 : BitVec 64) - 8 := by decide
      simp only [h2]
      rfl
    dsimp only
    rw [hq_eval]
    have hsh_q : shapeEqHOL .one (shapeOfHOLExact (.val (.word q))) = true := by
      simp [shapeEqHOL, shapeOfHOLExact]
    dsimp only
    rw [if_pos hsh_q]
    dsimp only
    let qState := setVarHOLFinite (ofString "q") (.val (.word q)) pState
    have hq_loc : qState.locals.lookup (ofString "q") = some (.val (.word q)) := by
      simp [qState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hp_loc_q : qState.locals.lookup (ofString "p") = some (.val (.word p)) := by
      simp [qState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hp_loc,
        show ofString "q" ≠ ofString "p" by decide]
    have hcode_q : qState.code = originalRuntimeCode := hcode
    rw [evaluateHOLFiniteState_seq_line780]
    have hev2 : @evalHOLExact 64 F _ qState.toExact
        (fun a => Classical.propDecidable (qState.memaddrs a))
        (.cmp .lower (.var .local (ofString "q")) (.var .global (ofString "frame_mem_ptr"))) =
        some (.val (.word (if q.toNat < f.toNat then 1 else 0))) := by
      have hf_q : qState.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word f)) :=
        hf_lookup
      simp only [evalHOLExact, hq_loc, hf_q, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def,
        decide_eq_true_eq]
    by_cases hcmp2 : q.toNat < f.toNat
    · have hite2 : evaluateHOLFiniteState qState
          (.ite (.cmp .lower (.var .local (ofString "q")) (.var .global (ofString "frame_mem_ptr")))
            (.call (some (none, none)) (ofString "trap_with") [.const 7])
            .skip) =
          evaluateHOLFiniteState qState (.call (some (none, none)) (ofString "trap_with") [.const 7]) := by
        rw [evaluateHOLFiniteState_ite, hev2, if_pos hcmp2]; simp
      rw [hite2]
      have hno_none := evaluate_call_trap_with_no_none qState 7 hcode_q
      have hno_ret := fun w => evaluate_call_trap_with_no_return qState 7 w hcode_q
      rcases htr : evaluateHOLFiniteState qState (.call (some (none, none)) (ofString "trap_with") [.const 7]) with ⟨r2, s2⟩
      rw [htr] at hno_none hno_ret
      cases r2 with
      | none => exact absurd rfl hno_none
      | some r2' =>
        intro retVal hret
        exact False.elim (hno_ret retVal hret)
    · have hite2 : evaluateHOLFiniteState qState
          (.ite (.cmp .lower (.var .local (ofString "q")) (.var .global (ofString "frame_mem_ptr")))
            (.call (some (none, none)) (ofString "trap_with") [.const 7])
            .skip) = (none, qState) := by
        rw [evaluateHOLFiniteState_ite, hev2, if_neg hcmp2]; simp [evaluateHOLFiniteState_skip]
      rw [hite2]
      dsimp only
      have hp_g : qState.globals.lookup (ofString "scratch_ptr") = some (.val (.word p)) := hp_lookup
      have heval_end : evaluateHOLFiniteState qState
          (.seq (.assign .global (ofString "scratch_ptr") (.var .local (ofString "q")))
            (.return (.var .local (ofString "q")))) =
          (some (.returned (.val (.word q))),
            emptyLocalsHOLFinite (setGlobalHOLFinite (ofString "scratch_ptr") (.val (.word q)) qState)) := by
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
        simp [evalHOLExact, hq_loc, hp_loc_q, isValidValueHOLExact, lookupKvarHOLExact, hp_g,
          shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite, setGlobalHOLFinite,
          evaluateHOLFiniteState_return, sizeOfShapeWithContextHOL]
      rw [heval_end]
      intro retVal hret
      injection hret with hr
      injection hr with hr'
      exact ⟨hr'.symm, hcmp1, hcmp2, rfl⟩

/-! ## 4. Normal-return combinators (`Ret` and `NS`) -/

def Ret {F : Type} (s : PanSemStateFiniteExact 64 F) (p : ProgHOL 64)
    (Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop) : Prop :=
  ∀ v, (evaluateHOLFiniteState s p).1 = some (.returned v) → Φ v (evaluateHOLFiniteState s p).2

noncomputable abbrev ev {F : Type} (s : PanSemStateFiniteExact 64 F) (e : ExpHOL 64) :
    Option (ValueHOL 64) :=
  @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e

theorem Ret.seq {F : Type} {s : PanSemStateFiniteExact 64 F} {a b : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (ha : Ret s a Φ) (hb : ∀ t, evaluateHOLFiniteState s a = (none, t) → Ret t b Φ) :
    Ret s (.seq a b) Φ := by
  intro v hv
  rw [evaluateHOLFiniteState_seq_line780] at hv ⊢
  rcases h : evaluateHOLFiniteState s a with ⟨r, t⟩
  simp only [h] at hv
  try simp only [h]
  cases r with
  | none => exact hb t h v hv
  | some r' =>
    have := ha v (by rw [h]; exact hv)
    rw [h] at this
    exact this

def updW (m : BitVec 64 → HolWordLab 64) (a w : BitVec 64) : BitVec 64 → HolWordLab 64 :=
  fun c => if c = a then .word w else m c

theorem stores_word {dom : BitVec 64 → Prop} (inst : DecidablePred dom)
    {m m' : BitVec 64 → HolWordLab 64}
    {a w : BitVec 64}
    (h : @panMemStoresHOL 64 _ a (flattenHOL (.val (.word w))) dom inst m = some m') :
    dom a ∧ m' = updW m a w := by
  unfold flattenHOL at h
  unfold panMemStoresHOL at h
  unfold panMemStoreHOL at h
  by_cases hd : dom a
  · simp only [hd, ↓reduceIte] at h
    simp only [panMemStoresHOL, Option.some.injEq] at h
    exact ⟨hd, h.symm⟩
  · simp [hd] at h

theorem Ret.seq_store {F : Type} {s : PanSemStateFiniteExact 64 F} {d e : ExpHOL 64}
    {b : ProgHOL 64} {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hb : ∀ (a : BitVec 64) (val : ValueHOL 64) m, ev s d = some (.val (.word a)) →
      ev s e = some val →
      @panMemStoresHOL 64 _ a (flattenHOL val) s.memaddrs
        (fun x => Classical.propDecidable (s.memaddrs x)) s.memory = some m →
      Ret { s with memory := m } b Φ) :
    Ret s (.seq (.store d e) b) Φ := by
  refine Ret.seq ?_ ?_
  · intro v hv
    rw [evaluateHOLFiniteState_store] at hv
    revert hv
    split
    · split
      · split <;> simp
      · simp
    · simp
  · intro t ht
    rw [evaluateHOLFiniteState_store] at ht
    revert ht
    split
    · rename_i a hd
      split
      · rename_i val he
        split
        · rename_i m hm
          intro ht
          simp only [Prod.mk.injEq] at ht
          rw [← ht.2]
          exact hb a val m hd he hm
        · simp
      · simp
    · simp

theorem Ret.seq_storeW {F : Type} {s : PanSemStateFiniteExact 64 F} {d e : ExpHOL 64}
    {b : ProgHOL 64} {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (a w : BitVec 64) (hd : ev s d = some (.val (.word a))) (he : ev s e = some (.val (.word w)))
    (hb : s.memaddrs a → Ret { s with memory := updW s.memory a w } b Φ) :
    Ret s (.seq (.store d e) b) Φ := by
  apply Ret.seq_store
  intro a' val m hd' he' hm
  rw [hd] at hd'
  rw [he] at he'
  simp only [Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hd' he'
  subst hd' he'
  obtain ⟨hdom, rfl⟩ := stores_word _ hm
  exact hb hdom

theorem Ret.dec {F : Type} {s : PanSemStateFiniteExact 64 F} {x : MlS} {sh : ShapeHOL}
    {init : ExpHOL 64} {body : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (h : ∀ val, ev s init = some val →
      Ret (setVarHOLFinite x val s) body
        (fun v t => Φ v { t with
          locals := HolFiniteMapExact.resVarEq t.locals (x, s.locals.lookup x) })) :
    Ret s (.dec x sh init body) Φ := by
  intro v hv
  rw [evaluateHOLFiniteState_dec_total] at hv ⊢
  dsimp only at hv ⊢
  revert hv
  split
  · simp
  · rename_i val hval
    split
    · intro hv
      exact h val hval v hv
    · simp

theorem Ret.ret {F : Type} {s : PanSemStateFiniteExact 64 F} {e : ExpHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (h : ∀ val, ev s e = some val → Φ val (emptyLocalsHOLFinite s)) :
    Ret s (.return e) Φ := by
  intro v hv
  rw [evaluateHOLFiniteState_return] at hv ⊢
  revert hv
  split
  · simp
  · rename_i val hval
    split
    · intro hv
      simp only [Option.some.injEq, PanSemResultExact.returned.injEq] at hv
      subst hv
      exact h _ hval
    · simp

theorem Ret.decCall1 {F : Type} {s : PanSemStateFiniteExact 64 F} {x fname : MlS}
    {arg : ExpHOL 64} {cont fbody : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hcode : s.code = originalRuntimeCode)
    (hlook : originalRuntimeCode.lookup fname = some ([(ofString "n", .one)], fbody, .one))
    (nv : BitVec 64) (harg : ev s arg = some (.val (.word nv)))
    (hk : ∀ w post,
      evaluateHOLFiniteState
        (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "n", .val (.word nv))))
        fbody = (some (.returned (.val (.word w))), post) →
      Ret (setVarHOLFinite x (.val (.word w)) { post with locals := s.locals }) cont
        (fun v t => Φ v { t with
          locals := HolFiniteMapExact.resVarEq t.locals (x, s.locals.lookup x) })) :
    Ret s (.decCall x .one fname [arg] cont) Φ := by
  intro v hv
  rw [evaluateHOLFiniteState_decCall_total] at hv ⊢
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [arg] =
      some [.val (.word nv)] := by
    simp only [ev] at harg
    simp [evalListHOLFinite, evalListHOLExact, harg]
  have hl := pan_one_word_lookup s.code.lookup fname (ofString "n") fbody nv
    (by rw [hcode]; exact hlook)
  rw [hargs] at hv ⊢
  dsimp only at hv ⊢
  rw [hl] at hv ⊢
  dsimp only at hv ⊢
  revert hv
  split
  · simp
  · rw [fixClockHOLFinite_evaluateState]
    rcases hrun : evaluateHOLFiniteState
        (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "n", .val (.word nv))))
        fbody with ⟨r, post⟩
    dsimp only
    rcases r with _ | r
    · simp
    · cases r with
      | returned rv =>
        dsimp only
        split
        · rename_i hsh
          rcases rv with ⟨⟨w⟩⟩ | fs | ⟨nm, fs⟩
          · intro hv
            exact hk w post hrun v hv
          · simp [shapeOfHOLExact, shapeEqHOL] at hsh
          · simp [shapeOfHOLExact, shapeEqHOL] at hsh
        · simp
      | _ => simp

theorem Ret.decCall_alloc {F : Type} {s : PanSemStateFiniteExact 64 F} {x : MlS}
    {arg : ExpHOL 64} {cont : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hcode : s.code = originalRuntimeCode) (nv : BitVec 64)
    (harg : ev s arg = some (.val (.word nv))) (p : BitVec 64)
    (hp : s.globals.lookup (ofString "heap_ptr") = some (.val (.word p)))
    (hk : ¬ ((cMax - p).toNat < nv.toNat) →
      ¬ (cMax.toNat < ((p + (nv + 7)) &&& ((0 : BitVec 64) - 8)).toNat) →
      Ret (setVarHOLFinite x (.val (.word p)) { s with
          globals := (s.globals.update (ofString "heap_ptr",
            .val (.word ((p + (nv + 7)) &&& ((0 : BitVec 64) - 8)))))
          clock := s.clock - 1 }) cont
        (fun v t => Φ v { t with
          locals := HolFiniteMapExact.resVarEq t.locals (x, s.locals.lookup x) })) :
    Ret s (.decCall x .one (ofString "alloc") [arg] cont) Φ := by
  refine Ret.decCall1 hcode lookup_alloc nv harg ?_
  intro w post hrun
  have hn : (callEntryStateHOLFinite s
      (HolFiniteMapExact.empty.update (ofString "n", .val (.word nv)))).locals.lookup (ofString "n") =
      some (.val (.word nv)) := by
    simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have := alloc_body_run (callEntryStateHOLFinite s
    (HolFiniteMapExact.empty.update (ofString "n", .val (.word nv)))) p nv hcode hp hn
    (.val (.word w)) (by rw [hrun])
  rw [hrun] at this
  obtain ⟨hw, h1, h2, hpost⟩ := this
  simp only [ValueHOL.val.injEq, HolWordLab.word.injEq] at hw
  subst hw
  have hst : { post with locals := s.locals } = { s with
      globals := (s.globals.update (ofString "heap_ptr",
        .val (.word ((w + (nv + 7)) &&& ((0 : BitVec 64) - 8)))))
      clock := s.clock - 1 } := by
    dsimp only at hpost
    rw [hpost]; rfl
  rw [hst]
  exact hk h1 h2

def NS {F : Type} (s : PanSemStateFiniteExact 64 F) (L G : HolFiniteMapExact MlS (ValueHOL 64))
    (M : BitVec 64 → HolWordLab 64) (C : Nat) : PanSemStateFiniteExact 64 F :=
  { s with locals := L, globals := G, memory := M, clock := C }

section NSlemmas
variable {F : Type} (s : PanSemStateFiniteExact 64 F) (L G : HolFiniteMapExact MlS (ValueHOL 64))
  (M : BitVec 64 → HolWordLab 64) (C : Nat)
@[simp] theorem NS_locals : (NS s L G M C).locals = L := rfl
@[simp] theorem NS_globals : (NS s L G M C).globals = G := rfl
@[simp] theorem NS_memory : (NS s L G M C).memory = M := rfl
@[simp] theorem NS_clock : (NS s L G M C).clock = C := rfl
@[simp] theorem NS_code : (NS s L G M C).code = s.code := rfl
@[simp] theorem NS_memaddrs : (NS s L G M C).memaddrs = s.memaddrs := rfl
@[simp] theorem NS_toExact_memaddrs : (NS s L G M C).toExact.memaddrs = s.memaddrs := rfl
end NSlemmas

theorem Ret.of_NS {F : Type} {s : PanSemStateFiniteExact 64 F} {p : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (h : Ret (NS s s.locals s.globals s.memory s.clock) p Φ) : Ret s p Φ := by
  cases s; exact h

theorem Ret.ns_storeW {F : Type} {s : PanSemStateFiniteExact 64 F} {L G} {M C}
    {d e : ExpHOL 64} {b : ProgHOL 64} {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (a w : BitVec 64) (hd : ev (NS s L G M C) d = some (.val (.word a)))
    (he : ev (NS s L G M C) e = some (.val (.word w)))
    (hb : s.memaddrs a → Ret (NS s L G (updW M a w) C) b Φ) :
    Ret (NS s L G M C) (.seq (.store d e) b) Φ :=
  Ret.seq_storeW a w hd he hb

theorem Ret.ns_dec {F : Type} {s : PanSemStateFiniteExact 64 F} {L G} {M C} {x : MlS}
    {sh : ShapeHOL} {init : ExpHOL 64} {body : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (h : ∀ val, ev (NS s L G M C) init = some val →
      Ret (NS s (L.update (x, val)) G M C) body
        (fun v t => Φ v { t with locals := HolFiniteMapExact.resVarEq t.locals (x, L.lookup x) })) :
    Ret (NS s L G M C) (.dec x sh init body) Φ :=
  Ret.dec h

theorem Ret.ns_alloc {F : Type} {s : PanSemStateFiniteExact 64 F} {L G} {M C} {x : MlS}
    {arg : ExpHOL 64} {cont : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hcode : s.code = originalRuntimeCode) (nv : BitVec 64)
    (harg : ev (NS s L G M C) arg = some (.val (.word nv))) (p : BitVec 64)
    (hp : G.lookup (ofString "heap_ptr") = some (.val (.word p)))
    (hk : ¬ ((cMax - p).toNat < nv.toNat) →
      ¬ (cMax.toNat < ((p + (nv + 7)) &&& ((0 : BitVec 64) - 8)).toNat) →
      Ret (NS s (L.update (x, .val (.word p)))
          (G.update (ofString "heap_ptr", .val (.word ((p + (nv + 7)) &&& ((0 : BitVec 64) - 8)))))
          M (C - 1)) cont
        (fun v t => Φ v { t with locals := HolFiniteMapExact.resVarEq t.locals (x, L.lookup x) })) :
    Ret (NS s L G M C) (.decCall x .one (ofString "alloc") [arg] cont) Φ :=
  Ret.decCall_alloc hcode nv harg p hp hk

theorem Ret.ns_ret {F : Type} {s : PanSemStateFiniteExact 64 F} {L G} {M C} {e : ExpHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (h : ∀ val, ev (NS s L G M C) e = some val →
      Φ val (NS s (emptyLocalsHOLFinite (NS s L G M C)).locals G M C)) :
    Ret (NS s L G M C) (.return e) Φ :=
  Ret.ret h

theorem ofNat_add_toNat_eq (p : BitVec 64) (k : Nat) :
    BitVec.ofNat 64 (p.toNat + k) = p + BitVec.ofNat 64 k := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, BitVec.toNat_ofNat]

end InitECandidate.Solver.Wave8Contracts.M26
