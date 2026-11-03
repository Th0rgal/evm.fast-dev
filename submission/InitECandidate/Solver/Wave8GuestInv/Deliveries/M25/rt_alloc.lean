import InitECandidate.Solver.Wave8GuestInv.MemoryViews
import InitECandidate.Solver.HeapPotential
import Guest.SoftwareAst

/-! `rt_alloc`: `alloc(n)` returns a fresh aligned heap block of `n` bytes (`FreshBlock`),
preserving `ArenaReady` and `AllocatorGrows`.
Checked against frozen spec revision 9 (`8a79d9f28`, tag `wave8-spec-frozen-r9`). -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace InitECandidate.Solver.Wave8Contracts.M25

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

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

private theorem lookup_alloc :
    originalRuntimeCode.lookup (ofString "alloc") =
      some ([(ofString "n", .one)], sourceFnBody Guest.Software.guestFn_alloc, .one) :=
  lookup_of_guestAst_getElem 7 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_alloc) rfl

private theorem ordinaryDomain_of_aligned_heap (addr : Nat) (halign : addr % 8 = 0)
    (hlo : sourceBase ≤ addr) (hhi : addr < heapLimit) :
    ordinaryDomain (BitVec.ofNat 64 addr) := by
  refine (Flapjack.Compiler.Backend.StackRemove.mem_addresses _ _ _).mpr
    ⟨(addr - sourceBase) / 8, ?_, ?_⟩
  · simp only [heapLimit, scratchStart, sourceBase, stackStart, ramEnd, ramStart, ramSize,
      stackSize, globalsWords] at hlo hhi ⊢
    omega
  · apply BitVec.eq_of_toNat_eq
    change (BitVec.ofNat 64 addr).toNat = (BitVec.ofNat 64 sourceBase +
      BitVec.ofNat 64 ((addr - sourceBase) / 8) * BitVec.ofNat 64 8).toNat
    rw [BitVec.ofNat_mul_ofNat, BitVec.ofNat_add_ofNat]
    simp only [BitVec.toNat_ofNat]
    simp only [heapLimit, scratchStart, sourceBase] at hlo hhi ⊢
    omega

private theorem alloc_returned_props {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode)
    (hP : ArenaReady s)
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_alloc)).1 =
      some (.returned v)) :
    let post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_alloc)).2
    ∃ w : BitVec 64, v = .val (.word w) ∧
      ArenaReady post ∧ AllocatorGrows s post ∧ FreshBlock s post w.toNat (locN s "n") := by
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
  rcases harena : hP with ⟨hginv, hp_lo, hp_hi, hfm_lo, hfm_hi, hsp_hi, hp_al, hfm_al, hsp_al⟩
  -- `heap_ptr` must be a word because `sourceBase > 0` and `globN s "heap_ptr" ≥ sourceBase`
  have hp_word : ∃ p : BitVec 64, s.globals.lookup (ofString "heap_ptr") = some (.val (.word p)) := by
    rcases hg : s.globals.lookup (ofString "heap_ptr") with _ | gv
    · simp [globN, hg, sourceBase] at hp_lo
    · rcases gv with ⟨⟨p⟩⟩ | fs | ⟨nm, fs⟩
      · exact ⟨p, rfl⟩
      · simp [globN, hg, sourceBase] at hp_lo
      · simp [globN, hg, sourceBase] at hp_lo
  obtain ⟨p, hp_lookup⟩ := hp_word
  have hp_glob : globN s "heap_ptr" = p.toNat := by simp [globN, hp_lookup]
  -- `n` must be a word for `alloc` body to return (the first `ite` evaluates local `"n"`).
  have hn_word : ∃ n : BitVec 64, s.locals.lookup (ofString "n") = some (.val (.word n)) := by
    rcases hl : s.locals.lookup (ofString "n") with _ | lv
    · exfalso
      rw [hbody_eq, evaluateHOLFiniteState_dec_total] at hret
      have hp_ev : @evalHOLExact 64 F _ s.toExact
          (fun a => Classical.propDecidable (s.memaddrs a))
          (.var .global (ofString "heap_ptr")) = some (.val (.word p)) := hp_lookup
      dsimp only at hret
      rw [hp_ev] at hret
      have hsh_p : shapeEqHOL .one (shapeOfHOLExact (.val (.word p))) = true := by
        simp [shapeEqHOL, shapeOfHOLExact]
      dsimp only at hret
      rw [if_pos hsh_p] at hret
      dsimp only at hret
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hret
      have hnl : (setVarHOLFinite (ofString "p") (.val (.word p)) s).locals.lookup (ofString "n") = none := by
        simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hl,
          show ofString "p" ≠ ofString "n" by decide]
      simp [evalHOLExact, evalListHOLExact, hnl] at hret
    · rcases lv with ⟨⟨n⟩⟩ | fs | ⟨nm, fs⟩
      · exact ⟨n, rfl⟩
      · exfalso
        rw [hbody_eq, evaluateHOLFiniteState_dec_total] at hret
        have hp_ev : @evalHOLExact 64 F _ s.toExact
            (fun a => Classical.propDecidable (s.memaddrs a))
            (.var .global (ofString "heap_ptr")) = some (.val (.word p)) := hp_lookup
        dsimp only at hret
        rw [hp_ev] at hret
        have hsh_p : shapeEqHOL .one (shapeOfHOLExact (.val (.word p))) = true := by
          simp [shapeEqHOL, shapeOfHOLExact]
        dsimp only at hret
        rw [if_pos hsh_p] at hret
        dsimp only at hret
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hret
        have hnl : (setVarHOLFinite (ofString "p") (.val (.word p)) s).locals.lookup (ofString "n") = some (.rStruct fs) := by
          simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hl,
            show ofString "p" ≠ ofString "n" by decide]
        simp [evalHOLExact, evalListHOLExact, hnl] at hret
      · exfalso
        rw [hbody_eq, evaluateHOLFiniteState_dec_total] at hret
        have hp_ev : @evalHOLExact 64 F _ s.toExact
            (fun a => Classical.propDecidable (s.memaddrs a))
            (.var .global (ofString "heap_ptr")) = some (.val (.word p)) := hp_lookup
        dsimp only at hret
        rw [hp_ev] at hret
        have hsh_p : shapeEqHOL .one (shapeOfHOLExact (.val (.word p))) = true := by
          simp [shapeEqHOL, shapeOfHOLExact]
        dsimp only at hret
        rw [if_pos hsh_p] at hret
        dsimp only at hret
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hret
        have hnl : (setVarHOLFinite (ofString "p") (.val (.word p)) s).locals.lookup (ofString "n") = some (.nStruct nm fs) := by
          simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hl,
            show ofString "p" ≠ ofString "n" by decide]
        simp [evalHOLExact, evalListHOLExact, hnl] at hret
  obtain ⟨n, hn_lookup⟩ := hn_word
  have hn_loc : locN s "n" = n.toNat := by simp [locN, hn_lookup]
  -- Step through `alloc` body explicitly to get the exact post state and both guard inequalities
  rw [hbody_eq, evaluateHOLFiniteState_dec_total] at hret ⊢
  have hp_eval : @evalHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a))
      (.var .global (ofString "heap_ptr")) = some (.val (.word p)) := hp_lookup
  dsimp only at hret ⊢
  rw [hp_eval] at hret ⊢
  have hsh_p : shapeEqHOL .one (shapeOfHOLExact (.val (.word p))) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  dsimp only at hret ⊢
  rw [if_pos hsh_p] at hret ⊢
  dsimp only at hret ⊢
  let pState := setVarHOLFinite (ofString "p") (.val (.word p)) s
  have hp_loc : pState.locals.lookup (ofString "p") = some (.val (.word p)) := by
    simp [pState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hn_loc_p : pState.locals.lookup (ofString "n") = some (.val (.word n)) := by
    simp [pState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn_lookup,
      show ofString "p" ≠ ofString "n" by decide]
  rw [evaluateHOLFiniteState_seq_line780] at hret ⊢
  have hev1 : @evalHOLExact 64 F _ pState.toExact
      (fun a => Classical.propDecidable (pState.memaddrs a))
      (.cmp .lower (.op .sub [.const cMax, .var .local (ofString "p")])
        (.var .local (ofString "n"))) =
      some (.val (.word (if (cMax - p).toNat < n.toNat then 1 else 0))) := by
    simp only [evalHOLExact, evalListHOLExact, hp_loc, hn_loc_p,
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
    rw [hite1] at hret
    have hno_none := evaluate_call_trap_with_no_none pState 1 hcode
    have hno_ret := fun w => evaluate_call_trap_with_no_return pState 1 w hcode
    rcases htr : evaluateHOLFiniteState pState (.call (some (none, none)) (ofString "trap_with") [.const 1]) with ⟨r1, s1⟩
    rw [htr] at hno_none hno_ret hret
    cases r1 with
    | none => exact absurd rfl hno_none
    | some _ => exact absurd hret (hno_ret v)
  · have hite1 : evaluateHOLFiniteState pState
        (.ite (.cmp .lower (.op .sub [.const cMax, .var .local (ofString "p")])
            (.var .local (ofString "n")))
          (.call (some (none, none)) (ofString "trap_with") [.const 1])
          .skip) = (none, pState) := by
      rw [evaluateHOLFiniteState_ite, hev1, if_neg hcmp1]; simp [evaluateHOLFiniteState_skip]
    rw [hite1] at hret ⊢
    dsimp only at hret ⊢
    rw [evaluateHOLFiniteState_dec_total] at hret ⊢
    let q : BitVec 64 := (p + (n + 7)) &&& ((0 : BitVec 64) - 8)
    have hq_eval : @evalHOLExact 64 F _ pState.toExact
        (fun a => Classical.propDecidable (pState.memaddrs a))
        (.op .and [.op .add [.var .local (ofString "p"), .var .local (ofString "n"), .const 7],
          .op .sub [.const 0, .const 8]]) = some (.val (.word q)) := by
      simp only [evalHOLExact, evalListHOLExact, hp_loc, hn_loc_p,
        wordOpHOL, wordOp, valueIsWord, valueWord, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr]
      exact congrArg (fun w => some (ValueHOL.val (HolWordLab.word w))) (alloc_q_word_eq p n)
    dsimp only at hret ⊢
    rw [hq_eval] at hret ⊢
    have hsh_q : shapeEqHOL .one (shapeOfHOLExact (.val (.word q))) = true := by
      simp [shapeEqHOL, shapeOfHOLExact]
    dsimp only at hret ⊢
    rw [if_pos hsh_q] at hret ⊢
    dsimp only at hret ⊢
    let qState := setVarHOLFinite (ofString "q") (.val (.word q)) pState
    have hq_loc : qState.locals.lookup (ofString "q") = some (.val (.word q)) := by
      simp [qState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hp_loc_q : qState.locals.lookup (ofString "p") = some (.val (.word p)) := by
      simp [qState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hp_loc,
        show ofString "q" ≠ ofString "p" by decide]
    rw [evaluateHOLFiniteState_seq_line780] at hret ⊢
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
      rw [hite2] at hret
      have hno_none := evaluate_call_trap_with_no_none qState 1 hcode
      have hno_ret := fun w => evaluate_call_trap_with_no_return qState 1 w hcode
      rcases htr : evaluateHOLFiniteState qState (.call (some (none, none)) (ofString "trap_with") [.const 1]) with ⟨r2, s2⟩
      rw [htr] at hno_none hno_ret hret
      cases r2 with
      | none => exact absurd rfl hno_none
      | some _ => exact absurd hret (hno_ret v)
    · have hite2 : evaluateHOLFiniteState qState
          (.ite (.cmp .lower (.const cMax) (.var .local (ofString "q")))
            (.call (some (none, none)) (ofString "trap_with") [.const 1])
            .skip) = (none, qState) := by
        rw [evaluateHOLFiniteState_ite, hev2, if_neg hcmp2]; simp [evaluateHOLFiniteState_skip]
      rw [hite2] at hret ⊢
      dsimp only at hret ⊢
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
      rw [heval_end] at hret ⊢
      dsimp only at hret ⊢
      injection hret with hr
      injection hr with hr'
      subst hr'
      -- Capture the exact evaluated post state
      set post : PanSemStateFiniteExact 64 F :=
        { locals :=
            ((setGlobalHOLFinite (ofString "heap_ptr") (ValueHOL.val (HolWordLab.word q))
                          qState).emptyLocalsHOLFinite.locals.resVarEq
                  (ofString "q", pState.locals.lookup (ofString "q"))).resVarEq
              (ofString "p", s.locals.lookup (ofString "p")),
          globals :=
            (setGlobalHOLFinite (ofString "heap_ptr") (ValueHOL.val (HolWordLab.word q))
                  qState).emptyLocalsHOLFinite.globals,
          structs :=
            (setGlobalHOLFinite (ofString "heap_ptr") (ValueHOL.val (HolWordLab.word q))
                  qState).emptyLocalsHOLFinite.structs,
          code :=
            (setGlobalHOLFinite (ofString "heap_ptr") (ValueHOL.val (HolWordLab.word q))
                  qState).emptyLocalsHOLFinite.code,
          eshapes :=
            (setGlobalHOLFinite (ofString "heap_ptr") (ValueHOL.val (HolWordLab.word q))
                  qState).emptyLocalsHOLFinite.eshapes,
          memory :=
            (setGlobalHOLFinite (ofString "heap_ptr") (ValueHOL.val (HolWordLab.word q))
                  qState).emptyLocalsHOLFinite.memory,
          memaddrs :=
            (setGlobalHOLFinite (ofString "heap_ptr") (ValueHOL.val (HolWordLab.word q))
                  qState).emptyLocalsHOLFinite.memaddrs,
          shMemaddrs :=
            (setGlobalHOLFinite (ofString "heap_ptr") (ValueHOL.val (HolWordLab.word q))
                  qState).emptyLocalsHOLFinite.shMemaddrs,
          clock :=
            (setGlobalHOLFinite (ofString "heap_ptr") (ValueHOL.val (HolWordLab.word q))
                  qState).emptyLocalsHOLFinite.clock,
          be :=
            (setGlobalHOLFinite (ofString "heap_ptr") (ValueHOL.val (HolWordLab.word q))
                  qState).emptyLocalsHOLFinite.be,
          ffi :=
            (setGlobalHOLFinite (ofString "heap_ptr") (ValueHOL.val (HolWordLab.word q))
                  qState).emptyLocalsHOLFinite.ffi,
          baseAddr :=
            (setGlobalHOLFinite (ofString "heap_ptr") (ValueHOL.val (HolWordLab.word q))
                  qState).emptyLocalsHOLFinite.baseAddr,
          topAddr :=
            (setGlobalHOLFinite (ofString "heap_ptr") (ValueHOL.val (HolWordLab.word q))
                  qState).emptyLocalsHOLFinite.topAddr }
      -- Arithmetic bounds on `p`, `n`, `q`
      have hcMax_val : cMax.toNat = 2952790016 := rfl
      have hhl_val : heapLimit = 2952790016 := rfl
      have hp_le_cMax : p.toNat ≤ cMax.toNat := by omega
      have hsub_toNat : (cMax - p).toNat = cMax.toNat - p.toNat := by
        rw [BitVec.toNat_sub_of_le]
        exact BitVec.le_def.mpr hp_le_cMax
      have hn_le : n.toNat ≤ 2952790016 - p.toNat := by omega
      have h7 : (7 : BitVec 64).toNat = 7 := rfl
      have hn7 : (n + 7).toNat = n.toNat + 7 := by
        rw [BitVec.toNat_add, h7]
        omega
      have hsum : (p + (n + 7)).toNat = p.toNat + n.toNat + 7 := by
        rw [BitVec.toNat_add, hn7]
        omega
      have hq_toNat : q.toNat = (p.toNat + n.toNat + 7) / 8 * 8 := by
        have hq1 := and_neg8_toNat (p + (n + 7))
        change q.toNat = _ at hq1
        rw [hq1, hsum]
      have hp_mod8 : p.toNat % 8 = 0 := by omega
      have hq_exact : q.toNat = p.toNat + (n.toNat + 7) / 8 * 8 := by omega
      have hq_le_hl : q.toNat ≤ heapLimit := by omega
      have hpost_hp : globN post "heap_ptr" = q.toNat := by
        simp [post, globN, emptyLocalsHOLFinite, setGlobalHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hpost_fm : globN post "frame_mem_ptr" = globN s "frame_mem_ptr" := by
        simp [post, qState, pState, globN, emptyLocalsHOLFinite, setGlobalHOLFinite, setVarHOLFinite,
          HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "heap_ptr" ≠ ofString "frame_mem_ptr" by decide]
      have hpost_sp : globN post "scratch_ptr" = globN s "scratch_ptr" := by
        simp [post, qState, pState, globN, emptyLocalsHOLFinite, setGlobalHOLFinite, setVarHOLFinite,
          HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "heap_ptr" ≠ ofString "scratch_ptr" by decide]
      have hpost_ginv : GuestInv post := ⟨hginv.code, hginv.memaddrs, hginv.shMemaddrs, hginv.baseAddr⟩
      have hpost_arena : ArenaOK post := by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hpost_hp]; omega
        · rw [hpost_hp]; exact hq_le_hl
        · rw [hpost_fm]; exact hfm_lo
        · rw [hpost_fm, hpost_sp]; exact hfm_hi
        · rw [hpost_sp]; exact hsp_hi
        · rw [hpost_hp]; omega
        · rw [hpost_fm]; exact hfm_al
        · rw [hpost_sp]; exact hsp_al.1
        · exact globalsWord_update (s := s) (t := post) (ofString "heap_ptr") q rfl hsp_al.2
      have hgrows : AllocatorGrows s post := by
        refine ⟨?_, ?_⟩
        · rw [hp_glob, hpost_hp]; omega
        · rw [hpost_sp]
      refine ⟨p, rfl, ⟨hpost_ginv, hpost_arena⟩, hgrows, ?_⟩
      refine ⟨hp_mod8, ?_, ?_⟩
      · rw [hp_glob, hpost_hp, hn_loc]
        exact ⟨Nat.le_refl _, by omega⟩
      · rw [hn_loc]
        refine ⟨hp_mod8, by omega, ?_⟩
        intro k hk
        dsimp only at hk ⊢
        have haddr_lo : sourceBase ≤ p.toNat + 8 * k := by omega
        have haddr_hi : p.toNat + 8 * k < heapLimit := by omega
        have haddr_al : (p.toNat + 8 * k) % 8 = 0 := by omega
        have hdom : post.memaddrs (BitVec.ofNat 64 (p.toNat + 8 * k)) := by
          change s.memaddrs _
          rw [hginv.memaddrs]
          exact ordinaryDomain_of_aligned_heap (p.toNat + 8 * k) haddr_al haddr_lo haddr_hi
        cases hcell : post.memory (BitVec.ofNat 64 (p.toNat + 8 * k)) with
        | word cw => exact ⟨cw, hdom, hcell⟩

/-- `alloc` (AST line 66): returns a fresh aligned heap block of `n` bytes. -/
theorem «rt_alloc» :
    Returns ArenaReady (fun s post p => FreshBlock s post p (locN s "n"))
      (ofString "alloc") := by
  refine ⟨_, _, _, lookup_alloc, ?_⟩
  intro F s hcode hP _ _hnt v hret
  exact alloc_returned_props s hcode hP v hret

end InitECandidate.Solver.Wave8Contracts.M25
