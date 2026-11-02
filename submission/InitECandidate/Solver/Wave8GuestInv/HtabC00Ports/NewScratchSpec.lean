import InitECandidate.Solver.Wave8GuestInv.HtabC00Ports.Bridge
import InitECandidate.Solver.HeapPotential

/-! `htab_new_scratch_spec`: verified against R11 `Wave8GuestInv` definitions (`HtabNewReady`,
`HtabNewExit`, including `AllocatorGrows`, `hdr post w.toNat 0 = locN s "key_len"`, 8-byte
alignment in `ArenaOK`, `CellHits` in `FrameOutside`, `MlS` global frame, and `cap ≤ htabCapMax`
with the `cap < 2 ? 2 : cap` clamp). -/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.HtabC00Ports

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8M19.Htab

/-! ## 1. Distinctness of local/global names used in `htab_new_scratch` -/

section NewNames
@[local simp] theorem nm1 : (ofString "t" = ofString "stride") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem nm2 : (ofString "t" = ofString "ncap") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem nm3 : (ofString "t" = ofString "keys") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem nm4 : (ofString "t" = ofString "nodes") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem nm5 : (ofString "t" = ofString "order") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem nm6 : (ofString "t" = ofString "key_len") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem nm7 : (ofString "t" = ofString "cap") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem nm8 : (ofString "stride" = ofString "t") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem nm9 : (ofString "stride" = ofString "ncap") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem nm10 : (ofString "stride" = ofString "keys") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem nm11 : (ofString "stride" = ofString "nodes") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem nm12 : (ofString "stride" = ofString "order") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem nm13 : (ofString "stride" = ofString "key_len") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem nm14 : (ofString "stride" = ofString "cap") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem nm15 : (ofString "ncap" = ofString "t") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem nm16 : (ofString "ncap" = ofString "stride") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem nm17 : (ofString "ncap" = ofString "keys") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem nm18 : (ofString "ncap" = ofString "nodes") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem nm19 : (ofString "ncap" = ofString "order") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem nm20 : (ofString "ncap" = ofString "key_len") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem nm21 : (ofString "ncap" = ofString "cap") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem nm22 : (ofString "keys" = ofString "t") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem nm23 : (ofString "keys" = ofString "stride") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem nm24 : (ofString "keys" = ofString "ncap") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem nm25 : (ofString "keys" = ofString "nodes") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem nm26 : (ofString "keys" = ofString "order") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem nm27 : (ofString "keys" = ofString "key_len") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem nm28 : (ofString "keys" = ofString "cap") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem nm29 : (ofString "nodes" = ofString "t") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem nm30 : (ofString "nodes" = ofString "stride") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem nm31 : (ofString "nodes" = ofString "ncap") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem nm32 : (ofString "nodes" = ofString "keys") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem nm33 : (ofString "nodes" = ofString "order") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem nm34 : (ofString "nodes" = ofString "key_len") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem nm35 : (ofString "nodes" = ofString "cap") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem nm36 : (ofString "order" = ofString "t") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem nm37 : (ofString "order" = ofString "stride") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem nm38 : (ofString "order" = ofString "ncap") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem nm39 : (ofString "order" = ofString "keys") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem nm40 : (ofString "order" = ofString "nodes") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem nm41 : (ofString "order" = ofString "key_len") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem nm42 : (ofString "order" = ofString "cap") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem nm43 : (ofString "heap_ptr" = ofString "scratch_ptr") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem nm44 : (ofString "scratch_ptr" = ofString "heap_ptr") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem nm45 : (ofString "heap_ptr" = ofString "frame_mem_ptr") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem nm46 : (ofString "frame_mem_ptr" = ofString "heap_ptr") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem nm47 : (ofString "scratch_ptr" = ofString "frame_mem_ptr") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem nm48 : (ofString "frame_mem_ptr" = ofString "scratch_ptr") = False := by simp only [eq_iff_iff, iff_false]; decide
end NewNames

/-! ## 2. Ordinary domain characterization and `scratch_alloc` semantics -/

theorem addresses_iff (b : BitVec 64) (n : Nat) (x : BitVec 64) :
    Flapjack.Compiler.Backend.StackRemove.addresses b n x ↔ ∃ i, i < n ∧ x = b + BitVec.ofNat 64 (8 * i) := by
  induction n generalizing b with
  | zero => simp [Flapjack.Compiler.Backend.StackRemove.addresses]
  | succ n ih =>
    simp only [Flapjack.Compiler.Backend.StackRemove.addresses, Flapjack.Compiler.Backend.StackRemove.bytesInWord]
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
    ordinaryDomain x ↔ 2701131776 ≤ x.toNat ∧ x.toNat < 2701131776 + 8 * 3888119741 ∧
      x.toNat % 8 = 0 := by
  have hb : (BitVec.ofNat 64 2701131776).toNat = 2701131776 := rfl
  rw [ordinaryDomain_eq, addresses_iff_nat _ _ (by rw [hb]; norm_num), hb]
  omega

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
          evaluateHOLFiniteState_return]
      rw [heval_end]
      intro retVal hret
      injection hret with hr
      injection hr with hr'
      exact ⟨hr'.symm, hcmp1, hcmp2, rfl⟩

theorem decCall_scratch_alloc {F : Type} {s : PanSemStateFiniteExact 64 F} {x : MlS}
    {arg : ExpHOL 64} {cont : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hcode : s.code = originalRuntimeCode) (nv : BitVec 64)
    (harg : ev s arg = some (.val (.word nv))) (p f : BitVec 64)
    (hp : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word p)))
    (hf : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word f)))
    (hk : ¬ ((p - f).toNat < nv.toNat) →
      ¬ (((p - nv) &&& ((0 : BitVec 64) - 8)).toNat < f.toNat) →
      Ret (setVarHOLFinite x (.val (.word ((p - nv) &&& ((0 : BitVec 64) - 8)))) { s with
          globals := (s.globals.update (ofString "scratch_ptr",
            .val (.word ((p - nv) &&& ((0 : BitVec 64) - 8)))))
          clock := s.clock - 1 }) cont
        (fun v t => Φ v { t with
          locals := HolFiniteMapExact.resVarEq t.locals (x, s.locals.lookup x) })) :
    Ret s (.decCall x .one (ofString "scratch_alloc") [arg] cont) Φ := by
  refine Ret.decCall1 hcode lookup_scratch_alloc nv harg ?_
  intro w post hrun
  have hn : (callEntryStateHOLFinite s
      (HolFiniteMapExact.empty.update (ofString "n", .val (.word nv)))).locals.lookup (ofString "n") =
      some (.val (.word nv)) := by
    simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have := scratch_alloc_body_run (callEntryStateHOLFinite s
    (HolFiniteMapExact.empty.update (ofString "n", .val (.word nv)))) p f nv hcode hp hf hn
    (.val (.word w)) (by rw [hrun])
  rw [hrun] at this
  obtain ⟨hw, h1, h2, hpost⟩ := this
  simp only [ValueHOL.val.injEq, HolWordLab.word.injEq] at hw
  subst hw
  have hst : { post with locals := s.locals } = { s with
      globals := (s.globals.update (ofString "scratch_ptr",
        .val (.word ((p - nv) &&& ((0 : BitVec 64) - 8)))))
      clock := s.clock - 1 } := by
    dsimp only at hpost
    rw [hpost]; rfl
  rw [hst]
  exact hk h1 h2

theorem ns_scratch_alloc {F : Type} {s : PanSemStateFiniteExact 64 F} {L G} {M C} {x : MlS}
    {arg : ExpHOL 64} {cont : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hcode : s.code = originalRuntimeCode) (nv : BitVec 64)
    (harg : ev (NS s L G M C) arg = some (.val (.word nv))) (p f : BitVec 64)
    (hp : G.lookup (ofString "scratch_ptr") = some (.val (.word p)))
    (hf : G.lookup (ofString "frame_mem_ptr") = some (.val (.word f)))
    (hk : ¬ ((p - f).toNat < nv.toNat) →
      ¬ (((p - nv) &&& ((0 : BitVec 64) - 8)).toNat < f.toNat) →
      Ret (NS s (L.update (x, .val (.word ((p - nv) &&& ((0 : BitVec 64) - 8)))))
          (G.update (ofString "scratch_ptr", .val (.word ((p - nv) &&& ((0 : BitVec 64) - 8)))))
          M (C - 1)) cont
        (fun v t => Φ v { t with locals := HolFiniteMapExact.resVarEq t.locals (x, L.lookup x) })) :
    Ret (NS s L G M C) (.decCall x .one (ofString "scratch_alloc") [arg] cont) Φ :=
  decCall_scratch_alloc hcode nv harg p f hp hf hk

theorem seq_ite_true {F : Type} {s : PanSemStateFiniteExact 64 F} {c : ExpHOL 64}
    {y n b : ProgHOL 64} {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (w : BitVec 64) (hc : ev s c = some (.val (.word w))) (hw : w ≠ 0)
    (hy : Ret s (.seq y b) Φ) :
    Ret s (.seq (.ite c y n) b) Φ := by
  have : evaluateHOLFiniteState s (.ite c y n) = evaluateHOLFiniteState s y := by
    rw [evaluateHOLFiniteState_ite]
    simp only [ev] at hc
    rw [hc]
    dsimp only
    rw [if_neg hw]
  intro v hv
  rw [evaluateHOLFiniteState_seq_line780, this] at hv ⊢
  have := hy v (by rw [evaluateHOLFiniteState_seq_line780]; exact hv)
  rw [evaluateHOLFiniteState_seq_line780] at this
  exact this

theorem ns_ite_true_assign {F : Type} {s : PanSemStateFiniteExact 64 F} {L G} {M C}
    {c e : ExpHOL 64} {x : MlS} {b : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (w : BitVec 64) (hc : ev (NS s L G M C) c = some (.val (.word w))) (hw : w ≠ 0)
    (u v0 : BitVec 64) (hx : L.lookup x = some (.val (.word v0)))
    (he : ev (NS s L G M C) e = some (.val (.word u)))
    (hb : Ret (NS s (L.update (x, .val (.word u))) G M C) b Φ) :
    Ret (NS s L G M C) (.seq (.ite c (.assign .local x e) .skip) b) Φ := by
  refine seq_ite_true w hc hw (Ret.seq ?_ ?_)
  · intro rv hrv
    rw [evaluateHOLFiniteState_assign] at hrv
    revert hrv
    split
    · simp
    · split <;> simp
  · intro t ht
    rw [evaluateHOLFiniteState_assign] at ht
    simp only [ev] at he
    rw [he] at ht
    dsimp only at ht
    have hval : (NS s L G M C).isValidValueHOLFinite .local x (.val (.word u)) = true := by
      simp [PanSemStateFiniteExact.isValidValueHOLFinite, lookupKvarHOLExact,
        hx, shapeOfHOLExact, shapeEqHOL]
    rw [if_pos hval] at ht
    cases ht
    exact hb

/-! ## 3. Empty table construction on scratch (`new_core_scratch` on R11) -/

theorem and_neg8_toNat_htab (w : BitVec 64) :
    (w &&& ((0 : BitVec 64) - 8)).toNat = w.toNat / 8 * 8 :=
  InitECandidate.Solver.GuestTrapAndLookup.and_neg8_toNat w

def hdrMem (m : BitVec 64 → HolWordLab 64) (t k st cap ncap q1 q2 q3 : BitVec 64) :
    BitVec 64 → HolWordLab 64 :=
  updW (updW (updW (updW (updW (updW (updW (updW (updW (updW (updW m
    (t + 0) k) (t + 8) st) (t + 16) cap) (t + 24) 0) (t + 32) q1) (t + 40) q2) (t + 48) q3)
    (t + 56) 0) (t + 64) 1) (t + 72) 0) (t + 80) ncap

theorem ofNat_add_toNat (t : BitVec 64) (n : Nat) :
    BitVec.ofNat 64 (t.toNat + n) = t + BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, BitVec.toNat_ofNat]

theorem hdrMem_read (m : BitVec 64 → HolWordLab 64) (t k st cap ncap q1 q2 q3 : BitVec 64) :
    (hdrMem m t k st cap ncap q1 q2 q3 (BitVec.ofNat 64 (t.toNat + 0)) = .word k) ∧
    (hdrMem m t k st cap ncap q1 q2 q3 (BitVec.ofNat 64 (t.toNat + 8)) = .word st) ∧
    (hdrMem m t k st cap ncap q1 q2 q3 (BitVec.ofNat 64 (t.toNat + 16)) = .word cap) ∧
    (hdrMem m t k st cap ncap q1 q2 q3 (BitVec.ofNat 64 (t.toNat + 24)) = .word 0) ∧
    (hdrMem m t k st cap ncap q1 q2 q3 (BitVec.ofNat 64 (t.toNat + 32)) = .word q1) ∧
    (hdrMem m t k st cap ncap q1 q2 q3 (BitVec.ofNat 64 (t.toNat + 40)) = .word q2) ∧
    (hdrMem m t k st cap ncap q1 q2 q3 (BitVec.ofNat 64 (t.toNat + 48)) = .word q3) ∧
    (hdrMem m t k st cap ncap q1 q2 q3 (BitVec.ofNat 64 (t.toNat + 56)) = .word 0) ∧
    (hdrMem m t k st cap ncap q1 q2 q3 (BitVec.ofNat 64 (t.toNat + 64)) = .word 1) ∧
    (hdrMem m t k st cap ncap q1 q2 q3 (BitVec.ofNat 64 (t.toNat + 72)) = .word 0) ∧
    (hdrMem m t k st cap ncap q1 q2 q3 (BitVec.ofNat 64 (t.toNat + 80)) = .word ncap) := by
  simp only [ofNat_add_toNat, hdrMem, updW]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp

theorem hdrMem_out (m : BitVec 64 → HolWordLab 64) (t k st cap ncap q1 q2 q3 : BitVec 64)
    (ht : t.toNat + 88 ≤ 2 ^ 64) (a : BitVec 64) (ha : ¬ (t.toNat ≤ a.toNat ∧ a.toNat < t.toNat + 88)) :
    hdrMem m t k st cap ncap q1 q2 q3 a = m a := by
  have hne : ∀ j : Nat, j < 88 → a ≠ t + BitVec.ofNat 64 j := by
    intro j hj h
    apply ha
    subst h
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have h0 : a ≠ t + 0 := hne 0 (by omega)
  have h8 : a ≠ t + 8 := hne 8 (by omega)
  have h16 : a ≠ t + 16 := hne 16 (by omega)
  have h24 : a ≠ t + 24 := hne 24 (by omega)
  have h32 : a ≠ t + 32 := hne 32 (by omega)
  have h40 : a ≠ t + 40 := hne 40 (by omega)
  have h48 : a ≠ t + 48 := hne 48 (by omega)
  have h56 : a ≠ t + 56 := hne 56 (by omega)
  have h64 : a ≠ t + 64 := hne 64 (by omega)
  have h72 : a ≠ t + 72 := hne 72 (by omega)
  have h80 : a ≠ t + 80 := hne 80 (by omega)
  simp only [hdrMem, updW, h0, h8, h16, h24, h32, h40, h48, h56, h64, h72, h80, ↓reduceIte]

theorem new_params (k c : BitVec 64) (hk : k.toNat ∈ htabKeyLens)
    (hc2 : 2 ≤ c.toNat) (hcmax : c.toNat ≤ htabCapMax) :
    ((k + 7) &&& 18446744073709551608#64).toNat = (k.toNat + 7) / 8 * 8 ∧
    ((k + 7) &&& 18446744073709551608#64).toNat % 8 = 0 ∧
    ((k + 7) &&& 18446744073709551608#64).toNat ≤ 64 ∧
    ((c + 1) * ((k + 7) &&& 18446744073709551608#64)).toNat =
      (c.toNat + 1) * ((k + 7) &&& 18446744073709551608#64).toNat ∧
    ((c + 1) * 32).toNat = (c.toNat + 1) * 32 ∧ ((c + 1) * 8).toNat = (c.toNat + 1) * 8 ∧
    2 ≤ c.toNat ∧ c.toNat ≤ htabCapMax ∧ 1 ≤ k.toNat ∧ k.toNat ≤ 60 := by
  obtain ⟨kn, hkn, rfl⟩ : ∃ kn ∈ htabKeyLens, k = BitVec.ofNat 64 kn := ⟨k.toNat, hk, by simp⟩
  have hclt : c.toNat ≤ 2 ^ 32 := by simpa [htabCapMax] using hcmax
  have hc1 : (c + 1).toNat = c.toNat + 1 := by
    simp only [BitVec.toNat_add]
    have : (1 : BitVec 64).toNat = 1 := rfl
    rw [this]; omega
  have hm2 : ((c + 1) * 32).toNat = (c.toNat + 1) * 32 := by
    rw [BitVec.toNat_mul, hc1]
    have : (32 : BitVec 64).toNat = 32 := rfl
    rw [this]; omega
  have hm3 : ((c + 1) * 8).toNat = (c.toNat + 1) * 8 := by
    rw [BitVec.toNat_mul, hc1]
    have : (8 : BitVec 64).toNat = 8 := rfl
    rw [this]; omega
  simp only [htabKeyLens, List.mem_cons, List.not_mem_nil, or_false] at hkn
  rcases hkn with rfl | rfl | rfl | rfl | rfl
  · have hm1 : ((c + 1) * ((BitVec.ofNat 64 20 + 7) &&& 18446744073709551608#64)).toNat =
        (c.toNat + 1) * ((BitVec.ofNat 64 20 + 7) &&& 18446744073709551608#64).toNat := by
      have hs : ((BitVec.ofNat 64 20 + 7) &&& 18446744073709551608#64) = 24#64 := by decide
      rw [hs, BitVec.toNat_mul, hc1]
      have : (24#64).toNat = 24 := rfl
      rw [this]; omega
    exact ⟨by decide, by decide, by decide, hm1, hm2, hm3, hc2, hcmax, by decide, by decide⟩
  · have hm1 : ((c + 1) * ((BitVec.ofNat 64 28 + 7) &&& 18446744073709551608#64)).toNat =
        (c.toNat + 1) * ((BitVec.ofNat 64 28 + 7) &&& 18446744073709551608#64).toNat := by
      have hs : ((BitVec.ofNat 64 28 + 7) &&& 18446744073709551608#64) = 32#64 := by decide
      rw [hs, BitVec.toNat_mul, hc1]
      have : (32#64).toNat = 32 := rfl
      rw [this]; omega
    exact ⟨by decide, by decide, by decide, hm1, hm2, hm3, hc2, hcmax, by decide, by decide⟩
  · have hm1 : ((c + 1) * ((BitVec.ofNat 64 32 + 7) &&& 18446744073709551608#64)).toNat =
        (c.toNat + 1) * ((BitVec.ofNat 64 32 + 7) &&& 18446744073709551608#64).toNat := by
      have hs : ((BitVec.ofNat 64 32 + 7) &&& 18446744073709551608#64) = 32#64 := by decide
      rw [hs, BitVec.toNat_mul, hc1]
      have : (32#64).toNat = 32 := rfl
      rw [this]; omega
    exact ⟨by decide, by decide, by decide, hm1, hm2, hm3, hc2, hcmax, by decide, by decide⟩
  · have hm1 : ((c + 1) * ((BitVec.ofNat 64 52 + 7) &&& 18446744073709551608#64)).toNat =
        (c.toNat + 1) * ((BitVec.ofNat 64 52 + 7) &&& 18446744073709551608#64).toNat := by
      have hs : ((BitVec.ofNat 64 52 + 7) &&& 18446744073709551608#64) = 56#64 := by decide
      rw [hs, BitVec.toNat_mul, hc1]
      have : (56#64).toNat = 56 := rfl
      rw [this]; omega
    exact ⟨by decide, by decide, by decide, hm1, hm2, hm3, hc2, hcmax, by decide, by decide⟩
  · have hm1 : ((c + 1) * ((BitVec.ofNat 64 60 + 7) &&& 18446744073709551608#64)).toNat =
        (c.toNat + 1) * ((BitVec.ofNat 64 60 + 7) &&& 18446744073709551608#64).toNat := by
      have hs : ((BitVec.ofNat 64 60 + 7) &&& 18446744073709551608#64) = 64#64 := by decide
      rw [hs, BitVec.toNat_mul, hc1]
      have : (64#64).toNat = 64 := rfl
      rw [this]; omega
    exact ⟨by decide, by decide, by decide, hm1, hm2, hm3, hc2, hcmax, by decide, by decide⟩

def NewPost {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (post : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ w : BitVec 64, v = .val (.word w) ∧
    ArenaReady post ∧ AllocatorGrows s post ∧ HtabWF post w.toNat ∧ hdr post w.toNat 3 = 0 ∧
    hdr post w.toNat 0 = locN s "key_len" ∧
    (∀ i ∈ htabFootprint post w.toNat, Allocated post i ∧
      (Inside i (globN s "heap_ptr") (globN post "heap_ptr") ∨
        Inside i (globN post "scratch_ptr") (globN s "scratch_ptr"))) ∧
    FrameOutside s post
      [(globN post "scratch_ptr", globN s "scratch_ptr" - globN post "scratch_ptr")]
      (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr") ∧
    ∀ k : MlS, k ∉ (["heap_ptr", "scratch_ptr"] : List String).map ofString →
      s.globals.lookup k = post.globals.lookup k

theorem hdr_hdrMem {F : Type} (post : PanSemStateFiniteExact 64 F) (m : BitVec 64 → HolWordLab 64)
    (t k st cap ncap q1 q2 q3 : BitVec 64) (hM : post.memory = hdrMem m t k st cap ncap q1 q2 q3) :
    hdr post t.toNat 0 = k.toNat ∧ hdr post t.toNat 1 = st.toNat ∧
    hdr post t.toNat 2 = cap.toNat ∧ hdr post t.toNat 3 = 0 ∧
    hdr post t.toNat 4 = q1.toNat ∧ hdr post t.toNat 5 = q2.toNat ∧
    hdr post t.toNat 6 = q3.toNat ∧ hdr post t.toNat 7 = 0 ∧
    hdr post t.toNat 8 = 1 ∧ hdr post t.toNat 9 = 0 ∧ hdr post t.toNat 10 = ncap.toNat := by
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10⟩ := hdrMem_read m t k st cap ncap q1 q2 q3
  simp only [hdr, memW, hM]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show t.toNat + 8 * 0 = t.toNat + 0 by omega, r0]
  · rw [show t.toNat + 8 * 1 = t.toNat + 8 by omega, r1]
  · rw [show t.toNat + 8 * 2 = t.toNat + 16 by omega, r2]
  · rw [show t.toNat + 8 * 3 = t.toNat + 24 by omega, r3]; rfl
  · rw [show t.toNat + 8 * 4 = t.toNat + 32 by omega, r4]
  · rw [show t.toNat + 8 * 5 = t.toNat + 40 by omega, r5]
  · rw [show t.toNat + 8 * 6 = t.toNat + 48 by omega, r6]
  · rw [show t.toNat + 8 * 7 = t.toNat + 56 by omega, r7]; rfl
  · rw [show t.toNat + 8 * 8 = t.toNat + 64 by omega, r8]; rfl
  · rw [show t.toNat + 8 * 9 = t.toNat + 72 by omega, r9]; rfl
  · rw [show t.toNat + 8 * 10 = t.toNat + 80 by omega, r10]

theorem wordAt_of_dom {F : Type} (post : PanSemStateFiniteExact 64 F)
    (hma : post.memaddrs = ordinaryDomain) (a : Nat) (h1 : 2701131776 ≤ a)
    (h2 : a < 2701131776 + 8 * 3888119741) (h3 : a % 8 = 0) : WordAt post a := by
  have ha : (BitVec.ofNat 64 a).toNat = a := by
    simp only [BitVec.toNat_ofNat]; omega
  rcases hw : post.memory (BitVec.ofNat 64 a) with ⟨w⟩
  refine ⟨w, ?_, hw⟩
  rw [hma, ordinaryDomain_iff, ha]
  exact ⟨h1, h2, h3⟩

theorem wordsOK_block {F : Type} (post : PanSemStateFiniteExact 64 F)
    (hma : post.memaddrs = ordinaryDomain) (b l : Nat) (hb : b % 8 = 0) (hl : l % 8 = 0)
    (h1 : 2701131776 ≤ b) (h2 : b + l ≤ 2965299200) : WordsOK post (b, l) := by
  refine ⟨hb, hl, fun j hj => wordAt_of_dom post hma _ (by omega) (by simp at hj; omega) (by omega)⟩

theorem htabWF_empty {F : Type} (post : PanSemStateFiniteExact 64 F) (t : Nat)
    (hma : post.memaddrs = ordinaryDomain)
    (kn stn cn b1 b2 b3 : Nat)
    (h0 : hdr post t 0 = kn) (h1 : hdr post t 1 = stn) (h3 : hdr post t 3 = 0)
    (h4 : hdr post t 4 = b1) (h5 : hdr post t 5 = b2) (h6 : hdr post t 6 = b3)
    (h7 : hdr post t 7 = 0) (h8 : hdr post t 8 = 1) (h9 : hdr post t 9 = 0)
    (h10 : hdr post t 10 = cn)
    (hk1 : 1 ≤ kn) (hk2 : kn ≤ 60) (hst : stn = (kn + 7) / 8 * 8) (hc : 2 ≤ cn)
    (ht8 : t % 8 = 0) (h18 : b1 % 8 = 0) (h28 : b2 % 8 = 0) (h38 : b3 % 8 = 0)
    (htlo : 2701131776 ≤ t) (h1lo : 2701131776 ≤ b1) (h2lo : 2701131776 ≤ b2)
    (h3lo : 2701131776 ≤ b3)
    (hthi : t + 88 ≤ 2965299200) (h1hi : b1 + (cn + 1) * stn ≤ 2965299200)
    (h2hi : b2 + (cn + 1) * 32 ≤ 2965299200) (h3hi : b3 + (cn + 1) * 8 ≤ 2965299200)
    (hdisj : ((t + 88 ≤ b1 ∨ b1 + (cn + 1) * stn ≤ t) ∧
      (t + 88 ≤ b2 ∨ b2 + (cn + 1) * 32 ≤ t) ∧ (t + 88 ≤ b3 ∨ b3 + (cn + 1) * 8 ≤ t)) ∧
      ((b1 + (cn + 1) * stn ≤ b2 ∨ b2 + (cn + 1) * 32 ≤ b1) ∧
        (b1 + (cn + 1) * stn ≤ b3 ∨ b3 + (cn + 1) * 8 ≤ b1)) ∧
      (b2 + (cn + 1) * 32 ≤ b3 ∨ b3 + (cn + 1) * 8 ≤ b2)) :
    HtabWF post t := by
  have hst8 : stn % 8 = 0 := by omega
  have hL1 : ((cn + 1) * stn) % 8 = 0 := by
    rw [Nat.mul_mod, hst8]; simp
  have hL2 : ((cn + 1) * 32) % 8 = 0 := by omega
  have hL3 : ((cn + 1) * 8) % 8 = 0 := by omega
  unfold HtabWF htabFootprint
  simp only [h0, h1, h3, h4, h5, h6, h7, h8, h9, h10]
  refine ⟨?_, ?_, hk1, hk2, hst, hc, le_refl _, by omega, [], [], [], by simp, by simp,
    fun n => by simp; omega, by simp, fun i hi => by simp at hi,
    fun n hn => by simp at hn, by simp, fun h => by omega, fun n hn => by simp at hn,
    fun n hn => by simp at hn, ⟨fun _ => 0, fun n hn => by simp at hn⟩, by simp [FreeChain]⟩
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact ⟨⟨by unfold sourceBase; omega, by unfold heapEnd stackStart ramEnd ramStart ramSize stackSize globalsWords; omega⟩,
        wordsOK_block post hma _ _ ht8 (by omega) htlo (by omega)⟩
    · exact ⟨⟨by unfold sourceBase; omega, by unfold heapEnd stackStart ramEnd ramStart ramSize stackSize globalsWords; omega⟩,
        wordsOK_block post hma _ _ (by omega) hL1 (by omega) (by omega)⟩
    · exact ⟨⟨by unfold sourceBase; omega, by unfold heapEnd stackStart ramEnd ramStart ramSize stackSize globalsWords; omega⟩,
        wordsOK_block post hma _ _ (by omega) hL2 (by omega) (by omega)⟩
    · exact ⟨⟨by unfold sourceBase; omega, by unfold heapEnd stackStart ramEnd ramStart ramSize stackSize globalsWords; omega⟩,
        wordsOK_block post hma _ _ (by omega) hL3 (by omega) (by omega)⟩
  · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, List.Pairwise.nil, and_true, Disj]
    exact ⟨⟨Or.inr (Or.inr hdisj.1.1), Or.inr (Or.inr hdisj.1.2.1), Or.inr (Or.inr hdisj.1.2.2)⟩,
      ⟨Or.inr (Or.inr hdisj.2.1.1), Or.inr (Or.inr hdisj.2.1.2)⟩,
      Or.inr (Or.inr hdisj.2.2), fun _ h => h.elim⟩

theorem round8_down (x y : BitVec 64) (f : Nat) (hf : f ≤ x.toNat)
    (hno : ¬ ((x - BitVec.ofNat 64 f).toNat < y.toNat)) :
    y.toNat ≤ x.toNat - f ∧
      ((x - y) &&& ((0 : BitVec 64) - 8)).toNat = (x.toNat - y.toNat) / 8 * 8 := by
  have hfl : f < 2 ^ 64 := by have := x.isLt; omega
  have hsub : (x - BitVec.ofNat 64 f).toNat = x.toNat - f := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfl]
    have := x.isLt
    omega
  rw [hsub] at hno
  refine ⟨by omega, ?_⟩
  rw [and_neg8_toNat_htab, BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega)]

theorem new_core_scratch {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (k cap c sp f r1 r2 r3 r4 : BitVec 64)
    (hAR : ArenaReady s) (hkl : k.toNat ∈ htabKeyLens)
    (hcap2 : 2 ≤ c.toNat) (hcapmax : c.toNat ≤ htabCapMax)
    (hkey : s.locals.lookup (ofString "key_len") = some (.val (.word k)))
    (hsp : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word sp)))
    (hfp : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word f)))
    (hR1 : (sp - 88) &&& ((0 : BitVec 64) - 8) = r1)
    (hc1 : ¬ ((sp - f).toNat < (88 : BitVec 64).toNat)) (_hd1 : ¬ (r1.toNat < f.toNat))
    (hR2 : (r1 - (c + 1) * ((k + 7) &&& 18446744073709551608#64)) &&& ((0 : BitVec 64) - 8) = r2)
    (hc2 : ¬ ((r1 - f).toNat < ((c + 1) * ((k + 7) &&& 18446744073709551608#64)).toNat))
    (_hd2 : ¬ (r2.toNat < f.toNat))
    (hR3 : (r2 - (c + 1) * 32) &&& ((0 : BitVec 64) - 8) = r3)
    (hc3 : ¬ ((r2 - f).toNat < ((c + 1) * 32).toNat)) (_hd3 : ¬ (r3.toNat < f.toNat))
    (hR4 : (r3 - (c + 1) * 8) &&& ((0 : BitVec 64) - 8) = r4)
    (hc4' : ¬ ((r3 - f).toNat < ((c + 1) * 8).toNat)) (hd4 : ¬ (r4.toNat < f.toNat))
    (hM : post.memory = hdrMem s.memory r1 k ((k + 7) &&& 18446744073709551608#64) cap c r2 r3 r4)
    (hG : post.globals = (((s.globals.update (ofString "scratch_ptr", .val (.word r1))).update
      (ofString "scratch_ptr", .val (.word r2))).update (ofString "scratch_ptr", .val (.word r3))).update
      (ofString "scratch_ptr", .val (.word r4)))
    (hGI : GuestInv post) :
    NewPost s (.val (.word r1)) post := by
  obtain ⟨hst, hst8, hst64, hL1, hL2, hL3, _, _, hk1, hk60⟩ := new_params k c hkl hcap2 hcapmax
  set st := (k + 7) &&& 18446744073709551608#64
  obtain ⟨hgis, hlo, hhi, hf1, hf2, hf3, ha_hp, ha_fm, ha_sp, hgw_s⟩ := hAR
  have hgsp : globN s "scratch_ptr" = sp.toNat := by simp [globN, hsp]
  have hgf : globN s "frame_mem_ptr" = f.toNat := by simp [globN, hfp]
  have hss : scratchStart = 2952790016 := rfl
  have hse : scratchEnd = 2965299200 := rfl
  rw [hgf, hss] at hf1
  rw [hgf, hgsp] at hf2
  rw [hgsp, hse] at hf3
  rw [hgsp] at ha_sp
  have hfeq : f = BitVec.ofNat 64 f.toNat := by simp
  have h88 : (88 : BitVec 64).toNat = 88 := rfl
  rw [hfeq] at hc1 hc2 hc3 hc4'
  obtain ⟨b1, e1⟩ := round8_down sp 88 f.toNat (by omega) hc1
  rw [h88] at b1 e1
  rw [hR1] at e1
  obtain ⟨b2, e2⟩ := round8_down r1 _ f.toNat (by omega) hc2
  rw [hR2, hL1] at e2
  rw [hL1] at b2
  obtain ⟨b3, e3⟩ := round8_down r2 _ f.toNat (by omega) hc3
  rw [hR3, hL2] at e3
  rw [hL2] at b3
  obtain ⟨b4, e4⟩ := round8_down r3 _ f.toNat (by omega) hc4'
  rw [hR4, hL3] at e4
  rw [hL3] at b4
  have hcN : c.toNat ≤ 4294967296 := by simpa [htabCapMax] using hcapmax
  have hL1m : ((c.toNat + 1) * st.toNat) % 8 = 0 := by rw [Nat.mul_mod, hst8]; simp
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10⟩ := hdr_hdrMem post s.memory r1 k st cap c r2 r3 r4 hM
  have hgpost : globN post "scratch_ptr" = r4.toNat := by
    simp [globN, hG, HolFiniteMapExact.lookup_update, FUPDATE]
  have hhp : globN post "heap_ptr" = globN s "heap_ptr" := by
    simp [globN, hG, HolFiniteMapExact.lookup_update, FUPDATE, nm44]
  have hfm : globN post "frame_mem_ptr" = f.toNat := by
    rw [← hgf]; simp [globN, hG, HolFiniteMapExact.lookup_update, FUPDATE, nm47]
  have hr4align : r4.toNat % 8 = 0 := by omega
  refine ⟨r1, rfl, ?_, ?_, ?_, d3, ?_, ?_, ?_, ?_⟩
  · refine ⟨hGI, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hhp]; exact hlo
    · rw [hhp]; exact hhi
    · rw [hfm, hss]; exact hf1
    · rw [hfm, hgpost]; omega
    · rw [hgpost, hse]; omega
    · rw [hhp]; exact ha_hp
    · rw [hfm, ← hgf]; exact ha_fm
    · rw [hgpost]; exact hr4align
    · intro n hn
      by_cases hk' : ofString "scratch_ptr" = ofString n
      · exact ⟨r4, by unfold GlobalWord; rw [hG]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hk']⟩
      · obtain ⟨w', hw'⟩ := hgw_s n hn
        exact ⟨w', by unfold GlobalWord at hw' ⊢; rw [hG]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hk', hw']⟩
  · exact ⟨by rw [hhp], by rw [hgpost, hgsp]; omega⟩
  · exact htabWF_empty post r1.toNat hGI.memaddrs k.toNat st.toNat c.toNat r2.toNat r3.toNat
      r4.toNat d0 d1 d3 d4 d5 d6 d7 d8 d9 d10 hk1 hk60 hst (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)
  · rw [d0]; simp [locN, hkey]
  · intro i hi
    simp only [htabFootprint, d1, d4, d5, d6, d10, List.mem_cons, List.not_mem_nil, or_false] at hi
    have hA : ∀ b l : Nat, r4.toNat ≤ b → b + l ≤ sp.toNat →
        Allocated post (b, l) ∧ (Inside (b, l) (globN s "heap_ptr") (globN post "heap_ptr") ∨
          Inside (b, l) (globN post "scratch_ptr") (globN s "scratch_ptr")) := by
      intro b l h1 h2
      exact ⟨Or.inr ⟨by rw [hgpost]; exact h1, by rw [hse]; omega⟩,
        Or.inr ⟨by rw [hgpost]; exact h1, by rw [hgsp]; exact h2⟩⟩
    rcases hi with rfl | rfl | rfl | rfl <;> refine hA _ _ ?_ ?_ <;> omega
  · intro a hkeep _
    rw [hM]
    apply hdrMem_out _ _ _ _ _ _ _ _ _ (by omega)
    intro hin
    have hk0 := hkeep _ (List.mem_singleton.2 rfl)
    apply hk0
    simp only [CellHits, hgpost, hgsp]
    omega
  · intro kname hkname
    simp only [List.map, List.mem_cons, List.not_mem_nil, or_false] at hkname
    have hne : ofString "scratch_ptr" ≠ kname := fun he => hkname (Or.inr he.symm)
    simp [hG, HolFiniteMapExact.lookup_update, FUPDATE, hne]

/-! ## 4. Symbolic run of `htab_new_scratch` -/

local macro "evs" : tactic => `(tactic| ((simp [ev, evalHOLExact, evalListHOLExact,
  HolFiniteMapExact.lookup_update, FUPDATE, wordOpHOL, wordOp, valueIsWord, valueWord,
  nm1, nm2, nm3, nm4, nm5, nm6, nm7, nm8, nm9, nm10, nm11, nm12, nm13, nm14, nm15, nm16,
  nm17, nm18, nm19, nm20, nm21, nm22, nm23, nm24, nm25, nm26, nm27, nm28, nm29, nm30, nm31,
  nm32, nm33, nm34, nm35, nm36, nm37, nm38, nm39, nm40, nm41, nm42, nm43, nm44, nm45, nm46,
  nm47, nm48]) <;>
  first | assumption | rfl))

local macro "st_step" a:term:max w:term:max : tactic =>
  `(tactic| (apply Ret.ns_storeW $a $w (by evs) (by evs); intro _))

attribute [local irreducible] Ret in
theorem htab_new_scratch_run {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) (k cap p0 f : BitVec 64)
    (hk : s.locals.lookup (ofString "key_len") = some (.val (.word k)))
    (hc : s.locals.lookup (ofString "cap") = some (.val (.word cap)))
    (hp : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word p0)))
    (hf : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word f)))
    (hAR : ArenaReady s) (hkl : k.toNat ∈ htabKeyLens) (hcl : cap.toNat ≤ htabCapMax) :
    Ret s (sourceFnBody Guest.Software.guestFn_htab_new_scratch) (NewPost s) := by
  have hb : sourceFnBody Guest.Software.guestFn_htab_new_scratch =
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_htab_new_scratch).body := rfl
  rw [hb]
  dsimp only [extractFn, Guest.Software.guestFn_htab_new_scratch,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural, List.map, Option.map]
  apply Ret.of_NS
  apply ns_scratch_alloc hcode 88 (by evs) p0 f hp hf
  intro hc1 hd1
  generalize hQ1 : (p0 - 88) &&& ((0 : BitVec 64) - 8) = q1 at *
  apply Ret.ns_dec
  intro stride hstride
  simp [ev, evalHOLExact, evalListHOLExact, HolFiniteMapExact.lookup_update,
    FUPDATE, hk, nm6, wordOpHOL, wordOp, valueIsWord, valueWord] at hstride
  generalize hS : (k + 7) &&& 18446744073709551608#64 = st at hstride
  subst hstride
  apply Ret.ns_dec
  intro ncap hncap
  simp [ev, evalHOLExact, HolFiniteMapExact.lookup_update, FUPDATE, hc, nm7, nm14] at hncap
  subst hncap
  by_cases hc2 : cap.toNat < 2
  · apply ns_ite_true_assign 1
      (by simp [ev, evalHOLExact, HolFiniteMapExact.lookup_update, FUPDATE,
            Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def]; omega)
      (by decide) 2 cap (by evs) (by evs)
    st_step (q1 + 0) k
    st_step (q1 + 8) st
    st_step (q1 + 16) cap
    st_step (q1 + 24) 0
    apply ns_scratch_alloc hcode (((2 : BitVec 64) + 1) * st) (by evs) q1 f (by evs) (by evs)
    intro hc2' hd2
    generalize hQ2 : (q1 - ((2 : BitVec 64) + 1) * st) &&& ((0 : BitVec 64) - 8) = q2 at *
    st_step (q1 + 32) q2
    apply ns_scratch_alloc hcode (((2 : BitVec 64) + 1) * 32) (by evs) q2 f (by evs) (by evs)
    intro hc3 hd3
    generalize hQ3 : (q2 - ((2 : BitVec 64) + 1) * 32) &&& ((0 : BitVec 64) - 8) = q3 at *
    st_step (q1 + 40) q3
    apply ns_scratch_alloc hcode (((2 : BitVec 64) + 1) * 8) (by evs) q3 f (by evs) (by evs)
    intro hc4' hd4
    generalize hQ4 : (q3 - ((2 : BitVec 64) + 1) * 8) &&& ((0 : BitVec 64) - 8) = q4 at *
    st_step (q1 + 48) q4
    st_step (q1 + 56) 0
    st_step (q1 + 64) 1
    st_step (q1 + 72) 0
    st_step (q1 + 80) 2
    apply Ret.ns_ret
    intro val hval
    simp [ev, evalHOLExact, HolFiniteMapExact.lookup_update, FUPDATE, nm15] at hval
    subst hval hS
    exact new_core_scratch s _ k cap 2 p0 f q1 q2 q3 q4 hAR hkl (by decide) (by decide) hk hp hf
      hQ1 hc1 hd1 hQ2 hc2' hd2 hQ3 hc3 hd3 hQ4 hc4' hd4 rfl rfl
      (guestInv_congr (s := s) rfl rfl rfl rfl hAR.1)
  · apply Ret.ns_ite_false_skip
      (by simp [ev, evalHOLExact, HolFiniteMapExact.lookup_update, FUPDATE,
            Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def]; omega)
    st_step (q1 + 0) k
    st_step (q1 + 8) st
    st_step (q1 + 16) cap
    st_step (q1 + 24) 0
    apply ns_scratch_alloc hcode ((cap + 1) * st) (by evs) q1 f (by evs) (by evs)
    intro hc2' hd2
    generalize hQ2 : (q1 - (cap + 1) * st) &&& ((0 : BitVec 64) - 8) = q2 at *
    st_step (q1 + 32) q2
    apply ns_scratch_alloc hcode ((cap + 1) * 32) (by evs) q2 f (by evs) (by evs)
    intro hc3 hd3
    generalize hQ3 : (q2 - (cap + 1) * 32) &&& ((0 : BitVec 64) - 8) = q3 at *
    st_step (q1 + 40) q3
    apply ns_scratch_alloc hcode ((cap + 1) * 8) (by evs) q3 f (by evs) (by evs)
    intro hc4' hd4
    generalize hQ4 : (q3 - (cap + 1) * 8) &&& ((0 : BitVec 64) - 8) = q4 at *
    st_step (q1 + 48) q4
    st_step (q1 + 56) 0
    st_step (q1 + 64) 1
    st_step (q1 + 72) 0
    st_step (q1 + 80) cap
    apply Ret.ns_ret
    intro val hval
    simp [ev, evalHOLExact, HolFiniteMapExact.lookup_update, FUPDATE, nm15] at hval
    subst hval hS
    exact new_core_scratch s _ k cap cap p0 f q1 q2 q3 q4 hAR hkl (by omega) hcl hk hp hf
      hQ1 hc1 hd1 hQ2 hc2' hd2 hQ3 hc3 hd3 hQ4 hc4' hd4 rfl rfl
      (guestInv_congr (s := s) rfl rfl rfl rfl hAR.1)

theorem lookup_htab_new_scratch :
    originalRuntimeCode.lookup (ofString "htab_new_scratch") =
      some ([(ofString "key_len", .one), (ofString "cap", .one)],
        sourceFnBody Guest.Software.guestFn_htab_new_scratch, .one) :=
  lookup_of_guestAst_getElem 129 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htab_new_scratch) rfl

theorem local_word_of_mem {F : Type} (s : PanSemStateFiniteExact 64 F) (n : String) (S : List Nat)
    (h0 : 0 ∉ S) (h : locN s n ∈ S) :
    ∃ w : BitVec 64, s.locals.lookup (ofString n) = some (.val (.word w)) ∧ w.toNat ∈ S := by
  unfold locN at h
  split at h
  · rename_i w hw; exact ⟨w, hw, h⟩
  · exact absurd h h0

theorem global_word_of_pos {F : Type} (s : PanSemStateFiniteExact 64 F) (n : String)
    (h : 0 < globN s n) : ∃ w : BitVec 64, s.globals.lookup (ofString n) = some (.val (.word w)) ∧
      w.toNat = globN s n := by
  unfold globN at h ⊢
  split at h
  · rename_i w hw; exact ⟨w, hw, rfl⟩
  · omega

theorem htab_new_scratch_no_cap_word_no_ret {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) (p0 f : BitVec 64)
    (hp : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word p0)))
    (hf : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word f)))
    (hncap : ∀ w : BitVec 64, s.locals.lookup (ofString "cap") ≠ some (.val (.word w))) :
    Ret s (sourceFnBody Guest.Software.guestFn_htab_new_scratch) (NewPost s) := by
  have hb : sourceFnBody Guest.Software.guestFn_htab_new_scratch =
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_htab_new_scratch).body := rfl
  rw [hb]
  dsimp only [extractFn, Guest.Software.guestFn_htab_new_scratch,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural, List.map, Option.map]
  refine Ret.of_NS (ns_scratch_alloc hcode 88 (by evs) p0 f hp hf fun _ _ => Ret.ns_dec fun stride _ => ?_)
  intro rv hrv
  rw [evaluateHOLFiniteState_dec_total] at hrv
  dsimp only at hrv
  have hcap_lookup : (((s.locals.update (ofString "t", .val (.word ((p0 - 88) &&& ((0 : BitVec 64) - 8))))).update
      (ofString "stride", stride)).lookup (ofString "cap")) = s.locals.lookup (ofString "cap") := by
    simp [HolFiniteMapExact.lookup_update, FUPDATE, nm7, nm14]
  simp only [evalHOLExact, NS, hcap_lookup] at hrv
  rcases hcl : s.locals.lookup (ofString "cap") with _ | v
  · simp [hcl] at hrv
  · simp only [hcl] at hrv
    rcases v with ⟨⟨w⟩⟩ | fs | ⟨nm, fs⟩
    · exact absurd hcl (hncap w)
    · simp [shapeOfHOLExact, shapeEqHOL] at hrv
    · simp [shapeOfHOLExact, shapeEqHOL] at hrv

theorem htab_new_scratch_spec :
    FunSpec HtabNewReady HtabNewExit (ofString "htab_new_scratch") := by
  refine ⟨_, _, _, lookup_htab_new_scratch, ?_⟩
  intro F s hcode hready _ _ v hv
  obtain ⟨hAR, hkl, hcl⟩ := hready
  obtain ⟨k, hk, hkl'⟩ := local_word_of_mem s "key_len" htabKeyLens (by decide) hkl
  have hss : scratchStart = 2952790016 := rfl
  have hposf : 0 < globN s "frame_mem_ptr" := by
    have := hAR.2.2.2.1; rw [hss] at this; omega
  have hpos : 0 < globN s "scratch_ptr" := by
    have := hAR.2.2.2.2.1; omega
  obtain ⟨p0, hp, _⟩ := global_word_of_pos s "scratch_ptr" hpos
  obtain ⟨f, hf, _⟩ := global_word_of_pos s "frame_mem_ptr" hposf
  by_cases hcw : ∃ cap : BitVec 64, s.locals.lookup (ofString "cap") = some (.val (.word cap))
  · obtain ⟨cap, hc⟩ := hcw
    have hcl' : cap.toNat ≤ htabCapMax := by simpa [locN, hc] using hcl
    exact htab_new_scratch_run s hcode k cap p0 f hk hc hp hf hAR hkl' hcl' v hv
  · exact htab_new_scratch_no_cap_word_no_ret s hcode p0 f hp hf (fun w hw => hcw ⟨w, hw⟩) v hv

end InitECandidate.Solver.Wave8GuestInv.HtabC00Ports
