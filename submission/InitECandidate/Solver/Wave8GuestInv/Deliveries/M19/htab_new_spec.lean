import InitECandidate.Solver.Wave8GuestInv.Deliveries.M19.Bridge
import InitECandidate.Solver.HeapPotential

/-! `htab_new_spec`: verified against rev9 `Wave8GuestInv` definitions (`HtabNewReady`,
`HtabNewExit`, including `AllocatorGrows`, `hdr post w.toNat 0 = locN s "key_len"`, 8-byte
alignment in `ArenaOK`, `CellHits` in `FrameOutside`, global frame, and `cap ≤ htabCapMax` with the
`cap < 2 ? 2 : cap` clamp). -/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.Wave8GuestInv.M19

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

/-! ## 1. Distinctness of local/global names used in `htab_new` -/

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

/-! ## 2. Ordinary domain characterization and `alloc` semantics -/

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

theorem alloc_body_run {F : Type}
    (state : PanSemStateFiniteExact 64 F) (p n : BitVec 64)
    (hcode : state.code = originalRuntimeCode)
    (hp_lookup : state.globals.lookup (ofString "heap_ptr") = some (.val (.word p)))
    (hn : state.locals.lookup (ofString "n") = some (.val (.word n))) :
    let out := evaluateHOLFiniteState state (sourceFnBody Guest.Software.guestFn_alloc)
    let q := (p + (n + 7)) &&& ((0 : BitVec 64) - 8)
    ∀ retVal : ValueHOL 64, out.1 = some (.returned retVal) →
      retVal = .val (.word p) ∧ ¬ (cMax.toNat < q.toNat) ∧
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
          evaluateHOLFiniteState_return]
      rw [heval_end]
      intro retVal hret
      injection hret with hr
      injection hr with hr'
      exact ⟨hr'.symm, hcmp2, rfl⟩

theorem decCall_alloc {F : Type} {s : PanSemStateFiniteExact 64 F} {x : MlS}
    {arg : ExpHOL 64} {cont : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hcode : s.code = originalRuntimeCode) (nv : BitVec 64)
    (harg : ev s arg = some (.val (.word nv))) (p : BitVec 64)
    (hp : s.globals.lookup (ofString "heap_ptr") = some (.val (.word p)))
    (hk : ¬ (cMax.toNat < ((p + (nv + 7)) &&& ((0 : BitVec 64) - 8)).toNat) →
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
  obtain ⟨hw, hq, hpost⟩ := this
  simp only [ValueHOL.val.injEq, HolWordLab.word.injEq] at hw
  subst hw
  have hst : { post with locals := s.locals } = { s with
      globals := (s.globals.update (ofString "heap_ptr",
        .val (.word ((w + (nv + 7)) &&& ((0 : BitVec 64) - 8)))))
      clock := s.clock - 1 } := by
    dsimp only at hpost
    rw [hpost]; rfl
  rw [hst]
  exact hk hq

theorem ns_alloc {F : Type} {s : PanSemStateFiniteExact 64 F} {L G} {M C} {x : MlS}
    {arg : ExpHOL 64} {cont : ProgHOL 64}
    {Φ : ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (hcode : s.code = originalRuntimeCode) (nv : BitVec 64)
    (harg : ev (NS s L G M C) arg = some (.val (.word nv))) (p : BitVec 64)
    (hp : G.lookup (ofString "heap_ptr") = some (.val (.word p)))
    (hk : ¬ (cMax.toNat < ((p + (nv + 7)) &&& ((0 : BitVec 64) - 8)).toNat) →
      Ret (NS s (L.update (x, .val (.word p)))
          (G.update (ofString "heap_ptr", .val (.word ((p + (nv + 7)) &&& ((0 : BitVec 64) - 8)))))
          M (C - 1)) cont
        (fun v t => Φ v { t with locals := HolFiniteMapExact.resVarEq t.locals (x, L.lookup x) })) :
    Ret (NS s L G M C) (.decCall x .one (ofString "alloc") [arg] cont) Φ :=
  decCall_alloc hcode nv harg p hp hk

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

/-! ## 3. Empty table construction (`NewCore` on rev9) -/

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

def HtabNewExitSafe : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
    PanSemStateFiniteExact 64 F → Prop :=
  fun s r post => ∀ v, r = some (.returned v) → ∃ w : BitVec 64, v = .val (.word w) ∧
    ArenaReady post ∧ AllocatorGrows s post ∧ HtabWF post w.toNat ∧ hdr post w.toNat 3 = 0 ∧
    hdr post w.toNat 0 = locN s "key_len" ∧
    (∀ i ∈ htabFootprint post w.toNat, Allocated post i ∧
      (Inside i (globN s "heap_ptr") (globN post "heap_ptr") ∨
        Inside i (globN post "scratch_ptr") (globN s "scratch_ptr"))) ∧
    FrameOutside s post
      [(globN post "scratch_ptr", globN s "scratch_ptr" - globN post "scratch_ptr")]
      (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr") ∧
    ∀ name, ofString name ∉ [ofString "heap_ptr", ofString "scratch_ptr"] →
      s.globals.lookup (ofString name) = post.globals.lookup (ofString name)

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
    ∀ name, ofString name ∉ [ofString "heap_ptr", ofString "scratch_ptr"] →
      s.globals.lookup (ofString name) = post.globals.lookup (ofString name)

theorem round8_toNat (x : BitVec 64) (n : Nat) (hx : x.toNat % 8 = 0) (hn : n % 8 = 0)
    (hb : x.toNat + n + 7 < 2 ^ 64) (y : BitVec 64) (hy : y.toNat = n) :
    ((x + (y + 7)) &&& ((0 : BitVec 64) - 8)).toNat = x.toNat + n := by
  rw [and_neg8_toNat_htab]
  have : (x + (y + 7)).toNat = x.toNat + n + 7 := by
    simp only [BitVec.toNat_add, hy]
    have : (7 : BitVec 64).toNat = 7 := rfl
    rw [this]
    omega
  rw [this]
  omega

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
    exact ⟨hdisj.1, hdisj.2.1, hdisj.2.2, fun _ h => h.elim⟩

theorem new_core_heap {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (k cap c p0 q1 q2 q3 q4 : BitVec 64)
    (hAR : ArenaReady s) (hkl : k.toNat ∈ htabKeyLens)
    (hcap2 : 2 ≤ c.toNat) (hcapmax : c.toNat ≤ htabCapMax)
    (hkey : s.locals.lookup (ofString "key_len") = some (.val (.word k)))
    (hp : s.globals.lookup (ofString "heap_ptr") = some (.val (.word p0)))
    (hdom0 : s.memaddrs (p0 + 0))
    (hQ1 : (p0 + (88 + 7)) &&& ((0 : BitVec 64) - 8) = q1)
    (hQ2 : (q1 + ((c + 1) * ((k + 7) &&& 18446744073709551608#64) + 7)) &&&
      ((0 : BitVec 64) - 8) = q2)
    (hQ3 : (q2 + ((c + 1) * 32 + 7)) &&& ((0 : BitVec 64) - 8) = q3)
    (hQ4 : (q3 + ((c + 1) * 8 + 7)) &&& ((0 : BitVec 64) - 8) = q4)
    (hq4 : ¬ cMax.toNat < q4.toNat)
    (hM : post.memory = hdrMem s.memory p0 k ((k + 7) &&& 18446744073709551608#64) cap c q1 q2 q3)
    (hG : post.globals = (((s.globals.update (ofString "heap_ptr", .val (.word q1))).update
      (ofString "heap_ptr", .val (.word q2))).update (ofString "heap_ptr", .val (.word q3))).update
      (ofString "heap_ptr", .val (.word q4)))
    (hGI : GuestInv post) :
    NewPost s (.val (.word p0)) post := by
  obtain ⟨hst, hst8, hst64, hL1, hL2, hL3, _, _, hk1, hk60⟩ := new_params k c hkl hcap2 hcapmax
  set st := (k + 7) &&& 18446744073709551608#64
  have hcMax : cMax.toNat = 2952790016 := rfl
  obtain ⟨hgis, hlo, hhi, h4, h5, h6, h7, h8, h9⟩ := hAR
  have hgp : globN s "heap_ptr" = p0.toNat := by simp [globN, hp]
  rw [hgp] at hlo hhi
  have hsb : sourceBase = 2701131776 := rfl
  have hhl : heapLimit = 2952790016 := rfl
  rw [hsb] at hlo
  rw [hhl] at hhi
  have hdom := hgis.memaddrs ▸ hdom0
  rw [ordinaryDomain_iff] at hdom
  have hp0z : (p0 + 0).toNat = p0.toNat := by simp
  rw [hp0z] at hdom
  obtain ⟨_, _, hal⟩ := hdom
  have hq4n : q4.toNat ≤ 2952790016 := by omega
  have e1 : q1.toNat = p0.toNat + 88 := by
    rw [← hQ1]; exact round8_toNat p0 88 hal (by norm_num) (by omega) 88 rfl
  have hcN : c.toNat ≤ 4294967296 := by simpa [htabCapMax] using hcapmax
  have hL1n : ((c + 1) * st).toNat ≤ (4294967296 + 1) * 64 := by
    rw [hL1]; exact Nat.mul_le_mul (by omega) hst64
  have hL2n : ((c + 1) * 32).toNat ≤ (4294967296 + 1) * 32 := by
    rw [hL2]; exact Nat.mul_le_mul (by omega) (by norm_num)
  have hL3n : ((c + 1) * 8).toNat ≤ (4294967296 + 1) * 8 := by
    rw [hL3]; exact Nat.mul_le_mul (by omega) (by norm_num)
  have hL1m : ((c + 1) * st).toNat % 8 = 0 := by rw [hL1, Nat.mul_mod, hst8]; simp
  have e2 : q2.toNat = q1.toNat + ((c + 1) * st).toNat := by
    rw [← hQ2]; exact round8_toNat q1 _ (by omega) hL1m (by omega) _ rfl
  have e3 : q3.toNat = q2.toNat + ((c + 1) * 32).toNat := by
    rw [← hQ3]; exact round8_toNat q2 _ (by omega) (by rw [hL2]; omega) (by rw [hL2]; omega) _ rfl
  have e4 : q4.toNat = q3.toNat + ((c + 1) * 8).toNat := by
    rw [← hQ4]; exact round8_toNat q3 _ (by omega) (by rw [hL3]; omega) (by rw [hL3]; omega) _ rfl
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10⟩ := hdr_hdrMem post s.memory p0 k st cap c q1 q2 q3 hM
  have hgpost : globN post "heap_ptr" = q4.toNat := by
    simp [globN, hG, HolFiniteMapExact.lookup_update, FUPDATE]
  have hsc : globN post "scratch_ptr" = globN s "scratch_ptr" := by
    simp [globN, hG, HolFiniteMapExact.lookup_update, FUPDATE, nm43]
  have hfm : globN post "frame_mem_ptr" = globN s "frame_mem_ptr" := by
    simp [globN, hG, HolFiniteMapExact.lookup_update, FUPDATE, nm45]
  have hq4align : q4.toNat % 8 = 0 := by
    rw [← hQ4, and_neg8_toNat_htab]; omega
  refine ⟨p0, rfl, ?_, ?_, ?_, d3, ?_, ?_, ?_, ?_⟩
  · refine ⟨hGI, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hgpost, hsb]; omega
    · rw [hgpost, hhl]; omega
    · rw [hfm]; exact h4
    · rw [hfm, hsc]; exact h5
    · rw [hsc]; exact h6
    · rw [hgpost]; exact hq4align
    · rw [hfm]; exact h8
    · rw [hsc]; exact h9
  · exact ⟨by rw [hgp, hgpost]; omega, by rw [hsc]⟩
  · exact htabWF_empty post p0.toNat hGI.memaddrs k.toNat st.toNat c.toNat q1.toNat q2.toNat
      q3.toNat d0 d1 d3 d4 d5 d6 d7 d8 d9 d10 hk1 hk60 hst (by omega) hal
      (by omega) (by rw [hL1] at e2; omega) (by rw [hL1, hL2] at *; omega) hlo (by omega)
      (by rw [hL1] at e2; omega) (by rw [hL1, hL2] at *; omega) (by omega)
      (by rw [hL1] at e2; omega) (by rw [hL1, hL2] at *; omega) (by rw [hL1, hL2, hL3] at *; omega)
      (by rw [hL1, hL2, hL3] at *; omega)
  · rw [d0]; simp [locN, hkey]
  · intro i hi
    simp only [htabFootprint, d1, d4, d5, d6, d10, List.mem_cons, List.not_mem_nil, or_false] at hi
    have hA : ∀ b l : Nat, p0.toNat ≤ b → b + l ≤ q4.toNat →
        Allocated post (b, l) ∧ (Inside (b, l) (globN s "heap_ptr") (globN post "heap_ptr") ∨
          Inside (b, l) (globN post "scratch_ptr") (globN s "scratch_ptr")) := by
      intro b l h1 h2
      refine ⟨Or.inl ⟨by rw [hsb]; omega, by rw [hgpost]; exact h2⟩,
        Or.inl ⟨by rw [hgp]; exact h1, by rw [hgpost]; exact h2⟩⟩
    rcases hi with rfl | rfl | rfl | rfl
    · exact hA _ _ (le_refl _) (by omega)
    · exact hA _ _ (by omega) (by rw [← hL1]; omega)
    · exact hA _ _ (by omega) (by rw [← hL2]; omega)
    · exact hA _ _ (by omega) (by rw [← hL3]; omega)
  · intro a _ hout
    rw [hM]
    apply hdrMem_out _ _ _ _ _ _ _ _ _ (by omega)
    intro hin
    apply hout
    simp only [CellHits, hgp, hgpost]
    have hp0a := hal
    have hq4a := hq4align
    omega
  · intro name hname
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hname
    have hne : ofString "heap_ptr" ≠ ofString name := fun he => hname (Or.inl he.symm)
    simp [hG, HolFiniteMapExact.lookup_update, FUPDATE, hne]

/-! ## 4. Symbolic run of `htab_new` -/

local macro "evs" : tactic => `(tactic| ((simp [ev, evalHOLExact, evalListHOLExact,
  HolFiniteMapExact.lookup_update, FUPDATE, wordOpHOL, wordOp, valueIsWord, valueWord,
  nm1, nm2, nm3, nm4, nm5, nm6, nm7, nm8, nm9, nm10, nm11, nm12, nm13, nm14, nm15, nm16,
  nm17, nm18, nm19, nm20, nm21, nm22, nm23, nm24, nm25, nm26, nm27, nm28, nm29, nm30, nm31,
  nm32, nm33, nm34, nm35, nm36, nm37, nm38, nm39, nm40, nm41, nm42]) <;>
  first | assumption | rfl))

local macro "st_step" a:term:max w:term:max : tactic =>
  `(tactic| (apply Ret.ns_storeW $a $w (by evs) (by evs); intro _))

attribute [local irreducible] Ret in
theorem htab_new_run {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) (k cap p0 : BitVec 64)
    (hk : s.locals.lookup (ofString "key_len") = some (.val (.word k)))
    (hc : s.locals.lookup (ofString "cap") = some (.val (.word cap)))
    (hp : s.globals.lookup (ofString "heap_ptr") = some (.val (.word p0)))
    (hAR : ArenaReady s) (hkl : k.toNat ∈ htabKeyLens) (hcl : cap.toNat ≤ htabCapMax) :
    Ret s (sourceFnBody Guest.Software.guestFn_htab_new) (NewPost s) := by
  have hb : sourceFnBody Guest.Software.guestFn_htab_new =
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_htab_new).body := rfl
  rw [hb]
  dsimp only [extractFn, Guest.Software.guestFn_htab_new,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural, List.map, Option.map]
  apply Ret.of_NS
  apply ns_alloc hcode 88 (by evs) p0 hp
  intro hq1
  generalize hQ1 : (p0 + (88 + 7)) &&& ((0 : BitVec 64) - 8) = q1 at *
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
    st_step (p0 + 0) k
    st_step (p0 + 8) st
    st_step (p0 + 16) cap
    st_step (p0 + 24) 0
    apply ns_alloc hcode (((2 : BitVec 64) + 1) * st) (by evs) q1 (by evs)
    intro hq2
    generalize hQ2 : (q1 + (((2 : BitVec 64) + 1) * st + 7)) &&& ((0 : BitVec 64) - 8) = q2 at *
    st_step (p0 + 32) q1
    apply ns_alloc hcode (((2 : BitVec 64) + 1) * 32) (by evs) q2 (by evs)
    intro hq3
    generalize hQ3 : (q2 + (((2 : BitVec 64) + 1) * 32 + 7)) &&& ((0 : BitVec 64) - 8) = q3 at *
    st_step (p0 + 40) q2
    apply ns_alloc hcode (((2 : BitVec 64) + 1) * 8) (by evs) q3 (by evs)
    intro hq4
    generalize hQ4 : (q3 + (((2 : BitVec 64) + 1) * 8 + 7)) &&& ((0 : BitVec 64) - 8) = q4 at *
    st_step (p0 + 48) q3
    st_step (p0 + 56) 0
    st_step (p0 + 64) 1
    st_step (p0 + 72) 0
    st_step (p0 + 80) 2
    apply Ret.ns_ret
    intro val hval
    simp [ev, evalHOLExact, HolFiniteMapExact.lookup_update, FUPDATE, nm15] at hval
    subst hval hS
    rename_i h0 _ _ _ _ _ _ _ _ _ _
    exact new_core_heap s _ k cap 2 p0 q1 q2 q3 q4 hAR hkl (by decide) (by decide) hk hp h0
      hQ1 hQ2 hQ3 hQ4 hq4 rfl rfl (guestInv_congr (s := s) rfl rfl rfl rfl hAR.1)
  · apply Ret.ns_ite_false_skip
      (by simp [ev, evalHOLExact, HolFiniteMapExact.lookup_update, FUPDATE,
            Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def]; omega)
    st_step (p0 + 0) k
    st_step (p0 + 8) st
    st_step (p0 + 16) cap
    st_step (p0 + 24) 0
    apply ns_alloc hcode ((cap + 1) * st) (by evs) q1 (by evs)
    intro hq2
    generalize hQ2 : (q1 + ((cap + 1) * st + 7)) &&& ((0 : BitVec 64) - 8) = q2 at *
    st_step (p0 + 32) q1
    apply ns_alloc hcode ((cap + 1) * 32) (by evs) q2 (by evs)
    intro hq3
    generalize hQ3 : (q2 + ((cap + 1) * 32 + 7)) &&& ((0 : BitVec 64) - 8) = q3 at *
    st_step (p0 + 40) q2
    apply ns_alloc hcode ((cap + 1) * 8) (by evs) q3 (by evs)
    intro hq4
    generalize hQ4 : (q3 + ((cap + 1) * 8 + 7)) &&& ((0 : BitVec 64) - 8) = q4 at *
    st_step (p0 + 48) q3
    st_step (p0 + 56) 0
    st_step (p0 + 64) 1
    st_step (p0 + 72) 0
    st_step (p0 + 80) cap
    apply Ret.ns_ret
    intro val hval
    simp [ev, evalHOLExact, HolFiniteMapExact.lookup_update, FUPDATE, nm15] at hval
    subst hval hS
    rename_i h0 _ _ _ _ _ _ _ _ _ _
    exact new_core_heap s _ k cap cap p0 q1 q2 q3 q4 hAR hkl (by omega) hcl hk hp h0
      hQ1 hQ2 hQ3 hQ4 hq4 rfl rfl (guestInv_congr (s := s) rfl rfl rfl rfl hAR.1)

theorem lookup_htab_new :
    originalRuntimeCode.lookup (ofString "htab_new") =
      some ([(ofString "key_len", .one), (ofString "cap", .one)],
        sourceFnBody Guest.Software.guestFn_htab_new, .one) :=
  lookup_of_guestAst_getElem 128 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_htab_new) rfl

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

theorem htab_new_no_cap_word_no_ret {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode) (p0 : BitVec 64)
    (hp : s.globals.lookup (ofString "heap_ptr") = some (.val (.word p0)))
    (hncap : ∀ w : BitVec 64, s.locals.lookup (ofString "cap") ≠ some (.val (.word w))) :
    Ret s (sourceFnBody Guest.Software.guestFn_htab_new) (NewPost s) := by
  have hb : sourceFnBody Guest.Software.guestFn_htab_new =
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_htab_new).body := rfl
  rw [hb]
  dsimp only [extractFn, Guest.Software.guestFn_htab_new,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural, List.map, Option.map]
  refine Ret.of_NS (ns_alloc hcode 88 (by evs) p0 hp fun _ => Ret.ns_dec fun stride _ => ?_)
  intro rv hrv
  rw [evaluateHOLFiniteState_dec_total] at hrv
  dsimp only at hrv
  have hcap_lookup : (((s.locals.update (ofString "t", .val (.word p0))).update
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

/-- Proved safe variant (`ofString name ∉ [ofString "heap_ptr", ofString "scratch_ptr"]`). -/
theorem htab_new_spec_safe :
    FunSpec HtabNewReady HtabNewExitSafe (ofString "htab_new") := by
  refine ⟨_, _, _, lookup_htab_new, ?_⟩
  intro F s hcode hready _ v hv
  obtain ⟨hAR, hkl, hcl⟩ := hready
  obtain ⟨k, hk, hkl'⟩ := local_word_of_mem s "key_len" htabKeyLens (by decide) hkl
  have hpos : 0 < globN s "heap_ptr" := by
    have := hAR.2.1
    have : sourceBase = 2701131776 := rfl
    omega
  obtain ⟨p0, hp, _⟩ := global_word_of_pos s "heap_ptr" hpos
  by_cases hcw : ∃ cap : BitVec 64, s.locals.lookup (ofString "cap") = some (.val (.word cap))
  · obtain ⟨cap, hc⟩ := hcw
    have hcl' : cap.toNat ≤ htabCapMax := by simpa [locN, hc] using hcl
    exact htab_new_run s hcode k cap p0 hk hc hp hAR hkl' hcl' v hv
  · exact htab_new_no_cap_word_no_ret s hcode p0 hp (fun w hw => hcw ⟨w, hw⟩) v hv

end InitECandidate.Solver.Wave8GuestInv.M19
