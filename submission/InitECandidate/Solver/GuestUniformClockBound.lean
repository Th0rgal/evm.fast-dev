import InitECandidate.Solver.UniformSourceClock
import InitECandidate.Solver.PanRunBounded

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace InitECandidate.Solver.GuestUniformClockBound

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestGlobalKeep
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanRunBounded

theorem ProgBounded.iteMax (condition : ExpHOL 64) {yes no : ProgHOL 64} {a b : Nat}
    (left : ProgBounded yes a) (right : ProgBounded no b) :
    ProgBounded (.ite condition yes no) (max a b) :=
  ProgBounded.ite condition (left.weaken (Nat.le_max_left a b)) (right.weaken (Nat.le_max_right a b))

theorem ProgBounded.sharedStore (operator : OpSize) (address value : ExpHOL 64) :
    ProgBounded (.shMemStore operator address value) 0 :=
  ProgBounded.straight _ rfl

theorem funBounded_of_guestAst
    (i : Nat) (hi : i < Guest.Software.guestAst.length)
    (d : Decl (BitVec 64)) (cost : Nat)
    (hd : Guest.Software.guestAst[i] = .function (extractFn d))
    (hprog : ProgBounded (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural (extractFn d).body) cost) :
    FunBounded (ofString (extractFn d).name) cost :=
  ⟨(extractFn d).params.map InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
   InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural (extractFn d).body,
   InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural (extractFn d).returnShape,
   lookup_of_guestAst_getElem i hi (extractFn d) hd,
   hprog⟩

theorem funBounded_trap_with : FunBounded (ofString "trap_with") 0 :=
  funBounded_of_guestAst 3 (by rw [guestAst_len]; decide) Guest.Software.guestFn_trap_with 0 rfl
    (ProgBounded.straight _ rfl)

theorem funBounded_mem_init : FunBounded (ofString "mem_init") 0 :=
  funBounded_of_guestAst 6 (by rw [guestAst_len]; decide) Guest.Software.guestFn_mem_init 0 rfl
    (ProgBounded.straight _ rfl)

theorem funBounded_heap_mark : FunBounded (ofString "heap_mark") 0 :=
  funBounded_of_guestAst 8 (by rw [guestAst_len]; decide) Guest.Software.guestFn_heap_mark 0 rfl
    (ProgBounded.straight _ rfl)

theorem funBounded_heap_release : FunBounded (ofString "heap_release") 0 :=
  funBounded_of_guestAst 9 (by rw [guestAst_len]; decide) Guest.Software.guestFn_heap_release 0 rfl
    (ProgBounded.straight _ rfl)

theorem funBounded_frame_mem_mark : FunBounded (ofString "frame_mem_mark") 0 :=
  funBounded_of_guestAst 11 (by rw [guestAst_len]; decide) Guest.Software.guestFn_frame_mem_mark 0 rfl
    (ProgBounded.straight _ rfl)

theorem funBounded_frame_mem_release : FunBounded (ofString "frame_mem_release") 0 :=
  funBounded_of_guestAst 12 (by rw [guestAst_len]; decide) Guest.Software.guestFn_frame_mem_release 0 rfl
    (ProgBounded.straight _ rfl)

theorem funBounded_scratch_mark : FunBounded (ofString "scratch_mark") 0 :=
  funBounded_of_guestAst 14 (by rw [guestAst_len]; decide) Guest.Software.guestFn_scratch_mark 0 rfl
    (ProgBounded.straight _ rfl)

theorem funBounded_scratch_release : FunBounded (ofString "scratch_release") 0 :=
  funBounded_of_guestAst 15 (by rw [guestAst_len]; decide) Guest.Software.guestFn_scratch_release 0 rfl
    (ProgBounded.straight _ rfl)

private theorem progBounded_guarded_trap_seq (cond : ExpHOL 64) (codeVal : BitVec 64)
    {tail : ProgHOL 64} {cost : Nat}
    (htail : ProgBounded tail (max 1 cost)) :
    ProgBounded (.seq (.ite cond (.call (some (none, none)) (ofString "trap_with") [.const codeVal]) .skip) tail)
      (max 1 cost) := by
  intro F state hcode hbudget
  rw [evaluateHOLFiniteState_seq_line780]
  rw [evaluateHOLFiniteState_ite]
  split
  · split
    · rw [evaluateHOLFiniteState_skip]
      dsimp only
      exact htail state hcode hbudget
    · have hcall := ProgBounded.call funBounded_trap_with none [.const codeVal] state hcode (by omega)
      have hnonone := evaluate_call_trap_with_no_none state codeVal hcode
      rcases hrun : evaluateHOLFiniteState state (.call (some (none, none)) (ofString "trap_with") [.const codeVal]) with ⟨res, post⟩
      rw [hrun] at hcall hnonone
      cases res with
      | none => exact absurd rfl hnonone
      | some r =>
        dsimp only at hcall ⊢
        exact ⟨by omega, hcall.2.1, hcall.2.2⟩
  · dsimp only
    exact ⟨by omega, le_refl _, by simp⟩

theorem funBounded_alloc : FunBounded (ofString "alloc") 1 := by
  refine funBounded_of_guestAst 7 (by rw [guestAst_len]; decide) Guest.Software.guestFn_alloc 1 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_alloc,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural, List.map, Option.map]
  apply ProgBounded.dec
  apply progBounded_guarded_trap_seq _ 1 (cost := 1)
  apply ProgBounded.dec
  exact progBounded_guarded_trap_seq _ 1 (cost := 0) (ProgBounded.weaken (ProgBounded.straight _ rfl) (by decide))

theorem funBounded_frame_mem_alloc : FunBounded (ofString "frame_mem_alloc") 1 := by
  refine funBounded_of_guestAst 10 (by rw [guestAst_len]; decide) Guest.Software.guestFn_frame_mem_alloc 1 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_frame_mem_alloc,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural, List.map, Option.map]
  apply ProgBounded.dec
  apply progBounded_guarded_trap_seq _ 6 (cost := 1)
  apply ProgBounded.dec
  exact progBounded_guarded_trap_seq _ 6 (cost := 0) (ProgBounded.weaken (ProgBounded.straight _ rfl) (by decide))

theorem funBounded_scratch_alloc : FunBounded (ofString "scratch_alloc") 1 := by
  refine funBounded_of_guestAst 13 (by rw [guestAst_len]; decide) Guest.Software.guestFn_scratch_alloc 1 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_scratch_alloc,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural, List.map, Option.map]
  apply ProgBounded.dec
  apply progBounded_guarded_trap_seq _ 7 (cost := 1)
  apply ProgBounded.dec
  exact progBounded_guarded_trap_seq _ 7 (cost := 0) (ProgBounded.weaken (ProgBounded.straight _ rfl) (by decide))

theorem ProgBounded.alloc (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64)) :
    ProgBounded (.call (some (destination, none)) (ofString "alloc") arguments) 2 :=
  ProgBounded.call funBounded_alloc destination arguments

theorem lookup_memcpy :
    originalRuntimeCode.lookup (ofString "memcpy") =
      some ([(ofString "dst", .one), (ofString "src", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_memcpy, .one) :=
  lookup_of_guestAst_getElem 16 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_memcpy) rfl

theorem lookup_memeq :
    originalRuntimeCode.lookup (ofString "memeq") =
      some ([(ofString "a", .one), (ofString "b", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_memeq, .one) :=
  lookup_of_guestAst_getElem 18 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_memeq) rfl

theorem lookup_is_zero_bytes :
    originalRuntimeCode.lookup (ofString "is_zero_bytes") =
      some ([(ofString "p", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_is_zero_bytes, .one) :=
  lookup_of_guestAst_getElem 19 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_is_zero_bytes) rfl

def noTopBreak : ProgHOL 64 → Bool
  | .break => false
  | .seq first second => noTopBreak first && noTopBreak second
  | .ite _ yes no => noTopBreak yes && noTopBreak no
  | .dec _ _ _ body => noTopBreak body
  | .decCall _ _ _ _ continuation => noTopBreak continuation
  | .skip | .assign _ _ _ | .primitive _ _ _ | .store _ _ | .storeByte _ _ | .store32 _ _
  | .raise _ _ | .return _ | .extCall _ _ _ _ _ | .annot _ _ | .while _ _ | .continue => true
  | .call none _ _ | .call (some (_, none)) _ _ => true
  | _ => false

theorem evaluate_noTopBreak {F : Type} (program : ProgHOL 64) (supported : noTopBreak program = true)
    (state : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState state program).1 ≠ some .break := by
  cases shape : program with
  | «break» => simp [shape, noTopBreak] at supported
  | seq first second =>
    have children : noTopBreak first = true ∧ noTopBreak second = true := by
      simpa only [shape, noTopBreak, Bool.and_eq_true] using supported
    have remaining := evaluateHOLFiniteState_clock_le state first
    rw [evaluateHOLFiniteState_seq_line780]
    have one := evaluate_noTopBreak first children.1 state
    rcases firstRun : evaluateHOLFiniteState state first with ⟨result, middle⟩
    rw [firstRun] at one remaining
    cases result with
    | none => exact evaluate_noTopBreak second children.2 middle
    | some _ => exact one
  | ite condition yes no =>
    have children : noTopBreak yes = true ∧ noTopBreak no = true := by
      simpa only [shape, noTopBreak, Bool.and_eq_true] using supported
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_noTopBreak no children.2 state
      · exact evaluate_noTopBreak yes children.1 state
    · simp
  | dec name kind initializer body =>
    have child : noTopBreak body = true := by simpa only [shape, noTopBreak] using supported
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · simp
    · split
      · exact evaluate_noTopBreak body child _
      · simp
  | decCall name shape' function arguments continuation =>
    have child : noTopBreak continuation = true := by simpa only [shape, noTopBreak] using supported
    intro hcont
    rcases run : evaluateHOLFiniteState state (.decCall name shape' function arguments continuation) with ⟨result, post⟩
    rw [run] at hcont
    dsimp only at hcont
    subst hcont
    obtain ⟨w, resumed, inner, _, smaller, contRun, _⟩ := decCall_flowing (Or.inr (Or.inl rfl)) run
    have hno := evaluate_noTopBreak continuation child resumed
    rw [contRun] at hno
    exact hno rfl
  | skip => simp [evaluateHOLFiniteState_skip]
  | «continue» => simp [evaluateHOLFiniteState_continue]
  | annot tag text => simp [evaluateHOLFiniteState_annot]
  | raise name value =>
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only; split <;> simp
    · simp
  | «return» value =>
    rw [evaluateHOLFiniteState_return]
    split
    · simp
    · split <;> simp
  | store destination value =>
    rcases (evaluate_store_control_frame state destination value).1 with h | h <;> rw [h] <;> simp
  | storeByte destination value =>
    rcases (evaluate_storeByte_control_frame state destination value).1 with h | h <;> rw [h] <;> simp
  | store32 address value =>
    rw [evaluateHOLFiniteState_store32]
    repeat' first | split | simp
  | assign kind name value =>
    rw [evaluateHOLFiniteState_assign]
    split
    · simp
    · split <;> simp
  | primitive name operator arguments =>
    rw [evaluateHOLFiniteState_primitive]
    repeat' first | split | simp
  | extCall function a b c d =>
    rw [evaluateHOLFiniteState_extCall_source]
    repeat' first | split | simp
  | call info function arguments =>
    have handlerFree : info = none ∨ ∃ d, info = some (d, none) := by
      rcases info with _ | ⟨d, _ | h⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨d, rfl⟩
      · simp [shape, noTopBreak] at supported
    rw [evaluateHOLFiniteState_call]
    rcases handlerFree with rfl | ⟨d, rfl⟩
    all_goals dsimp only
    all_goals repeat' first | split | simp | simp_all
  | «while» condition body =>
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · simp
        · rename_i nonzero
          dsimp only
          rw [fixClockHOLFinite_evaluateState]
          have remaining := evaluateHOLFiniteState_clock_le (decClockHOLFinite state) body
          rcases bodyRun : evaluateHOLFiniteState (decClockHOLFinite state) body with ⟨result, middle⟩
          rw [bodyRun] at remaining
          have smaller : middle.clock < state.clock := by
            change middle.clock ≤ state.clock - 1 at remaining
            omega
          cases result with
          | none => exact evaluate_noTopBreak (.while condition body) (by simp [noTopBreak]) middle
          | some result =>
            cases result with
            | «continue» => exact evaluate_noTopBreak (.while condition body) (by simp [noTopBreak]) middle
            | _ => simp
      · simp
    · simp
  | _ => simp [shape, noTopBreak] at supported
termination_by (state.clock, sizeOf program)
decreasing_by all_goals (simp_all [decClockHOLFinite, setVarHOLFinite]; omega)

private theorem eval_notLower_stride_guard {F : Type} (state : PanSemStateFiniteExact 64 F)
    (counter limit : MlS) (K w stride : BitVec 64)
    (hsmall : K.toNat + stride.toNat < 2 ^ 64) (hw : w.toNat ≤ K.toNat)
    (atCounter : state.locals.lookup counter = some (.val (.word w)))
    (atLimit : state.locals.lookup limit = some (.val (.word K))) :
    evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      (.cmp .notLower (.var .local limit) (.op .add [.var .local counter, .const stride])) =
      some (.val (.word (if w.toNat + stride.toNat ≤ K.toNat then 1 else 0))) := by
  rw [evalHOLFinite_eq_toExact]
  have hadd : (w + stride).toNat = w.toNat + stride.toNat :=
    BitVec.toNat_add_of_lt (by omega)
  simp only [evalHOLExact, evalListHOLExact, atCounter, atLimit, wordOpHOL, wordOp,
    List.all_cons, List.all_nil, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
    valueIsWord, valueWord, Bool.and_true, if_true, Option.map_some,
    Compiler.Encoders.Asm.wordCmpHOL]
  by_cases hle : w.toNat + stride.toNat ≤ K.toNat
  · have hlt : ¬ (K < w + stride) := by
      rw [BitVec.lt_def, hadd]
      omega
    simp [hle, hlt]
  · have hlt : K < w + stride := by
      rw [BitVec.lt_def, hadd]
      omega
    simp [hle, hlt]

theorem notLowerStrideWhile_run (counter limit : MlS) (K stride : BitVec 64)
    (hsmall : K.toNat + stride.toNat < 2 ^ 64) (hpos : 0 < stride.toNat)
    {body : ProgHOL 64} {cost : Nat} (counted : CountedBody counter stride body cost)
    (preservesLimit : avoidsLocal limit body = true)
    (noBreak : noTopBreak body = true) :
    ∀ m : Nat, ∀ {F : Type} (state : PanSemStateFiniteExact 64 F),
      state.code = originalRuntimeCode →
      ∀ w : BitVec 64, state.locals.lookup counter = some (.val (.word w)) →
      state.locals.lookup limit = some (.val (.word K)) →
      w.toNat ≤ K.toNat → (K.toNat - w.toNat) / stride.toNat = m →
      m * (cost + 1) ≤ state.clock →
      let r := evaluateHOLFiniteState state
        (.while (.cmp .notLower (.var .local limit) (.op .add [.var .local counter, .const stride])) body)
      state.clock ≤ r.2.clock + m * (cost + 1) ∧ r.2.clock ≤ state.clock ∧ r.1 ≠ some .timeOut ∧
        (r.1 = none → ∃ w' : BitVec 64, r.2.locals.lookup counter = some (.val (.word w')) ∧
          r.2.locals.lookup limit = some (.val (.word K)) ∧
          w.toNat ≤ w'.toNat ∧ w'.toNat ≤ K.toNat ∧ K.toNat < w'.toNat + stride.toNat ∧
          r.2.code = state.code) := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro F state code w atCounter atLimit hw hm hbudget
    have hguard := eval_notLower_stride_guard state counter limit K w stride hsmall hw atCounter atLimit
    dsimp only
    rw [evaluateHOLFiniteState_while_total, hguard]
    by_cases hle : w.toNat + stride.toNat ≤ K.toNat
    · rw [if_pos hle]
      simp only [show (1 : BitVec 64) ≠ 0 by decide, if_true, ne_eq, not_false_eq_true]
      have hm_pos : 0 < m := by
        have h1 : stride.toNat ≤ K.toNat - w.toNat := by omega
        have h2 := Nat.div_pos h1 hpos
        omega
      have hone : cost + 1 ≤ m * (cost + 1) := Nat.le_mul_of_pos_left _ hm_pos
      have hclk : state.clock ≠ 0 := by omega
      rw [if_neg hclk, fixClockHOLFinite_evaluateState]
      have stepRun := counted.run (decClockHOLFinite state) code w atCounter
        (by change cost ≤ state.clock - 1; omega)
      have frame := evaluate_avoidsLocal_flowing limit body preservesLimit (decClockHOLFinite state)
      have hnb := evaluate_noTopBreak body noBreak (decClockHOLFinite state)
      rcases bodyRun : evaluateHOLFiniteState (decClockHOLFinite state) body with ⟨res, mid⟩
      rw [bodyRun] at stepRun frame hnb
      dsimp only at stepRun frame hnb
      obtain ⟨spent, kept, safe, noCont, advance⟩ := stepRun
      change state.clock - 1 ≤ mid.clock + cost at spent
      change mid.clock ≤ state.clock - 1 at kept
      cases res with
      | none =>
        dsimp only
        obtain ⟨nextCounter, nextCode⟩ := advance rfl
        have hadd : (w + stride).toNat = w.toNat + stride.toNat :=
          BitVec.toNat_add_of_lt (by omega)
        have hsub_eq : K.toNat - (w + stride).toNat + stride.toNat = K.toNat - w.toNat := by
          rw [hadd]
          omega
        have hdiv_step : (K.toNat - w.toNat) / stride.toNat =
            (K.toNat - (w + stride).toNat) / stride.toNat + 1 := by
          rw [← hsub_eq, Nat.add_div_right _ hpos]
        let m' := (K.toNat - (w + stride).toNat) / stride.toNat
        have hm' : m'.succ = m := by omega
        have nextLimit : mid.locals.lookup limit = some (.val (.word K)) := by
          rw [frame (Or.inl rfl)]
          exact atLimit
        have hdec : m' * (cost + 1) + (cost + 1) = m * (cost + 1) := by
          rw [← Nat.succ_mul, hm']
        obtain ⟨t1, t2, t3, t4⟩ := ih m' (by omega) mid (nextCode.trans code)
          (w + stride) nextCounter nextLimit (by rw [hadd]; omega) rfl (by omega)
        refine ⟨by omega, by omega, t3, fun hnorm => ?_⟩
        obtain ⟨w', hw1, hw2, hw3, hw4, hw5, hw6⟩ := t4 hnorm
        exact ⟨w', hw1, hw2, by rw [hadd] at hw3; omega, hw4, hw5, hw6.trans nextCode⟩
      | some r =>
        cases r with
        | «continue» => exact absurd rfl noCont
        | «break» => exact absurd rfl hnb
        | timeOut => exact absurd rfl safe
        | _ => exact ⟨by simp; omega, by simp; omega, by simp, fun h => by simp at h⟩
    · rw [if_neg hle]
      dsimp only
      have hzero : ¬ ((0 : BitVec 64) ≠ 0) := by decide
      rw [if_neg hzero]
      dsimp only
      exact ⟨by omega, le_refl _, by simp, fun _ => ⟨w, atCounter, atLimit, le_refl _, hw, by omega, rfl⟩⟩

theorem funBounded_ld_le32 : FunBounded (ofString "ld_le32") 0 :=
  funBounded_of_guestAst 20 (by rw [guestAst_len]; decide) Guest.Software.guestFn_ld_le32 0 rfl
    (ProgBounded.straight _ rfl)

theorem funBounded_ld_le64 : FunBounded (ofString "ld_le64") 0 :=
  funBounded_of_guestAst 21 (by rw [guestAst_len]; decide) Guest.Software.guestFn_ld_le64 0 rfl
    (ProgBounded.straight _ rfl)

theorem funBounded_ld_be32 : FunBounded (ofString "ld_be32") 0 :=
  funBounded_of_guestAst 22 (by rw [guestAst_len]; decide) Guest.Software.guestFn_ld_be32 0 rfl
    (ProgBounded.straight _ rfl)

theorem funBounded_bswap64 : FunBounded (ofString "bswap64") 0 :=
  funBounded_of_guestAst 23 (by rw [guestAst_len]; decide) Guest.Software.guestFn_bswap64 0 rfl
    (ProgBounded.straight _ rfl)

theorem funBounded_ld_be64 : FunBounded (ofString "ld_be64") 1 := by
  refine funBounded_of_guestAst 24 (by rw [guestAst_len]; decide) Guest.Software.guestFn_ld_be64 1 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_ld_be64,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.seq (ProgBounded.iteMax _ (ProgBounded.tail funBounded_bswap64 _) (ProgBounded.straight _ rfl))
      (ProgBounded.straight _ rfl))
    (by decide)

theorem funBounded_st_le32 : FunBounded (ofString "st_le32") 0 :=
  funBounded_of_guestAst 25 (by rw [guestAst_len]; decide) Guest.Software.guestFn_st_le32 0 rfl
    (ProgBounded.straight _ rfl)

theorem funBounded_st_le64 : FunBounded (ofString "st_le64") 2 := by
  refine funBounded_of_guestAst 26 (by rw [guestAst_len]; decide) Guest.Software.guestFn_st_le64 2 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_st_le64,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.seq (ProgBounded.call funBounded_st_le32 none _)
      (ProgBounded.seq (ProgBounded.call funBounded_st_le32 none _) (ProgBounded.straight _ rfl)))
    (by decide)

theorem funBounded_st_be32 : FunBounded (ofString "st_be32") 0 :=
  funBounded_of_guestAst 27 (by rw [guestAst_len]; decide) Guest.Software.guestFn_st_be32 0 rfl
    (ProgBounded.straight _ rfl)

theorem funBounded_st_be64 : FunBounded (ofString "st_be64") 3 := by
  refine funBounded_of_guestAst 28 (by rw [guestAst_len]; decide) Guest.Software.guestFn_st_be64 3 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_st_be64,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.seq
      (ProgBounded.iteMax _
        (ProgBounded.decCall funBounded_bswap64 _ _ _ (ProgBounded.straight _ rfl))
        (ProgBounded.straight _ rfl))
      (ProgBounded.seq (ProgBounded.call funBounded_st_be32 none _)
        (ProgBounded.seq (ProgBounded.call funBounded_st_be32 none _) (ProgBounded.straight _ rfl))))
    (by decide)

theorem funBounded_addr_from_words : FunBounded (ofString "addr_from_words") 9 := by
  refine funBounded_of_guestAst 860 (by rw [guestAst_len]; decide) Guest.Software.guestFn_addr_from_words 9 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_addr_from_words,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural, List.map, Option.map]
  exact ProgBounded.weaken
    (ProgBounded.seq (ProgBounded.call funBounded_st_be32 none _)
      (ProgBounded.seq (ProgBounded.call funBounded_st_be64 none _)
        (ProgBounded.seq (ProgBounded.call funBounded_st_be64 none _) (ProgBounded.straight _ rfl))))
    (by decide)

private theorem runBounded_notLowerStride_and_lowerTail {F : Type}
    (state : PanSemStateFiniteExact 64 F) (K : BitVec 64)
    (hsmall : K.toNat + 32 < 2 ^ 64)
    {b32 b8a b8b b1 : ProgHOL 64}
    (hb32 : CountedBody (ofString "i") 32 b32 0)
    (hb32_lim : avoidsLocal (ofString "n") b32 = true)
    (hb32_nb : noTopBreak b32 = true)
    (hb8a : CountedBody (ofString "i") 8 b8a 0)
    (hb8a_lim : avoidsLocal (ofString "n") b8a = true)
    (hb8a_nb : noTopBreak b8a = true)
    (hb8b : CountedBody (ofString "i") 8 b8b 0)
    (hb8b_lim : avoidsLocal (ofString "n") b8b = true)
    (hb8b_nb : noTopBreak b8b = true)
    (hb1 : CountedBody (ofString "i") 1 b1 0)
    (hb1_lim : avoidsLocal (ofString "n") b1 = true)
    {pre tail : ProgHOL 64} {preCost : Nat}
    (hpre : ProgBounded pre preCost)
    (hpre_i : avoidsLocal (ofString "i") pre = true)
    (hpre_n : avoidsLocal (ofString "n") pre = true)
    (htail : ProgBounded tail 0)
    (condAlign : ExpHOL 64)
    (hcode : state.code = originalRuntimeCode)
    (atN : state.locals.lookup (ofString "n") = some (.val (.word K)))
    (hbudget : preCost + K.toNat / 8 + 7 ≤ state.clock) :
    RunBounded state
      (.dec (ofString "i") .one (.const 0)
        (.seq
          (.ite condAlign
            (.seq pre
              (.seq
                (.while (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 32])) b32)
                (.while (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 8])) b8a)))
            .skip)
          (.seq
            (.while (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 8])) b8b)
            (.seq
              (.while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) b1)
              tail))))
      (preCost + K.toNat / 8 + 7) := by
  apply RunBounded.decConst
  let s0 := setVarHOLFinite (ofString "i") (.val (.word 0)) state
  have hs0_code : s0.code = originalRuntimeCode := hcode
  have hs0_i : s0.locals.lookup (ofString "i") = some (.val (.word 0)) := by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs0_n : s0.locals.lookup (ofString "n") = some (.val (.word K)) := by
    have hne : ofString "i" ≠ ofString "n" := by decide
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, atN]
  have hs0_clk : s0.clock = state.clock := rfl
  let firstBranch :=
    ProgHOL.ite condAlign
      (.seq pre
        (.seq
          (.while (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 32])) b32)
          (.while (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 8])) b8a)))
      .skip
  have hfirst :
      ∃ c1 : Nat,
        s0.clock ≤ (evaluateHOLFiniteState s0 firstBranch).2.clock + c1 ∧
        (evaluateHOLFiniteState s0 firstBranch).2.clock ≤ s0.clock ∧
        (evaluateHOLFiniteState s0 firstBranch).1 ≠ some .timeOut ∧
        ((evaluateHOLFiniteState s0 firstBranch).1 ≠ none → c1 ≤ preCost + K.toNat / 8) ∧
        ((evaluateHOLFiniteState s0 firstBranch).1 = none →
          ∃ w1 : BitVec 64,
            (evaluateHOLFiniteState s0 firstBranch).2.locals.lookup (ofString "i") = some (.val (.word w1)) ∧
            (evaluateHOLFiniteState s0 firstBranch).2.locals.lookup (ofString "n") = some (.val (.word K)) ∧
            w1.toNat ≤ K.toNat ∧
            c1 + (K.toNat - w1.toNat) / 8 ≤ preCost + K.toNat / 8 ∧
            (evaluateHOLFiniteState s0 firstBranch).2.code = originalRuntimeCode) := by
    dsimp only [firstBranch]
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · rw [evaluateHOLFiniteState_skip]
        dsimp only
        refine ⟨0, by omega, le_refl _, by simp, fun h => absurd rfl h, fun _ => ?_⟩
        exact ⟨0, hs0_i, hs0_n, by simp, by simp, hs0_code⟩
      · rw [evaluateHOLFiniteState_seq_line780]
        have hpre_run := hpre s0 hs0_code (by omega)
        have hpre_fi := evaluate_avoidsLocal_flowing (ofString "i") pre hpre_i s0
        have hpre_fn := evaluate_avoidsLocal_flowing (ofString "n") pre hpre_n s0
        have hpre_meta := PanRunBounded.evaluateHOLFiniteState_metadata s0 pre
        rcases hp : evaluateHOLFiniteState s0 pre with ⟨rpre, s1⟩
        rw [hp] at hpre_run hpre_fi hpre_fn hpre_meta
        dsimp only at hpre_run hpre_fi hpre_fn hpre_meta ⊢
        cases rpre with
        | some r =>
          dsimp only
          exact ⟨preCost, hpre_run.1, hpre_run.2.1, hpre_run.2.2, fun _ => by omega, fun h => by simp at h⟩
        | none =>
          dsimp only
          have hs1_i : s1.locals.lookup (ofString "i") = some (.val (.word 0)) :=
            (hpre_fi (Or.inl rfl)).trans hs0_i
          have hs1_n : s1.locals.lookup (ofString "n") = some (.val (.word K)) :=
            (hpre_fn (Or.inl rfl)).trans hs0_n
          have hs1_code : s1.code = originalRuntimeCode := hpre_meta.1.trans hs0_code
          rw [evaluateHOLFiniteState_seq_line780]
          have h32 := notLowerStrideWhile_run (ofString "i") (ofString "n") K 32
            (by simpa using hsmall) (by decide) hb32 hb32_lim hb32_nb
            (K.toNat / 32) s1 hs1_code 0 hs1_i hs1_n (by simp) (by simp)
            (by have := hpre_run.1; simp; omega)
          rcases hr32 : evaluateHOLFiniteState s1
              (.while (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 32])) b32)
              with ⟨res32, s2⟩
          rw [hr32] at h32
          dsimp only at h32 ⊢
          cases res32 with
          | some r =>
            dsimp only
            exact ⟨preCost + K.toNat / 32, by omega, by omega, h32.2.2.1, fun _ => by omega, fun h => by simp at h⟩
          | none =>
            dsimp only
            obtain ⟨w32, hw32_i, hw32_n, _, hw32_le, hw32_rem, hs2_code⟩ := h32.2.2.2 rfl
            have hw32_lt32 : K.toNat - w32.toNat < 32 := by
              change K.toNat < w32.toNat + 32 at hw32_rem
              omega
            have hrem3 : (K.toNat - w32.toNat) / 8 ≤ 3 := by omega
            have hdiv32 : K.toNat / 32 + (K.toNat - w32.toNat) / 8 ≤ K.toNat / 8 := by
              omega
            have h8a := notLowerStrideWhile_run (ofString "i") (ofString "n") K 8
              (by change K.toNat + 8 < 2 ^ 64; omega) (by decide) hb8a hb8a_lim hb8a_nb
              ((K.toNat - w32.toNat) / 8) s2 (hs2_code.trans hs1_code) w32 hw32_i hw32_n hw32_le rfl
              (by
                have := hpre_run.1
                have := h32.1
                simp only [Nat.zero_add, Nat.mul_one] at *
                omega)
            rcases hr8a : evaluateHOLFiniteState s2
                (.while (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 8])) b8a)
                with ⟨res8a, s3⟩
            rw [hr8a] at h8a
            dsimp only at h8a ⊢
            have hc1_le : preCost + K.toNat / 32 + (K.toNat - w32.toNat) / 8 ≤ preCost + K.toNat / 8 := by
              omega
            refine ⟨preCost + K.toNat / 32 + (K.toNat - w32.toNat) / 8,
              by simp only [Nat.zero_add, Nat.mul_one] at h32 h8a; omega,
              by omega, h8a.2.2.1, fun _ => hc1_le, fun hnorm => ?_⟩
            obtain ⟨w8a, hw8a_i, hw8a_n, _, hw8a_le, hw8a_rem, hs3_code⟩ := h8a.2.2.2 hnorm
            have hw8a_lt8 : K.toNat - w8a.toNat < 8 := by
              change K.toNat < w8a.toNat + 8 at hw8a_rem
              omega
            exact ⟨w8a, hw8a_i, hw8a_n, hw8a_le, by omega, hs3_code.trans (hs2_code.trans hs1_code)⟩
    · refine ⟨0, by simp, by simp, by simp, fun _ => by omega, fun h => by simp at h⟩
  obtain ⟨c1, hc1_spent, hc1_kept, hc1_safe, hc1_abrupt, hc1_norm⟩ := hfirst
  change RunBounded s0 _ _
  unfold RunBounded
  rw [evaluateHOLFiniteState_seq_line780]
  rcases hf : evaluateHOLFiniteState s0 firstBranch with ⟨rf, sf⟩
  rw [hf] at hc1_spent hc1_kept hc1_safe hc1_abrupt hc1_norm
  dsimp only at hc1_spent hc1_kept hc1_safe hc1_abrupt hc1_norm ⊢
  cases rf with
  | some r =>
    dsimp only
    have hc1_bound := hc1_abrupt (by simp)
    exact ⟨by omega, hc1_kept, hc1_safe⟩
  | none =>
    dsimp only
    obtain ⟨w1, hsf_i, hsf_n, hw1_le, hc1_rem, hsf_code⟩ := hc1_norm rfl
    rw [evaluateHOLFiniteState_seq_line780]
    have h8b := notLowerStrideWhile_run (ofString "i") (ofString "n") K 8
      (by change K.toNat + 8 < 2 ^ 64; omega) (by decide) hb8b hb8b_lim hb8b_nb
      ((K.toNat - w1.toNat) / 8) sf hsf_code w1 hsf_i hsf_n hw1_le rfl
      (by simp only [Nat.zero_add, Nat.mul_one]; omega)
    rcases hr8b : evaluateHOLFiniteState sf
        (.while (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 8])) b8b)
        with ⟨res8b, sg⟩
    rw [hr8b] at h8b
    dsimp only at h8b ⊢
    cases res8b with
    | some r =>
      dsimp only
      exact ⟨by simp only [Nat.zero_add, Nat.mul_one] at h8b; omega, by omega, h8b.2.2.1⟩
    | none =>
      dsimp only
      obtain ⟨w2, hsg_i, hsg_n, _, hw2_le, hw2_rem, hsg_code⟩ := h8b.2.2.2 rfl
      rw [evaluateHOLFiniteState_seq_line780]
      have hrem7 : K.toNat - w2.toNat ≤ 7 := by
        change K.toNat < w2.toNat + 8 at hw2_rem
        omega
      have h1 := variableCountedWhile_run (ofString "i") (ofString "n") .lower (Or.inr rfl) K
        (fun h => by cases h) hb1 hb1_lim (K.toNat - w2.toNat) sg (hsg_code.trans hsf_code)
        w2 hsg_i hsg_n hw2_le rfl
        (by
          simp only [Nat.zero_add, Nat.mul_one] at h8b ⊢
          omega)
      have h1_meta := PanRunBounded.evaluateHOLFiniteState_metadata sg
        (.while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) b1)
      rcases hr1 : evaluateHOLFiniteState sg
          (.while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) b1)
          with ⟨res1, sh⟩
      rw [hr1] at h1 h1_meta
      dsimp only at h1 h1_meta ⊢
      cases res1 with
      | some r =>
        dsimp only
        exact ⟨by simp only [Nat.zero_add, Nat.mul_one] at h8b h1; omega, by omega, h1.2.2⟩
      | none =>
        dsimp only
        have ht := htail sh (h1_meta.1.trans (hsg_code.trans hsf_code)) (by omega)
        exact ⟨by simp only [Nat.zero_add, Nat.mul_one] at h8b h1 ht; omega, by omega, ht.2.2⟩

private theorem runBounded_notLowerStride_noPre {F : Type}
    (state : PanSemStateFiniteExact 64 F) (K : BitVec 64)
    (hsmall : K.toNat + 32 < 2 ^ 64)
    {b32 b8a b8b b1 : ProgHOL 64}
    (hb32 : CountedBody (ofString "i") 32 b32 0)
    (hb32_lim : avoidsLocal (ofString "n") b32 = true)
    (hb32_nb : noTopBreak b32 = true)
    (hb8a : CountedBody (ofString "i") 8 b8a 0)
    (hb8a_lim : avoidsLocal (ofString "n") b8a = true)
    (hb8a_nb : noTopBreak b8a = true)
    (hb8b : CountedBody (ofString "i") 8 b8b 0)
    (hb8b_lim : avoidsLocal (ofString "n") b8b = true)
    (hb8b_nb : noTopBreak b8b = true)
    (hb1 : CountedBody (ofString "i") 1 b1 0)
    (hb1_lim : avoidsLocal (ofString "n") b1 = true)
    {tail : ProgHOL 64} (htail : ProgBounded tail 0)
    (condAlign : ExpHOL 64)
    (hcode : state.code = originalRuntimeCode)
    (atN : state.locals.lookup (ofString "n") = some (.val (.word K)))
    (hbudget : K.toNat / 8 + 7 ≤ state.clock) :
    RunBounded state
      (.dec (ofString "i") .one (.const 0)
        (.seq
          (.ite condAlign
            (.seq
              (.while (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 32])) b32)
              (.while (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 8])) b8a))
            .skip)
          (.seq
            (.while (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const 8])) b8b)
            (.seq
              (.while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) b1)
              tail))))
      (K.toNat / 8 + 7) := by
  have heq :
      ∀ (s : PanSemStateFiniteExact 64 F) (p : ProgHOL 64),
        evaluateHOLFiniteState s (.seq .skip p) = evaluateHOLFiniteState s p := by
    intro s p
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_skip]
  have hite :
      ∀ (s : PanSemStateFiniteExact 64 F) (p : ProgHOL 64),
        evaluateHOLFiniteState s (.ite condAlign (.seq .skip p) .skip) =
          evaluateHOLFiniteState s (.ite condAlign p .skip) := by
    intro s p
    rw [evaluateHOLFiniteState_ite, evaluateHOLFiniteState_ite]
    split
    · split
      · rfl
      · exact heq s p
    · rfl
  have h := runBounded_notLowerStride_and_lowerTail state K hsmall
    hb32 hb32_lim hb32_nb hb8a hb8a_lim hb8a_nb hb8b hb8b_lim hb8b_nb hb1 hb1_lim
    (ProgBounded.straight .skip rfl) rfl rfl htail condAlign hcode atN
    (by simp only [Nat.zero_add]; exact hbudget)
  unfold RunBounded at h ⊢
  simp only [evaluateHOLFiniteState_dec_total, evalHOLExact, shapeOfHOLExact, shapeEqHOL, if_true,
    evaluateHOLFiniteState_seq_line780, hite, Nat.zero_add] at h ⊢
  exact h

private theorem runBounded_memzero_body {F : Type}
    (state : PanSemStateFiniteExact 64 F) (K : BitVec 64)
    (hsmall : K.toNat + 32 < 2 ^ 64)
    (hcode : state.code = originalRuntimeCode)
    (atN : state.locals.lookup (ofString "n") = some (.val (.word K)))
    (hbudget : K.toNat / 8 + 7 ≤ state.clock) :
    RunBounded state (sourceFnBody Guest.Software.guestFn_memzero) (K.toNat / 8 + 7) := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_memzero,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact runBounded_notLowerStride_noPre state K hsmall
    (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
      (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
        (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
          (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl CountedBody.incr))))
    rfl rfl
    (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl CountedBody.incr)
    rfl rfl
    (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
      (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
        (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
          (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
            (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
              (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
                (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
                  (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl CountedBody.incr))))))))
    rfl rfl
    (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl CountedBody.incr)
    rfl
    (ProgBounded.straight _ rfl) _ hcode atN hbudget

private theorem runBounded_memcpy_body {F : Type}
    (state : PanSemStateFiniteExact 64 F) (K : BitVec 64)
    (hsmall : K.toNat + 32 < 2 ^ 64)
    (hcode : state.code = originalRuntimeCode)
    (atN : state.locals.lookup (ofString "n") = some (.val (.word K)))
    (hbudget : K.toNat / 8 + 7 ≤ state.clock) :
    RunBounded state (sourceFnBody Guest.Software.guestFn_memcpy) (K.toNat / 8 + 7) := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_memcpy,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  exact runBounded_notLowerStride_noPre state K hsmall
    (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
      (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
        (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
          (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl CountedBody.incr))))
    rfl rfl
    (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl CountedBody.incr)
    rfl rfl
    (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
      (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
        (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
          (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
            (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
              (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
                (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
                  (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl CountedBody.incr))))))))
    rfl rfl
    (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl CountedBody.incr)
    rfl
    (ProgBounded.straight _ rfl) _ hcode atN hbudget

private theorem evaluate_seq_reassoc3 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (p1 p2 p3 rest : ProgHOL 64) :
    evaluateHOLFiniteState s (.seq p1 (.seq p2 (.seq p3 rest))) =
      evaluateHOLFiniteState s (.seq (.seq p1 (.seq p2 p3)) rest) := by
  simp only [evaluateHOLFiniteState_seq_line780]
  rcases evaluateHOLFiniteState s p1 with ⟨_ | _, s1⟩ <;> dsimp only
  · rcases evaluateHOLFiniteState s1 p2 with ⟨_ | _, s2⟩ <;> rfl

private theorem runBounded_seq_ite_reassoc3 {F : Type}
    (s0 : PanSemStateFiniteExact 64 F) (cost : Nat)
    (cond : ExpHOL 64) (p1 p2 p3 w32 w8 tailProg : ProgHOL 64)
    (hh : RunBounded s0 (.seq (.ite cond (.seq (.seq p1 (.seq p2 p3)) (.seq w32 w8)) .skip) tailProg) (0 + cost)) :
    RunBounded s0 (.seq (.ite cond (.seq p1 (.seq p2 (.seq p3 (.seq w32 w8)))) .skip) tailProg) cost := by
  have heq :
      evaluateHOLFiniteState s0 (.ite cond (.seq p1 (.seq p2 (.seq p3 (.seq w32 w8)))) .skip) =
      evaluateHOLFiniteState s0 (.ite cond (.seq (.seq p1 (.seq p2 p3)) (.seq w32 w8)) .skip) := by
    rw [evaluateHOLFiniteState_ite, evaluateHOLFiniteState_ite]
    split
    · split
      · rfl
      · exact evaluate_seq_reassoc3 s0 p1 p2 p3 (.seq w32 w8)
    · rfl
  unfold RunBounded at hh ⊢
  rw [evaluateHOLFiniteState_seq_line780, heq]
  rw [evaluateHOLFiniteState_seq_line780, Nat.zero_add] at hh
  exact hh

private theorem runBounded_decConst_inv {F : Type}
    (state : PanSemStateFiniteExact 64 F) (name : MlS) (k : BitVec 64) {body : ProgHOL 64} {cost : Nat}
    (h : RunBounded state (.dec name .one (.const k) body) cost) :
    RunBounded (setVarHOLFinite name (.val (.word k)) state) body cost := by
  unfold RunBounded at h ⊢
  rw [evaluateHOLFiniteState_dec_total] at h
  simp only [evalHOLExact, shapeOfHOLExact, shapeEqHOL, if_true] at h
  exact h

private theorem runBounded_memeq_body {F : Type}
    (state : PanSemStateFiniteExact 64 F) (K : BitVec 64)
    (hsmall : K.toNat + 32 < 2 ^ 64)
    (hcode : state.code = originalRuntimeCode)
    (atN : state.locals.lookup (ofString "n") = some (.val (.word K)))
    (hbudget : K.toNat / 8 + 7 ≤ state.clock) :
    RunBounded state (sourceFnBody Guest.Software.guestFn_memeq) (K.toNat / 8 + 7) := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_memeq,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  apply RunBounded.decConst
  apply runBounded_seq_ite_reassoc3
  exact runBounded_decConst_inv state (ofString "i") 0
    (runBounded_notLowerStride_and_lowerTail state K hsmall
      (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
        (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
          (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
            (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl CountedBody.incr))))
      rfl rfl
      (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl CountedBody.incr)
      rfl rfl
      (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
        (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
          (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
            (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
              (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
                (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
                  (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl
                    (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl CountedBody.incr))))))))
      rfl rfl
      (CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl CountedBody.incr)
      rfl
      (ProgBounded.straight _ rfl) rfl rfl (ProgBounded.straight _ rfl) _ hcode atN
      (by simp only [Nat.zero_add]; exact hbudget))

private theorem two_arg_lookup_n (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (fn p1 : MlS) (body : ProgHOL 64) (hp : p1 ≠ ofString "n")
    (hlookup_fn : code fn = some ([(p1, .one), (ofString "n", .one)], body, .one))
    {v1 : ValueHOL 64} {K : BitVec 64}
    {foundBody : ProgHOL 64} {locals : HolFiniteMapExact MlS (ValueHOL 64)} {rs : ShapeHOL}
    (hfound : PanSemStateFiniteExact.lookupCodeHOLFinite code fn [v1, .val (.word K)] =
      some (foundBody, locals, rs)) :
    foundBody = body ∧ locals.lookup (ofString "n") = some (.val (.word K)) := by
  have hbody := lookupCodeHOLFinite_installed_body code fn _ body foundBody .one rs
    [v1, .val (.word K)] locals hlookup_fn hfound
  refine ⟨hbody, ?_⟩
  cases v1 with
  | val wl =>
    cases wl with
    | word w1 =>
      rw [pan_two_word_lookup code fn p1 (ofString "n") body w1 K hp hlookup_fn] at hfound
      cases hfound
      simp [HolFiniteMapExact.lookup_update, FUPDATE]
  | rStruct _ =>
    unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hfound
    split at hfound
    · cases hfound
    · rename_i _ _ _ raw
      simp [lookupCodeHOLExact, hlookup_fn, shapeOfHOLExact, shapeEqHOL] at raw
  | nStruct _ _ =>
    unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hfound
    split at hfound
    · cases hfound
    · rename_i _ _ _ raw
      simp [lookupCodeHOLExact, hlookup_fn, shapeOfHOLExact, shapeEqHOL] at raw

private theorem three_arg_lookup_n (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (fn p1 p2 : MlS) (body : ProgHOL 64)
    (hp12 : p1 ≠ p2) (hp1n : p1 ≠ ofString "n") (hp2n : p2 ≠ ofString "n")
    (hlookup_fn : code fn = some ([(p1, .one), (p2, .one), (ofString "n", .one)], body, .one))
    {v1 v2 : ValueHOL 64} {K : BitVec 64}
    {foundBody : ProgHOL 64} {locals : HolFiniteMapExact MlS (ValueHOL 64)} {rs : ShapeHOL}
    (hfound : PanSemStateFiniteExact.lookupCodeHOLFinite code fn [v1, v2, .val (.word K)] =
      some (foundBody, locals, rs)) :
    foundBody = body ∧ locals.lookup (ofString "n") = some (.val (.word K)) := by
  have hbody := lookupCodeHOLFinite_installed_body code fn _ body foundBody .one rs
    [v1, v2, .val (.word K)] locals hlookup_fn hfound
  refine ⟨hbody, ?_⟩
  cases v1 with
  | rStruct _ =>
    unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hfound
    split at hfound
    · cases hfound
    · rename_i _ _ _ raw
      simp [lookupCodeHOLExact, hlookup_fn, shapeOfHOLExact, shapeEqHOL] at raw
  | nStruct _ _ =>
    unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hfound
    split at hfound
    · cases hfound
    · rename_i _ _ _ raw
      simp [lookupCodeHOLExact, hlookup_fn, shapeOfHOLExact, shapeEqHOL] at raw
  | val wl1 =>
    cases wl1 with
    | word w1 =>
      cases v2 with
      | rStruct _ =>
        unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hfound
        split at hfound
        · cases hfound
        · rename_i _ _ _ raw
          simp [lookupCodeHOLExact, hlookup_fn, shapeOfHOLExact, shapeEqHOL] at raw
      | nStruct _ _ =>
        unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hfound
        split at hfound
        · cases hfound
        · rename_i _ _ _ raw
          simp [lookupCodeHOLExact, hlookup_fn, shapeOfHOLExact, shapeEqHOL] at raw
      | val wl2 =>
        cases wl2 with
        | word w2 =>
          rw [pan_three_word_lookup code fn p1 p2 (ofString "n") body w1 w2 K hp12 hp1n hp2n hlookup_fn] at hfound
          cases hfound
          simp [HolFiniteMapExact.lookup_update, FUPDATE]

private theorem runBounded_is_zero_bytes_body {F : Type}
    (state : PanSemStateFiniteExact 64 F) (K : BitVec 64)
    (hcode : state.code = originalRuntimeCode)
    (atN : state.locals.lookup (ofString "n") = some (.val (.word K)))
    (hbudget : K.toNat ≤ state.clock) :
    RunBounded state (sourceFnBody Guest.Software.guestFn_is_zero_bytes) K.toNat := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_is_zero_bytes,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  apply RunBounded.decConst
  let s0 := setVarHOLFinite (ofString "i") (.val (.word 0)) state
  have hs0_code : s0.code = originalRuntimeCode := hcode
  have hs0_i : s0.locals.lookup (ofString "i") = some (.val (.word 0)) := by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs0_n : s0.locals.lookup (ofString "n") = some (.val (.word K)) := by
    have hne : ofString "i" ≠ ofString "n" := by decide
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, atN]
  have hbody :
      CountedBody (ofString "i") 1
        (.seq
          (.ite (.cmp .notEqual (.loadByte (.op .add [.var .local (ofString "p"), .var .local (ofString "i")])) (.const 0))
            (.return (.const 0))
            .skip)
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1]))) 0 :=
    CountedBody.seq _ (ProgBounded.straight _ rfl) rfl rfl CountedBody.incr
  have hloop := variableCountedWhile_run (ofString "i") (ofString "n") .lower (Or.inr rfl) K
    (fun h => by cases h) hbody rfl K.toNat s0 hs0_code 0 hs0_i hs0_n (by simp) (by simp)
    (by simp only [Nat.zero_add, Nat.mul_one]; exact hbudget)
  simp only [Nat.zero_add, Nat.mul_one] at hloop
  exact (RunBounded.seq hloop (a := K.toNat) (b := 0)
    (by change K.toNat + 0 ≤ state.clock; omega)
    (fun next _ nextCode nextBudget =>
      (ProgBounded.straight (.return (.const 1)) rfl) next (nextCode.trans hs0_code) nextBudget)).weaken (by omega)

private theorem evalListHOLFinite_two_word2 {F : Type}
    (state : PanSemStateFiniteExact 64 F) (e1 e2 : ExpHOL 64) (K : BitVec 64) {vs : List (ValueHOL 64)}
    (hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) [e1, e2] = some vs)
    (hk : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) e2 = some (.val (.word K))) :
    ∃ v1, vs = [v1, .val (.word K)] := by
  rw [evalListHOLFinite_eq_toExact] at hargs
  rw [evalHOLFinite_eq_toExact] at hk
  simp only [evalListHOLExact] at hargs
  rw [hk] at hargs
  rcases h1 : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a)) e1 with _ | v1
  · rw [h1] at hargs
    cases hargs
  · rw [h1] at hargs
    cases hargs
    exact ⟨v1, rfl⟩

private theorem evalListHOLFinite_three_word3 {F : Type}
    (state : PanSemStateFiniteExact 64 F) (e1 e2 e3 : ExpHOL 64) (K : BitVec 64) {vs : List (ValueHOL 64)}
    (hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) [e1, e2, e3] = some vs)
    (hk : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) e3 = some (.val (.word K))) :
    ∃ v1 v2, vs = [v1, v2, .val (.word K)] := by
  rw [evalListHOLFinite_eq_toExact] at hargs
  rw [evalHOLFinite_eq_toExact] at hk
  simp only [evalListHOLExact] at hargs
  rw [hk] at hargs
  rcases h1 : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a)) e1 with _ | v1
  · rw [h1] at hargs
    cases hargs
  · rw [h1] at hargs
    rcases h2 : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a)) e2 with _ | v2
    · rw [h2] at hargs
      cases hargs
    · rw [h2] at hargs
      cases hargs
      exact ⟨v1, v2, rfl⟩

theorem progBounded_memzero_exp (destination : Option (VarKind × MlS)) (dst sizeExp : ExpHOL 64)
    (K : BitVec 64) (hsmall : K.toNat + 32 < 2 ^ 64)
    (heval : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) sizeExp = some (.val (.word K))) :
    ProgBounded (.call (some (destination, none)) (ofString "memzero") [dst, sizeExp]) (K.toNat / 8 + 8) := by
  intro F state hcode hbudget
  cases hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) [dst, sizeExp] with
  | none =>
    rw [evaluateHOLFiniteState_call, hargs]
    simp
  | some vs =>
    obtain ⟨v1, rfl⟩ := evalListHOLFinite_two_word2 state dst sizeExp K hargs (heval state)
    exact RunBounded.call hargs hbudget (fun body locals rs hfound => by
      rw [hcode] at hfound
      obtain ⟨rfl, hn⟩ := two_arg_lookup_n originalRuntimeCode.lookup
        (ofString "memzero") (ofString "dst") (sourceFnBody Guest.Software.guestFn_memzero)
        (by decide) lookup_memzero hfound
      exact runBounded_memzero_body (callEntryStateHOLFinite state locals) K hsmall hcode hn
        (by change K.toNat / 8 + 7 ≤ state.clock - 1; omega))

theorem progBounded_memzero_const (destination : Option (VarKind × MlS)) (dst : ExpHOL 64)
    (K : BitVec 64) (hsmall : K.toNat + 32 < 2 ^ 64) :
    ProgBounded (.call (some (destination, none)) (ofString "memzero") [dst, .const K]) (K.toNat / 8 + 8) :=
  progBounded_memzero_exp destination dst (.const K) K hsmall
    (fun s => by rw [evalHOLFinite_eq_toExact]; rfl)

theorem progBounded_memzero_mul_const (destination : Option (VarKind × MlS)) (dst : ExpHOL 64)
    (a b : BitVec 64) (hsmall : (a * b).toNat + 32 < 2 ^ 64) :
    ProgBounded (.call (some (destination, none)) (ofString "memzero") [dst, .panop .mul [.const a, .const b]])
      ((a * b).toNat / 8 + 8) :=
  progBounded_memzero_exp destination dst (.panop .mul [.const a, .const b]) (a * b) hsmall
    (fun s => by
      rw [evalHOLFinite_eq_toExact]
      simp [evalHOLExact, evalListHOLExact, panOpHOL, valueIsWord, valueWord])

theorem progBounded_memcpy_exp (destination : Option (VarKind × MlS)) (dst src sizeExp : ExpHOL 64)
    (K : BitVec 64) (hsmall : K.toNat + 32 < 2 ^ 64)
    (heval : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) sizeExp = some (.val (.word K))) :
    ProgBounded (.call (some (destination, none)) (ofString "memcpy") [dst, src, sizeExp]) (K.toNat / 8 + 8) := by
  intro F state hcode hbudget
  cases hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) [dst, src, sizeExp] with
  | none =>
    rw [evaluateHOLFiniteState_call, hargs]
    simp
  | some vs =>
    obtain ⟨v1, v2, rfl⟩ := evalListHOLFinite_three_word3 state dst src sizeExp K hargs (heval state)
    exact RunBounded.call hargs hbudget (fun body locals rs hfound => by
      rw [hcode] at hfound
      obtain ⟨rfl, hn⟩ := three_arg_lookup_n originalRuntimeCode.lookup
        (ofString "memcpy") (ofString "dst") (ofString "src") (sourceFnBody Guest.Software.guestFn_memcpy)
        (by decide) (by decide) (by decide) lookup_memcpy hfound
      exact runBounded_memcpy_body (callEntryStateHOLFinite state locals) K hsmall hcode hn
        (by change K.toNat / 8 + 7 ≤ state.clock - 1; omega))

theorem progBounded_memcpy_const (destination : Option (VarKind × MlS)) (dst src : ExpHOL 64)
    (K : BitVec 64) (hsmall : K.toNat + 32 < 2 ^ 64) :
    ProgBounded (.call (some (destination, none)) (ofString "memcpy") [dst, src, .const K]) (K.toNat / 8 + 8) :=
  progBounded_memcpy_exp destination dst src (.const K) K hsmall
    (fun s => by rw [evalHOLFinite_eq_toExact]; rfl)

theorem progBounded_memeq_const (destination : Option (VarKind × MlS)) (a b : ExpHOL 64)
    (K : BitVec 64) (hsmall : K.toNat + 32 < 2 ^ 64) :
    ProgBounded (.call (some (destination, none)) (ofString "memeq") [a, b, .const K]) (K.toNat / 8 + 8) := by
  intro F state hcode hbudget
  cases hargs : evalListHOLFinite state (h := fun addr => Classical.propDecidable (state.memaddrs addr)) [a, b, .const K] with
  | none =>
    rw [evaluateHOLFiniteState_call, hargs]
    simp
  | some vs =>
    obtain ⟨v1, v2, rfl⟩ := evalListHOLFinite_three_word3 state a b (.const K) K hargs
      (by rw [evalHOLFinite_eq_toExact]; rfl)
    exact RunBounded.call hargs hbudget (fun body locals rs hfound => by
      rw [hcode] at hfound
      obtain ⟨rfl, hn⟩ := three_arg_lookup_n originalRuntimeCode.lookup
        (ofString "memeq") (ofString "a") (ofString "b") (sourceFnBody Guest.Software.guestFn_memeq)
        (by decide) (by decide) (by decide) lookup_memeq hfound
      exact runBounded_memeq_body (callEntryStateHOLFinite state locals) K hsmall hcode hn
        (by change K.toNat / 8 + 7 ≤ state.clock - 1; omega))

theorem progBounded_memeq_decCall_const (name : MlS) (shape : ShapeHOL) (a b : ExpHOL 64)
    (K : BitVec 64) {continuation : ProgHOL 64} {tailCost : Nat}
    (hsmall : K.toNat + 32 < 2 ^ 64)
    (hrest : ProgBounded continuation tailCost) :
    ProgBounded (.decCall name shape (ofString "memeq") [a, b, .const K] continuation)
      (K.toNat / 8 + 8 + tailCost) := by
  intro F state hcode hbudget
  cases hargs : evalListHOLFinite state (h := fun addr => Classical.propDecidable (state.memaddrs addr)) [a, b, .const K] with
  | none =>
    rw [evaluateHOLFiniteState_decCall_args_none state name shape (ofString "memeq") [a, b, .const K] continuation hargs]
    simp
  | some vs =>
    obtain ⟨v1, v2, rfl⟩ := evalListHOLFinite_three_word3 state a b (.const K) K hargs
      (by rw [evalHOLFinite_eq_toExact]; rfl)
    have h := RunBounded.decCall (name := name) (shape := shape) (continuation := continuation)
      (bodyCost := K.toNat / 8 + 7) (tailCost := tailCost) hargs (by omega)
      (fun body locals rs hfound => by
        rw [hcode] at hfound
        obtain ⟨rfl, hn⟩ := three_arg_lookup_n originalRuntimeCode.lookup
          (ofString "memeq") (ofString "a") (ofString "b") (sourceFnBody Guest.Software.guestFn_memeq)
          (by decide) (by decide) (by decide) lookup_memeq hfound
        have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state locals)
          (sourceFnBody Guest.Software.guestFn_memeq)
        refine ⟨runBounded_memeq_body (callEntryStateHOLFinite state locals) K hsmall hcode hn
          (by change K.toNat / 8 + 7 ≤ state.clock - 1; omega), ?_⟩
        intro value post hran hpost_clk
        rw [hran] at hmeta
        exact hrest _ (hmeta.1.trans hcode) hpost_clk)
    exact h.weaken (by omega)

theorem progBounded_is_zero_bytes_const (destination : Option (VarKind × MlS)) (p : ExpHOL 64)
    (K : BitVec 64) :
    ProgBounded (.call (some (destination, none)) (ofString "is_zero_bytes") [p, .const K]) (K.toNat + 1) := by
  intro F state hcode hbudget
  cases hargs : evalListHOLFinite state (h := fun addr => Classical.propDecidable (state.memaddrs addr)) [p, .const K] with
  | none =>
    rw [evaluateHOLFiniteState_call, hargs]
    simp
  | some vs =>
    obtain ⟨v1, rfl⟩ := evalListHOLFinite_two_word2 state p (.const K) K hargs
      (by rw [evalHOLFinite_eq_toExact]; rfl)
    exact RunBounded.call hargs hbudget (fun body locals rs hfound => by
      rw [hcode] at hfound
      obtain ⟨rfl, hn⟩ := two_arg_lookup_n originalRuntimeCode.lookup
        (ofString "is_zero_bytes") (ofString "p") (sourceFnBody Guest.Software.guestFn_is_zero_bytes)
        (by decide) lookup_is_zero_bytes hfound
      exact runBounded_is_zero_bytes_body (callEntryStateHOLFinite state locals) K hcode hn
        (by change K.toNat ≤ state.clock - 1; omega))

theorem progBounded_is_zero_bytes_decCall_const (name : MlS) (shape : ShapeHOL) (p : ExpHOL 64)
    (K : BitVec 64) {continuation : ProgHOL 64} {tailCost : Nat}
    (hrest : ProgBounded continuation tailCost) :
    ProgBounded (.decCall name shape (ofString "is_zero_bytes") [p, .const K] continuation)
      (K.toNat + 1 + tailCost) := by
  intro F state hcode hbudget
  cases hargs : evalListHOLFinite state (h := fun addr => Classical.propDecidable (state.memaddrs addr)) [p, .const K] with
  | none =>
    rw [evaluateHOLFiniteState_decCall_args_none state name shape (ofString "is_zero_bytes") [p, .const K] continuation hargs]
    simp
  | some vs =>
    obtain ⟨v1, rfl⟩ := evalListHOLFinite_two_word2 state p (.const K) K hargs
      (by rw [evalHOLFinite_eq_toExact]; rfl)
    have h := RunBounded.decCall (name := name) (shape := shape) (continuation := continuation)
      (bodyCost := K.toNat) (tailCost := tailCost) hargs (by omega)
      (fun body locals rs hfound => by
        rw [hcode] at hfound
        obtain ⟨rfl, hn⟩ := two_arg_lookup_n originalRuntimeCode.lookup
          (ofString "is_zero_bytes") (ofString "p") (sourceFnBody Guest.Software.guestFn_is_zero_bytes)
          (by decide) lookup_is_zero_bytes hfound
        have hmeta := PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state locals)
          (sourceFnBody Guest.Software.guestFn_is_zero_bytes)
        refine ⟨runBounded_is_zero_bytes_body (callEntryStateHOLFinite state locals) K hcode hn
          (by change K.toNat ≤ state.clock - 1; omega), ?_⟩
        intro value post hran hpost_clk
        rw [hran] at hmeta
        exact hrest _ (hmeta.1.trans hcode) hpost_clk)
    exact h.weaken (by omega)

private theorem countedBody_seq_straight {counter : MlS} {step : BitVec 64}
    (first : ProgHOL 64) {tail : ProgHOL 64} {cost : Nat}
    (hs : extStraightLine first = true)
    (ha : avoidsLocal counter first = true)
    (hn : noTopContinue first = true)
    (hrest : CountedBody counter step tail cost) :
    CountedBody counter step (.seq first tail) cost := by
  simpa using CountedBody.seq first (ProgBounded.straight first hs) ha hn hrest

theorem funBounded_keccak_f1600 : FunBounded (ofString "keccak_f1600") 24 := by
  refine funBounded_of_guestAst 101 (by rw [guestAst_len]; decide) Guest.Software.guestFn_keccak_f1600 24 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_keccak_f1600,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  iterate 25 apply ProgBounded.dec
  refine ProgBounded.weaken
    (ProgBounded.countedDec (ofString "r") .less (Or.inl rfl) 24 1 0
      (by decide) (by decide) (by decide) (cost := 0) ?_ (ProgBounded.straight _ (by decide)))
    (by decide)
  iterate 60 (refine CountedBody.dec _ _ _ (by decide) ?_)
  iterate 26 (refine countedBody_seq_straight _ (by decide) (by decide) (by decide) ?_)
  exact CountedBody.incr

theorem funBounded_keccak_absorb_block : FunBounded (ofString "keccak_absorb_block") 161 := by
  refine funBounded_of_guestAst 102 (by rw [guestAst_len]; decide) Guest.Software.guestFn_keccak_absorb_block 161 rfl ?_
  dsimp only [extractFn, Guest.Software.guestFn_keccak_absorb_block,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  intro F state hcode hbudget
  apply RunBounded.decConst
  let s0 := setVarHOLFinite (ofString "i") (.val (.word 0)) state
  have hs0_code : s0.code = originalRuntimeCode := hcode
  have hs0_i : s0.locals.lookup (ofString "i") = some (.val (.word 0)) := by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have htail : ProgBounded
      (.seq (.call (some (none, none)) (ofString "keccak_f1600") [.var .local (ofString "stp")])
        (.return (.const 0))) 25 :=
    ProgBounded.seq (ProgBounded.call funBounded_keccak_f1600 none [.var .local (ofString "stp")])
      (ProgBounded.straight _ (by decide))
  refine RunBounded.seq ?_ (a := 136) (b := 25) (by change 136 + 25 ≤ state.clock; omega)
    (fun next _ nextCode nextBudget => htail next (nextCode.trans hs0_code) nextBudget)
  apply RunBounded.ite
  · unfold RunBounded
    exact countedWhile_from (ofString "i") .less (Or.inl rfl) 136 8 (by decide) (by decide) (cost := 0)
      (countedBody_seq_straight _ (by decide) (by decide) (by decide) CountedBody.incr)
      s0 hs0_code 0 hs0_i (by decide) (by change 136 * (0 + 1) ≤ state.clock; omega)
  · unfold RunBounded
    exact countedWhile_from (ofString "i") .less (Or.inl rfl) 136 8 (by decide) (by decide) (cost := 0)
      (countedBody_seq_straight _ (by decide) (by decide) (by decide) CountedBody.incr)
      s0 hs0_code 0 hs0_i (by decide) (by change 136 * (0 + 1) ≤ state.clock; omega)

end InitECandidate.Solver.GuestUniformClockBound
