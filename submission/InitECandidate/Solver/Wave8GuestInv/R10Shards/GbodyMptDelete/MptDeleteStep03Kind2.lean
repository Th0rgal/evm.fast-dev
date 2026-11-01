import InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptDelete.MptCuts
set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
namespace InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptDelete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded

namespace MptDeleteKind2

/-! ### 1. Body clock bound & `noTopContinue` -/

private theorem mptDeleteBody_noTopContinue : noTopContinue mptDeleteBody = true := rfl

private theorem mptDeleteBody_bounded (h : MptDeleteCallees) :
    TerminatingProgBoundedOn GuestInv mptDeleteBody mptDeleteCost := by
  dsimp only [mptDeleteBody, mptWhileBody, mptLeft, mptDeleteTail, mptDecBody, mptDeleteCode,
    sourceFunctionEntry, Guest.Software.guestFn__mpt_delete_node_body,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    List.map, Option.map]
  refine TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.seq_guestInv
      (TerminatingProgBoundedOn.of_clock (fun s => clock_assign s _ _ _))
      (TerminatingProgBoundedOn.ite_on
        (TerminatingProgBoundedOn.of_clock (fun s => clock_assign s _ _ _))
        (TerminatingProgBoundedOn.dec_on localsFree_guestInv _ _ _
          (TerminatingProgBoundedOn.seq_guestInv
            (TerminatingProgBoundedOn.ite_on
              (TerminatingProgBoundedOn.call_guestInv h.fb_mpt_fail _ _)
              (TerminatingProgBoundedOn.of_clock clock_skip))
            (TerminatingProgBoundedOn.seq_guestInv
              (TerminatingProgBoundedOn.call_guestInv h.fb_node_invalidate _ _)
              (TerminatingProgBoundedOn.ite_on
                (TerminatingProgBoundedOn.seq_guestInv
                  (TerminatingProgBoundedOn.of_clock (fun s => clock_assign s _ _ _))
                  (TerminatingProgBoundedOn.ite_on
                    (TerminatingProgBoundedOn.decCall_guestInv h.fb_memeq _ _ _
                      (TerminatingProgBoundedOn.ite_on
                        (TerminatingProgBoundedOn.of_clock (fun s => clock_assign s _ _ _))
                        (TerminatingProgBoundedOn.of_clock clock_skip)))
                    (TerminatingProgBoundedOn.of_clock clock_skip)))
                (TerminatingProgBoundedOn.ite_on
                  (TerminatingProgBoundedOn.dec_on localsFree_guestInv _ _ _
                    (TerminatingProgBoundedOn.dec_on localsFree_guestInv _ _ _
                      (TerminatingProgBoundedOn.decCall_guestInv h.fb_common_prefix_length _ _ _
                        (TerminatingProgBoundedOn.ite_on
                          (TerminatingProgBoundedOn.of_clock (fun s => clock_assign s _ _ _))
                          (TerminatingProgBoundedOn.decCall_guestInv h.fb_scratch_alloc _ _ _
                            (TerminatingProgBoundedOn.of_clock
                              (seq_clock (fun s => clock_store s _ _)
                                (seq_clock (fun s => clock_store s _ _)
                                  (seq_clock (fun s => clock_store s _ _)
                                    (seq_clock (fun s => clock_store s _ _)
                                      (seq_clock (fun s => clock_store s _ _)
                                        (seq_clock (fun s => clock_assign s _ _ _)
                                          (seq_clock (fun s => clock_assign s _ _ _)
                                            (seq_clock (fun s => clock_assign s _ _ _)
                                              (fun s => clock_assign s _ _ _)))))))))))))))
                  (TerminatingProgBoundedOn.ite_on
                    (TerminatingProgBoundedOn.ite_on
                      (TerminatingProgBoundedOn.of_clock (fun s => clock_assign s _ _ _))
                      (TerminatingProgBoundedOn.seq_guestInv
                        (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                        (TerminatingProgBoundedOn.seq_guestInv
                          (TerminatingProgBoundedOn.of_clock (fun s => clock_store s _ _))
                          (TerminatingProgBoundedOn.call_guestInv h.fb__collapse_branch _ _))))
                    (TerminatingProgBoundedOn.dec_on localsFree_guestInv _ _ _
                      (TerminatingProgBoundedOn.decCall_guestInv h.fb_scratch_alloc _ _ _
                        (TerminatingProgBoundedOn.of_clock
                          (seq_clock (fun s => clock_store s _ _)
                            (seq_clock (fun s => clock_store s _ _)
                              (seq_clock (fun s => clock_store s _ _)
                                (seq_clock (fun s => clock_store s _ _)
                                  (seq_clock (fun s => clock_assign s _ _ _)
                                    (seq_clock (fun s => clock_assign s _ _ _)
                                      (seq_clock (fun s => clock_assign s _ _ _)
                                        (fun s => clock_assign s _ _ _))))))))))))))))))) ?_
  have hmax : ∀ x y : Nat, Nat.max x y = max x y := fun _ _ => rfl
  unfold mptDeleteCost
  simp only [hmax]
  omega

/-! ### 2. Installed-callee lookups & parameter binding -/

private theorem lookup_scratch_alloc :
    originalRuntimeCode.lookup (ofString "scratch_alloc") =
      some ((sourceFunctionEntry Guest.Software.guestFn_scratch_alloc).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 13 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_scratch_alloc) rfl

private theorem lookup_common_prefix_length :
    originalRuntimeCode.lookup (ofString "common_prefix_length") =
      some ((sourceFunctionEntry Guest.Software.guestFn_common_prefix_length).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 251 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_common_prefix_length) rfl

private theorem lookup_node_invalidate :
    originalRuntimeCode.lookup (ofString "node_invalidate") =
      some ((sourceFunctionEntry Guest.Software.guestFn_node_invalidate).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 259 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_node_invalidate) rfl

private theorem callee_param_one_exp {F : Type} (state : PanSemStateFiniteExact 64 F)
    (fname p1 : MlS) (s1 : ShapeHOL) (body : ProgHOL 64) (ret : ShapeHOL)
    (hl : state.code.lookup fname = some ([(p1, s1)], body, ret))
    (e1 : ExpHOL 64) (values : List (ValueHOL 64)) (body' : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret' : ShapeHOL)
    (hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [e1] = some values)
    (hlook : lookupCodeHOLFinite state.code.lookup fname values = some (body', callee, ret')) :
    ∃ v1, evalAt state e1 = some v1 ∧ callee.lookup p1 = some v1 := by
  rw [evalListHOLFinite_eq_toExact] at hargs
  simp only [evalListHOLExact] at hargs
  rcases he1 : evalAt state e1 with _ | v1
  · simp [evalAt] at he1; simp [he1] at hargs
  · have he1' : @evalHOLExact 64 F _ state.toExact
        (fun a => Classical.propDecidable (state.memaddrs a)) e1 = some v1 := he1
    simp only [he1', Option.some.injEq] at hargs
    subst hargs
    unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hlook
    split at hlook
    · cases hlook
    · rename_i exactBody exactLocals exactShape raw
      have heq := Option.some.inj hlook
      rcases Prod.mk.inj heq with ⟨rfl, hrest⟩
      rcases Prod.mk.inj hrest with ⟨rfl, _⟩
      unfold lookupCodeHOLExact at raw
      rw [hl] at raw
      dsimp only at raw
      split at raw
      · have rawEq := Option.some.inj raw
        rcases Prod.mk.inj rawEq with ⟨-, hrest2⟩
        rcases Prod.mk.inj hrest2 with ⟨hloc, -⟩
        subst hloc
        exact ⟨v1, rfl, by simp [List.zip, List.foldl]⟩
      · cases raw

private theorem callee_param_four_exp {F : Type} (state : PanSemStateFiniteExact 64 F)
    (fname p1 p2 p3 p4 : MlS) (s1 s2 s3 s4 : ShapeHOL) (body : ProgHOL 64) (ret : ShapeHOL)
    (hl : state.code.lookup fname = some ([(p1, s1), (p2, s2), (p3, s3), (p4, s4)], body, ret))
    (e1 e2 e3 e4 : ExpHOL 64) (values : List (ValueHOL 64)) (body' : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret' : ShapeHOL)
    (hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [e1, e2, e3, e4] = some values)
    (hlook : lookupCodeHOLFinite state.code.lookup fname values = some (body', callee, ret')) :
    ∃ v1 v2 v3 v4,
      evalAt state e1 = some v1 ∧ evalAt state e2 = some v2 ∧
      evalAt state e3 = some v3 ∧ evalAt state e4 = some v4 ∧
      callee.lookup p2 = some v2 ∧ callee.lookup p4 = some v4 := by
  rw [evalListHOLFinite_eq_toExact] at hargs
  simp only [evalListHOLExact] at hargs
  rcases he1 : evalAt state e1 with _ | v1 <;>
  rcases he2 : evalAt state e2 with _ | v2 <;>
  rcases he3 : evalAt state e3 with _ | v3 <;>
  rcases he4 : evalAt state e4 with _ | v4 <;>
    simp only [evalAt] at he1 he2 he3 he4 <;>
    simp only [he1, he2, he3, he4, Option.some.injEq] at hargs <;>
    cases hargs
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hlook
  split at hlook
  · cases hlook
  · rename_i exactBody exactLocals exactShape raw
    have heq := Option.some.inj hlook
    rcases Prod.mk.inj heq with ⟨rfl, hrest⟩
    rcases Prod.mk.inj hrest with ⟨rfl, _⟩
    unfold lookupCodeHOLExact at raw
    rw [hl] at raw
    dsimp only at raw
    split at raw
    · rename_i hcond
      have rawEq := Option.some.inj raw
      rcases Prod.mk.inj rawEq with ⟨-, hrest2⟩
      rcases Prod.mk.inj hrest2 with ⟨hloc, -⟩
      subst hloc
      obtain ⟨hnd, -, -⟩ := hcond
      simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons,
        not_or, List.not_mem_nil, or_false] at hnd
      refine ⟨v1, v2, v3, v4, rfl, rfl, rfl, rfl, ?_, ?_⟩
      · simp [List.zip, List.foldl, hnd.2.1.1, hnd.2.1.2]
      · simp [List.zip, List.foldl]
    · cases raw

/-! ### 3. Expression evaluation & fall-through Hoare rules -/

private theorem evalAt_loadL {F : Type} (t : PanSemStateFiniteExact 64 F) (n : String)
    (k : BitVec 64) (v : ValueHOL 64)
    (h : evalAt t (.load .one (.op .add [.var .local (ofString n), .const k])) = some v) :
    ∃ a : BitVec 64, v = .val (.word a) ∧ a.toNat = memW t (locN t n + k.toNat) := by
  simp [evalAt, evalHOLExact, evalListHOLExact] at h
  rcases hl : t.locals.lookup (ofString n) with _ | w
  · simp [hl] at h
  · rcases w with x | fs | ⟨nm, fs⟩
    · cases x with
      | word x =>
        simp [hl, valueIsWord, valueWord, wordOpHOL, wordOp, memLoadHOLExact] at h
        rcases hm : t.memory (x + k) with ⟨y⟩
        have hadd : BitVec.ofNat 64 (x.toNat + k.toNat) = x + k := by
          rw [BitVec.add_def]
        refine ⟨y, by rw [← h.2, hm], ?_⟩
        have hy : ValueHOL.val (.word y) = v := by rw [← h.2, hm]
        subst hy
        simp only [locN, memW, hl, hadd, hm]
    · simp [hl, valueIsWord] at h
    · simp [hl, valueIsWord] at h

private theorem evalAt_add_locals {F : Type} (t : PanSemStateFiniteExact 64 F) (a b : String)
    (v : ValueHOL 64)
    (h : evalAt t (.op .add [.var .local (ofString a), .var .local (ofString b)]) = some v) :
    ∃ wa wb : BitVec 64,
      t.locals.lookup (ofString a) = some (.val (.word wa)) ∧
      t.locals.lookup (ofString b) = some (.val (.word wb)) ∧
      wa.toNat = locN t a ∧ wb.toNat = locN t b ∧
      v = .val (.word (wa + wb)) := by
  simp [evalAt, evalHOLExact, evalListHOLExact] at h
  rcases ha : t.locals.lookup (ofString a) with _ | va <;>
  rcases hb : t.locals.lookup (ofString b) with _ | vb <;>
    simp [ha, hb] at h
  rcases va with xa | _ | _ <;> rcases vb with xb | _ | _ <;>
    simp [valueIsWord] at h
  cases xa with
  | word wa =>
    cases xb with
    | word wb =>
      simp [valueWord, wordOpHOL, wordOp] at h
      exact ⟨wa, wb, rfl, rfl, by simp [locN, ha], by simp [locN, hb], h.symm⟩

private theorem evalAt_sub_locals {F : Type} (t : PanSemStateFiniteExact 64 F) (a b : String)
    (v : ValueHOL 64)
    (h : evalAt t (.op .sub [.var .local (ofString a), .var .local (ofString b)]) = some v) :
    ∃ wa wb : BitVec 64,
      t.locals.lookup (ofString a) = some (.val (.word wa)) ∧
      t.locals.lookup (ofString b) = some (.val (.word wb)) ∧
      wa.toNat = locN t a ∧ wb.toNat = locN t b ∧
      v = .val (.word (wa - wb)) := by
  simp [evalAt, evalHOLExact, evalListHOLExact] at h
  rcases ha : t.locals.lookup (ofString a) with _ | va <;>
  rcases hb : t.locals.lookup (ofString b) with _ | vb <;>
    simp [ha, hb] at h
  rcases va with xa | _ | _ <;> rcases vb with xb | _ | _ <;>
    simp [valueIsWord] at h
  cases xa with
  | word wa =>
    cases xb with
    | word wb =>
      simp [valueWord, wordOpHOL, wordOp] at h
      exact ⟨wa, wb, rfl, rfl, by simp [locN, ha], by simp [locN, hb], h.symm⟩

private theorem condTrue_local_eq_const {F : Type} {t : PanSemStateFiniteExact 64 F}
    {n : String} {k : BitVec 64}
    (h : CondTrue (.cmp .equal (.var .local (ofString n)) (.const k)) t) :
    locN t n = k.toNat := by
  obtain ⟨w, hw, hne⟩ := h
  obtain ⟨a, b, ha, hb, rfl⟩ := cond_local t _ n _ w hw
  cases evalAt_const t k _ hb
  rw [← ha]
  by_cases heq : a = k
  · subst heq; rfl
  · exfalso; apply hne
    simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, heq]

private theorem condFalse_local_eq_const {F : Type} {t : PanSemStateFiniteExact 64 F}
    {n : String} {k : BitVec 64}
    (h : CondFalse (.cmp .equal (.var .local (ofString n)) (.const k)) t) :
    locN t n ≠ k.toNat := by
  obtain ⟨a, b, ha, hb, h0⟩ := cond_local t _ n _ 0 h
  cases evalAt_const t k _ hb
  rw [← ha]
  intro heq
  have hak : a = k := BitVec.eq_of_toNat_eq heq
  subst hak
  simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at h0

private theorem condFalse_local_lower_local {F : Type} {t : PanSemStateFiniteExact 64 F}
    {a b : String}
    (h : CondFalse (.cmp .lower (.var .local (ofString a)) (.var .local (ofString b))) t) :
    locN t b ≤ locN t a := by
  obtain ⟨wa, wb, ha, hb, h0⟩ := evalAt_cmp t .lower _ _ 0 h
  have ha' := evalAt_local t a wa ha
  have hb' := evalAt_local t b wb hb
  rw [← ha', ← hb']
  by_cases hlt : wa < wb
  · exfalso
    simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlt] at h0
  · exact Nat.le_of_not_lt (fun hc => hlt (BitVec.lt_def.mpr hc))

private theorem hoare_seq_fall {P R Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {first second : ProgHOL 64}
    (h1 : Hoare P first (fun r t => r = none → R t))
    (h2 : Hoare R second (fun r t => r = none → Q t)) :
    Hoare P (.seq first second) (fun r t => r = none → Q t) :=
  Hoare.seq ⟨fun s hc hP hnt => ⟨h1.run s hc hP hnt, fun hr h => absurd h hr⟩⟩ h2

private theorem hoare_ite_fall {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {cond : ExpHOL 64} {yes no : ProgHOL 64}
    (hyes : Hoare (fun s => P s ∧ CondTrue cond s) yes (fun r t => r = none → Q t))
    (hno : Hoare (fun s => P s ∧ CondFalse cond s) no (fun r t => r = none → Q t)) :
    Hoare P (.ite cond yes no) (fun r t => r = none → Q t) :=
  Hoare.ite hyes hno (fun _ _ hr => absurd hr (by simp))

private theorem hoare_dec_fall {P P' Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {names : List String} {name : MlS} {shape : ShapeHOL} {init : ExpHOL 64} {body : ProgHOL 64}
    (hname : ∀ n ∈ names, ofString n ≠ name)
    (hQ : LocalsOnly names Q)
    (hinit : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64), P s →
      evalAt s init = some v → P' (setVarHOLFinite name v s))
    (hbody : Hoare P' body (fun r t => r = none → Q t)) :
    Hoare P (.dec name shape init body) (fun r t => r = none → Q t) :=
  Hoare.dec hname hinit hbody
    (fun _ t locals hl h hr => hQ t locals t.clock hl (h hr))
    (fun _ _ hr => absurd hr (by simp))

private theorem hoare_assign_fall {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {kind : VarKind} {name : MlS} {source : ExpHOL 64}
    (h : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64), P s →
      evalAt s source = some v →
      isValidValueHOLExact s.toExact kind name v = true →
      Q (setKvarHOLFinite kind name v s)) :
    Hoare P (.assign kind name source) (fun r t => r = none → Q t) := by
  refine ⟨fun {F} s _ hP _ hr => ?_⟩
  rw [evaluateHOLFiniteState_assign] at hr ⊢
  revert hr
  split
  · simp
  · rename_i v hv
    split
    · rename_i hval
      intro _
      exact h s v hP hv hval
    · simp

private theorem hoare_decCall_fall {P R Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {names : List String} {name fname : MlS} {shape : ShapeHOL}
    {arguments : List (ExpHOL 64)} {cont : ProgHOL 64}
    (hname : ∀ n ∈ names, ofString n ≠ name)
    (hQ : LocalsOnly names Q)
    (hres : DecCallResumeOn P R name fname arguments)
    (hcont : Hoare R cont (fun r t => r = none → Q t)) :
    Hoare P (.decCall name shape fname arguments cont) (fun r t => r = none → Q t) := by
  refine ⟨fun {F} s hcode hP _ hr => ?_⟩
  rcases hrun : evaluateHOLFiniteState s (.decCall name shape fname arguments cont) with ⟨r, post⟩
  rw [hrun] at hr
  dsimp only at hr
  subst hr
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hrun
  rcases hargs : evalListHOLFinite s
      (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments with _ | values
  · rw [hargs] at hrun; simp at hrun
  · rw [hargs] at hrun; dsimp only at hrun
    rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · rw [hl] at hrun; simp at hrun
    · rw [hl] at hrun; dsimp only at hrun
      by_cases hz : s.clock = 0
      · rw [if_pos hz] at hrun; simp at hrun
      · rw [if_neg hz] at hrun
        have hmeta := (evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body').1
        rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with ⟨bres, bpost⟩
        rw [hb] at hrun hmeta
        dsimp only at hmeta
        cases bres with
        | none => simp at hrun
        | some br =>
          cases br with
          | returned v =>
            dsimp only at hrun
            split at hrun
            · set resumed := setVarHOLFinite name v { bpost with locals := s.locals }
              have hresR : R resumed := hres s values body' callee ret' v bpost hcode hP hargs hl hb
              have hresCode : resumed.code = originalRuntimeCode := hmeta.trans hcode
              rcases hc : evaluateHOLFiniteState resumed cont with ⟨cres, cpost⟩
              rw [hc] at hrun
              dsimp only at hrun
              obtain ⟨rfl, hpost_eq⟩ := Prod.mk.inj hrun
              have hQc0 := hcont.run resumed hresCode hresR (by rw [hc]; simp)
              rw [hc] at hQc0
              have hQc : Q cpost := hQc0 rfl
              dsimp only
              rw [← hpost_eq]
              exact hQ cpost _ cpost.clock
                (fun n hn => resVarEq_lookup_ne _ _ _ _ (hname n hn)) hQc
            · simp at hrun
          | _ => simp [emptyLocalsHOLFinite] at hrun

private theorem hoare_call0_fall {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {fname : MlS} {arguments : List (ExpHOL 64)}
    (hres : ∀ {F : Type} (state : PanSemStateFiniteExact 64 F) (values : List (ValueHOL 64))
      (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
      (value : ValueHOL 64) (post : PanSemStateFiniteExact 64 F),
      state.code = originalRuntimeCode → P state →
      evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
        arguments = some values →
      lookupCodeHOLFinite state.code.lookup fname values = some (body, callee, returnShape) →
      evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body =
        (some (.returned value), post) →
      Q { post with locals := state.locals }) :
    Hoare P (.call (some (none, none)) fname arguments) (fun r t => r = none → Q t) := by
  refine ⟨fun {F} s hcode hP _ hr => ?_⟩
  rcases hcall : evaluateHOLFiniteState s (.call (some (none, none)) fname arguments) with ⟨r, t⟩
  rw [hcall] at hr
  dsimp only at hr
  subst hr
  rw [evaluateHOLFiniteState_call] at hcall
  rcases hargs : evalListHOLFinite s
      (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments with _ | values
  · rw [hargs] at hcall; simp at hcall
  · rw [hargs] at hcall; dsimp only at hcall
    rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · rw [hl] at hcall; simp at hcall
    · rw [hl] at hcall; dsimp only at hcall
      by_cases hz : s.clock = 0
      · rw [if_pos hz] at hcall; simp at hcall
      · rw [if_neg hz] at hcall
        rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with ⟨bres, post⟩
        rw [hb] at hcall
        cases bres with
        | none => simp at hcall
        | some br =>
          cases br with
          | returned v =>
            dsimp only at hcall
            split at hcall
            · obtain ⟨_, rfl⟩ := Prod.mk.inj hcall
              exact hres s values body' callee ret' v post hcode hP hargs hl hb
            · simp at hcall
          | _ => simp [emptyLocalsHOLFinite] at hcall

private theorem hoare_store_word_off {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (base : String) (off : BitVec 64) (src : ExpHOL 64)
    (hwv : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64),
      P s → evalAt s src = some v → ∃ wv : BitVec 64, v = .val (.word wv))
    (h : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (wb wv : BitVec 64),
      P s → s.locals.lookup (ofString base) = some (.val (.word wb)) →
      evalAt s src = some (.val (.word wv)) →
      Q { s with memory := fun a => if a = wb + off then .word wv else s.memory a }) :
    Hoare P (.store (.op .add [.var .local (ofString base), .const off]) src)
      (fun r t => r = none → Q t) := by
  refine ⟨fun {F} s _ hP _ hr => ?_⟩
  rw [evaluateHOLFiniteState_store] at hr ⊢
  revert hr
  split
  · rename_i x hx
    split
    · rename_i v hv
      obtain ⟨wv, rfl⟩ := hwv s v hP hv
      have hbase : ∃ wb : BitVec 64,
          s.locals.lookup (ofString base) = some (.val (.word wb)) ∧ x = wb + off := by
        simp [evalHOLExact, evalListHOLExact] at hx
        rcases hb : s.locals.lookup (ofString base) with _ | vb
        · simp [hb] at hx
        · rcases vb with xb | _ | _
          · cases xb with
            | word wb =>
              simp [hb, valueIsWord, valueWord, wordOpHOL, wordOp] at hx
              exact ⟨wb, rfl, hx.symm⟩
          · simp [hb, valueIsWord] at hx
          · simp [hb, valueIsWord] at hx
      obtain ⟨wb, hwb, rfl⟩ := hbase
      simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL]
      by_cases hdom : s.memaddrs (wb + off)
      · simp only [hdom, ↓reduceIte]
        intro _
        exact h s wb wv hP hwb hv
      · simp [hdom]
    · simp
  · simp

private theorem hoare_store_locals_fall {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (dst src : ExpHOL 64)
    (hP : ∀ {F : Type} (s t : PanSemStateFiniteExact 64 F), t.locals = s.locals → P s → P t) :
    Hoare P (.store dst src) (fun r t => r = none → P t) := by
  refine ⟨fun {F} s _ hs _ _ => ?_⟩
  exact hP s _ (evaluate_store_control_frame s dst src).2.1 hs

private theorem isValid_local_word_iff {F : Type} (s : PanSemStateFiniteExact 64 F)
    (name : MlS) (w : BitVec 64)
    (h : isValidValueHOLExact s.toExact .local name (.val (.word w)) = true) :
    ∃ w0 : BitVec 64, s.locals.lookup name = some (.val (.word w0)) := by
  unfold isValidValueHOLExact lookupKvarHOLExact at h
  dsimp only [PanSemStateFiniteExact.toExact] at h
  rcases hl : s.locals.lookup name with _ | existing
  · simp [hl] at h
  · rw [hl] at h
    rcases existing with wl | _ | _
    · cases wl with
      | word w0 => exact ⟨w0, rfl⟩
    · simp [shapeOfHOLExact, shapeEqHOL] at h
    · simp [shapeOfHOLExact, shapeEqHOL] at h

/-! ### 4. Memory & MPT-invariant framing lemmas -/

private theorem panByteAlignHOL_toNat {a : Nat} (ha : a < 2 ^ 64) :
    (panByteAlignHOL (BitVec.ofNat 64 a)).toNat = a / 8 * 8 := by
  have hal : 2 ^ ((64 : Nat) / 8).log2 = 8 := by decide
  change (BitVec.ofNat 64 ((BitVec.ofNat 64 a).toNat / 2 ^ ((64 : Nat) / 8).log2 *
    2 ^ ((64 : Nat) / 8).log2)).toNat = a / 8 * 8
  rw [hal, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_mul_le_self a 8) ha)]

private theorem wordsOK_transfer {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hgS : GuestInv s) (hgP : GuestInv post) {i : Ivl} (hw : WordsOK s i) :
    WordsOK post i := by
  refine ⟨hw.1, hw.2.1, fun k hk => ?_⟩
  obtain ⟨_, hdom, _⟩ := hw.2.2 k hk
  rcases hm : post.memory (BitVec.ofNat 64 (i.1 + 8 * k)) with ⟨w⟩
  refine ⟨w, ?_, hm⟩
  rw [hgP.memaddrs, ← hgS.memaddrs]
  exact hdom

private theorem allocated_heap_of_below_limit {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hA : ArenaOK s) {i : Ivl} (hal : Allocated s i) (hin : Inside i sourceBase heapLimit)
    (hpos : 0 < i.2) : Inside i sourceBase (globN s "heap_ptr") := by
  rcases hal with h | h
  · exact h
  · exfalso
    have hsep : heapLimit = scratchStart := rfl
    have := hA.2.2.1
    have := hA.2.2.2.1
    have := h.1
    have := hin.2
    omega

private theorem nodeSize_ge32_mod8 (k : Nat) : 32 ≤ nodeSize k ∧ nodeSize k % 8 = 0 := by
  unfold nodeSize
  split_ifs <;> omega

private theorem mptStack_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) (Nd : List Nat) :
    ∀ (fs : List Nat) (p : Nat),
      MptStack { s with locals := locals, clock := k } Nd p fs ↔ MptStack s Nd p fs
  | [], _ => Iff.rfl
  | _ :: qs, p => by
    simp only [MptStack]
    exact and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl
      (and_congr Iff.rfl (mptStack_with_locals s locals k Nd qs _))))

private def MptDeletePost (sp0 : Nat) : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun t => MptDeleteHead t ∧ (locN t "go" = 0 ∨ globN t "scratch_ptr" + 40 ≤ sp0)

private def headLocals : List String := ["top", "res", "go", "level", "klen", "node", "key"]

private theorem localsOnly_mptDeletePost (sp0 : Nat) :
    LocalsOnly headLocals (MptDeletePost sp0) := by
  intro F s locals k hl hP
  have htop := locN_congr s locals k "top" (hl "top" (by simp [headLocals]))
  have hres := locN_congr s locals k "res" (hl "res" (by simp [headLocals]))
  have hgo := locN_congr s locals k "go" (hl "go" (by simp [headLocals]))
  have hlev := locN_congr s locals k "level" (hl "level" (by simp [headLocals]))
  have hklen := locN_congr s locals k "klen" (hl "klen" (by simp [headLocals]))
  have hnode := locN_congr s locals k "node" (hl "node" (by simp [headLocals]))
  have hkey := locN_congr s locals k "key" (hl "key" (by simp [headLocals]))
  obtain ⟨⟨hA, Nd, fs, hNd, hSt, hRes, hAct⟩, hEff⟩ := hP
  refine ⟨⟨(arenaReady_with_locals s locals k).2 hA, Nd, fs, hNd, ?_, ?_, ?_⟩, ?_⟩
  · rw [htop, mptStack_with_locals]; exact hSt
  · rw [hres]; exact hRes
  · rw [hgo, hlev, hklen, hnode, hkey]; exact hAct
  · rw [hgo]; exact hEff

/-! #### 4a. `clearCache` (`node_invalidate`) framing -/

private theorem clearCache_memory_eq {F : Type} (s : PanSemStateFiniteExact 64 F)
    {node0 : Nat} (hhi : node0 + 24 < 2 ^ 64) {a : BitVec 64}
    (hne8 : a.toNat ≠ node0 + 8) (hne16 : a.toNat ≠ node0 + 16) (hne24 : a.toNat ≠ node0 + 24) :
    (clearCache s node0).memory a = s.memory a := by
  unfold clearCache
  dsimp only
  split
  · rename_i hhit
    exfalso
    rcases hhit with rfl | rfl | rfl
    · apply hne8; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    · apply hne16; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    · apply hne24; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  · rfl

private theorem clearCache_memW_eq {F : Type} (s : PanSemStateFiniteExact 64 F)
    {node0 x : Nat} (hhi : node0 + 24 < 2 ^ 64) (hx : x < 2 ^ 64)
    (hne8 : x ≠ node0 + 8) (hne16 : x ≠ node0 + 16) (hne24 : x ≠ node0 + 24) :
    memW (clearCache s node0) x = memW s x := by
  have hmem := clearCache_memory_eq s hhi (a := BitVec.ofNat 64 x)
    (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx]; exact hne8)
    (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx]; exact hne16)
    (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx]; exact hne24)
  unfold memW
  rw [hmem]

private theorem clearCache_node_head_eq {F : Type} {s : PanSemStateFiniteExact 64 F}
    {Nd : List Nat} (hNd : NodeHeap s Nd) {node0 n : Nat} (hn0 : node0 ∈ Nd) (hn : n ∈ Nd) :
    memW (clearCache s node0) n = memW s n ∧
      nodeIvl (clearCache s node0) n = nodeIvl s n := by
  have hlim : heapLimit < 2 ^ 64 := by decide
  have hin0 := (hNd.1 node0 hn0).2.2.1
  have hsz0 := nodeSize_ge32_mod8 (memW s node0)
  have hin_n := (hNd.1 n hn).2.2.1
  have hsz_n := nodeSize_ge32_mod8 (memW s n)
  dsimp only [Inside, nodeIvl] at hin0 hin_n
  have hhi0 : node0 + 24 < 2 ^ 64 := by omega
  have hxn : n < 2 ^ 64 := by omega
  have hne : n ≠ node0 + 8 ∧ n ≠ node0 + 16 ∧ n ≠ node0 + 24 := by
    by_cases heq : n = node0
    · subst heq; omega
    · rcases hNd.2 n hn node0 hn0 heq with hd | hd <;> (dsimp only [nodeIvl] at hd; omega)
  have hw := clearCache_memW_eq s hhi0 hxn hne.1 hne.2.1 hne.2.2
  exact ⟨hw, by simp [nodeIvl, hw]⟩

private theorem clearCache_keyIn {F : Type} {s : PanSemStateFiniteExact 64 F}
    {Nd : List Nat} (hNd : NodeHeap s Nd) {node0 : Nat} (hn0 : node0 ∈ Nd)
    {p len : Nat} (hk : KeyIn s Nd p len) :
    KeyIn (clearCache s node0) Nd p len := by
  rcases hk with rfl | ⟨hnib, hal, hin, hdisj⟩
  · exact Or.inl rfl
  · right
    have hlim : heapLimit < 2 ^ 64 := by decide
    have hin0 := (hNd.1 node0 hn0).2.2.1
    have hn0_8 : node0 % 8 = 0 := (hNd.1 node0 hn0).2.2.2.1.1
    have hsz0 := nodeSize_ge32_mod8 (memW s node0)
    dsimp only [Inside, nodeIvl] at hin0
    have hhi0 : node0 + 24 < 2 ^ 64 := by omega
    have hd0 := hdisj node0 hn0
    dsimp only [nodeIvl] at hd0
    refine ⟨fun k hklt => ?_, hal, hin, fun n hn => ?_⟩
    · have hpk : p + k < 2 ^ 64 := by have := hin.2; dsimp only at this; omega
      let c := panByteAlignHOL (BitVec.ofNat 64 (p + k))
      have hc : c.toNat = (p + k) / 8 * 8 := panByteAlignHOL_toNat hpk
      have hne : c.toNat ≠ node0 + 8 ∧ c.toNat ≠ node0 + 16 ∧ c.toNat ≠ node0 + 24 := by
        rw [hc]
        rcases hd0 with hd | hd <;> omega
      have hmem := clearCache_memory_eq s hhi0 hne.1 hne.2.1 hne.2.2
      unfold memB
      change (match (clearCache s node0).memory c with
        | .word v => (panGetByteHOL (BitVec.ofNat 64 (p + k)) v (clearCache s node0).be).toNat) < 16
      have hbe : (clearCache s node0).be = s.be := rfl
      rw [hmem, hbe]
      exact hnib k hklt
    · rw [(clearCache_node_head_eq hNd hn0 hn).2]
      exact hdisj n hn

private theorem clearCache_nodeHeap {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hg : GuestInv s) {Nd : List Nat} (hNd : NodeHeap s Nd) {node0 : Nat} (hn0 : node0 ∈ Nd) :
    NodeHeap (clearCache s node0) Nd := by
  have hlim : heapLimit < 2 ^ 64 := by decide
  have hin0 := (hNd.1 node0 hn0).2.2.1
  have hsz0 := nodeSize_ge32_mod8 (memW s node0)
  dsimp only [Inside, nodeIvl] at hin0
  have hhi0 : node0 + 24 < 2 ^ 64 := by omega
  have hgC : GuestInv (clearCache s node0) := guestInv_congr (s := s) rfl rfl rfl rfl hg
  refine ⟨fun n hn => ?_, fun n hn m hm hne => ?_⟩
  · obtain ⟨hk3, hal, hin, hw, hext, hbr, hpath, hcache, hleaf, hbranch⟩ := hNd.1 n hn
    obtain ⟨hw0, hivl⟩ := clearCache_node_head_eq hNd hn0 hn
    have hin_n := hin; dsimp only [Inside, nodeIvl] at hin_n
    have hoff_eq : ∀ off, 32 ≤ off → off + 8 ≤ nodeSize (memW s n) →
        memW (clearCache s node0) (n + off) = memW s (n + off) := by
      intro off h32 hoff_hi
      have hx : n + off < 2 ^ 64 := by omega
      have hne : n + off ≠ node0 + 8 ∧ n + off ≠ node0 + 16 ∧ n + off ≠ node0 + 24 := by
        by_cases heq : n = node0
        · subst heq; omega
        · rcases hNd.2 n hn node0 hn0 heq with hd | hd <;> (dsimp only [nodeIvl] at hd; omega)
      exact clearCache_memW_eq s hhi0 hx hne.1 hne.2.1 hne.2.2
    rw [hw0, hivl]
    refine ⟨hk3, hal, hin, wordsOK_transfer hg hgC hw, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro h2
      have hsz : nodeSize (memW s n) = 56 := by unfold nodeSize; simp [h2]
      rw [hoff_eq 48 (by omega) (by omega)]
      exact hext h2
    · intro h3 i hi
      have hsz : nodeSize (memW s n) = 176 := by unfold nodeSize; simp [h3]
      have heq_addr : n + 32 + 8 * i = n + (32 + 8 * i) := by omega
      rw [heq_addr, hoff_eq (32 + 8 * i) (by omega) (by omega), ← heq_addr]
      exact hbr h3 i hi
    · intro h12
      have hsz : 56 ≤ nodeSize (memW s n) := by
        unfold nodeSize
        rcases h12 with h1 | h2
        · simp [h1]
        · simp [h2]
      rw [hoff_eq 32 (by omega) (by omega), hoff_eq 40 (by omega) (by omega)]
      exact clearCache_keyIn hNd hn0 (hpath h12)
    · simp only [memW, clearCache]
      split
      · decide
      · exact hcache
    · intro h1
      have hsz : nodeSize (memW s n) = 64 := by simp [nodeSize, h1]
      rw [hoff_eq 56 (by omega) (by omega)]
      exact hleaf h1
    · intro h3
      have hsz : nodeSize (memW s n) = 176 := by simp [nodeSize, h3]
      rw [hoff_eq 168 (by omega) (by omega)]
      exact hbranch h3
  · rw [(clearCache_node_head_eq hNd hn0 hn).2, (clearCache_node_head_eq hNd hn0 hm).2]
    exact hNd.2 n hn m hm hne

private theorem clearCache_mptStack {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hA : ArenaReady s) {Nd : List Nat} (hNd : NodeHeap s Nd) {node0 : Nat} (hn0 : node0 ∈ Nd) :
    ∀ (fs : List Nat) (p : Nat),
      MptStack s Nd p fs → MptStack (clearCache s node0) Nd p fs
  | [], p, hp => hp
  | q :: qs, p, ⟨hpq, hne0, hfr, hord, htail⟩ => by
    subst hpq
    have hlim : heapLimit < 2 ^ 64 := by decide
    have hse : scratchEnd < 2 ^ 64 := by decide
    have hsep : heapLimit = scratchStart := rfl
    have hin0 := (hNd.1 node0 hn0).2.2.1
    have hsz0 := nodeSize_ge32_mod8 (memW s node0)
    dsimp only [Inside, nodeIvl] at hin0
    have hhi0 : node0 + 24 < 2 ^ 64 := by omega
    have hgC : GuestInv (clearCache s node0) := guestInv_congr (s := s) rfl rfl rfl rfl hA.1
    obtain ⟨hin_p, hw_p, hn_in, hkind_p⟩ := hfr
    have hp_lo : heapLimit ≤ p := by
      have := hA.2.2.2.1; have := hA.2.2.2.2.1; have := hin_p.1; dsimp only at this; omega
    have hp_eq : ∀ off, off ≤ 32 → memW (clearCache s node0) (p + off) = memW s (p + off) := by
      intro off hoff
      have hx : p + off < 2 ^ 64 := by have := hin_p.2; dsimp only at this; omega
      exact clearCache_memW_eq s hhi0 hx (by omega) (by omega) (by omega)
    have hp0 : memW (clearCache s node0) p = memW s p := by simpa using hp_eq 0 (by omega)
    have hp8 := hp_eq 8 (by omega)
    have hp16 := hp_eq 16 (by omega)
    have hp24 := hp_eq 24 (by omega)
    have hp32 := hp_eq 32 (by omega)
    have hfn : memW (clearCache s node0) (memW s (p + 8)) = memW s (memW s (p + 8)) :=
      (clearCache_node_head_eq hNd hn0 hn_in).1
    refine ⟨rfl, hne0, ⟨hin_p, wordsOK_transfer hA.1 hgC hw_p, ?_⟩, hord, ?_⟩
    · dsimp only
      rw [hp8]
      refine ⟨hn_in, ?_⟩
      rw [hp16, hp24, hp32, hfn]
      rcases hkind_p with ⟨h1, h2, hk⟩ | h3
      · exact Or.inl ⟨h1, h2, clearCache_keyIn hNd hn0 hk⟩
      · exact Or.inr h3
    · rw [hp0]
      exact clearCache_mptStack hA hNd hn0 qs (memW s p) htail

/-! #### 4b. `SameHeapAligned` / `SameAboveScratch` framing & `keyIn_suffix` -/

private def SameHeapAligned {F : Type} (s post : PanSemStateFiniteExact 64 F) : Prop :=
  ArenaReady s ∧ ArenaReady post ∧ post.be = s.be ∧
  globN post "heap_ptr" = globN s "heap_ptr" ∧
  globN post "scratch_ptr" ≤ globN s "scratch_ptr" ∧
  (∀ a : BitVec 64, a.toNat % 8 = 0 → a.toNat < globN s "heap_ptr" → post.memory a = s.memory a)

private def SameAboveScratch {F : Type} (s post : PanSemStateFiniteExact 64 F) : Prop :=
  ∀ a : BitVec 64, globN s "scratch_ptr" ≤ a.toNat → a.toNat < scratchEnd → post.memory a = s.memory a

private theorem sameHeapAligned_refl {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hA : ArenaReady s) : SameHeapAligned s s :=
  ⟨hA, hA, rfl, rfl, Nat.le_refl _, fun _ _ _ => rfl⟩

private theorem sameHeapAligned_trans {F : Type} {s m post : PanSemStateFiniteExact 64 F}
    (h1 : SameHeapAligned s m) (h2 : SameHeapAligned m post) : SameHeapAligned s post := by
  refine ⟨h1.1, h2.2.1, h2.2.2.1.trans h1.2.2.1, h2.2.2.2.1.trans h1.2.2.2.1,
    Nat.le_trans h2.2.2.2.2.1 h1.2.2.2.2.1, fun a ha8 hlt => ?_⟩
  rw [h2.2.2.2.2.2 a ha8 (by rw [h1.2.2.2.1]; exact hlt), h1.2.2.2.2.2 a ha8 hlt]

private theorem sameAboveScratch_trans {F : Type} {s m post : PanSemStateFiniteExact 64 F}
    (h1 : SameAboveScratch s m)
    (h2 : ∀ a : BitVec 64, globN s "scratch_ptr" ≤ a.toNat → a.toNat < scratchEnd →
      post.memory a = m.memory a) :
    SameAboveScratch s post :=
  fun a hlo hhi => (h2 a hlo hhi).trans (h1 a hlo hhi)

private theorem sameHeapAligned_memW {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (h : SameHeapAligned s post) {x : Nat} (hx8 : x % 8 = 0) (hx : x < globN s "heap_ptr") :
    memW post x = memW s x := by
  have hlim : heapLimit < 2 ^ 64 := by decide
  have hx264 : x < 2 ^ 64 := by have := h.1.2.2.1; omega
  have hmem := h.2.2.2.2.2 (BitVec.ofNat 64 x)
    (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx264]; exact hx8)
    (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx264]; exact hx)
  unfold memW
  rw [hmem]

private theorem sameHeapAligned_memB {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (h : SameHeapAligned s post) {x : Nat} (hx : x < globN s "heap_ptr") :
    memB post x = memB s x := by
  have hlim : heapLimit < 2 ^ 64 := by decide
  have hx264 : x < 2 ^ 64 := by have := h.1.2.2.1; omega
  have hhp8 : globN s "heap_ptr" % 8 = 0 := h.1.2.2.2.2.2.2.1
  let c := panByteAlignHOL (BitVec.ofNat 64 x)
  have hc : c.toNat = x / 8 * 8 := panByteAlignHOL_toNat hx264
  have hmem := h.2.2.2.2.2 c (by rw [hc]; omega) (by rw [hc]; omega)
  unfold memB
  change (match post.memory c with | .word v => (panGetByteHOL (BitVec.ofNat 64 x) v post.be).toNat) =
         (match s.memory c with | .word v => (panGetByteHOL (BitVec.ofNat 64 x) v s.be).toNat)
  rw [hmem, h.2.2.1]

private theorem sameHeapAligned_node_head {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (h : SameHeapAligned s post) {Nd : List Nat} (hNd : NodeHeap s Nd) {n : Nat} (hn : n ∈ Nd) :
    memW post n = memW s n ∧ nodeIvl post n = nodeIvl s n := by
  obtain ⟨_, hal, hin, hw, _⟩ := hNd.1 n hn
  have hsz := nodeSize_ge32_mod8 (memW s n)
  have hhp := allocated_heap_of_below_limit h.1.2 hal hin (by dsimp [nodeIvl]; omega)
  dsimp only [Inside, nodeIvl] at hhp
  have hn8 : n % 8 = 0 := hw.1
  have hw0 := sameHeapAligned_memW h hn8 (by omega)
  exact ⟨hw0, by simp [nodeIvl, hw0]⟩

private theorem sameHeapAligned_keyIn {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (h : SameHeapAligned s post) {Nd : List Nat} (hNd : NodeHeap s Nd)
    {p len : Nat} (hk : KeyIn s Nd p len) :
    KeyIn post Nd p len := by
  rcases hk with rfl | ⟨hnib, hal, hin, hdisj⟩
  · exact Or.inl rfl
  · by_cases hlen0 : len = 0
    · exact Or.inl hlen0
    · right
      have hhp := allocated_heap_of_below_limit h.1.2 hal hin (by omega)
      dsimp only [Inside] at hhp
      have hag : AllocatorGrows s post := ⟨by rw [h.2.2.2.1], h.2.2.2.2.1⟩
      refine ⟨fun k hklt => ?_, hag.allocated hal, hin, fun n hn => ?_⟩
      · rw [sameHeapAligned_memB h (by omega)]
        exact hnib k hklt
      · rw [(sameHeapAligned_node_head h hNd hn).2]
        exact hdisj n hn

private theorem sameHeapAligned_nodeHeap {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (h : SameHeapAligned s post) {Nd : List Nat} (hNd : NodeHeap s Nd) :
    NodeHeap post Nd := by
  have hag : AllocatorGrows s post := ⟨by rw [h.2.2.2.1], h.2.2.2.2.1⟩
  refine ⟨fun n hn => ?_, fun n hn m hm hne => ?_⟩
  · obtain ⟨hk3, hal, hin, hw, hext, hbr, hpath, hcache, hleaf, hbranch⟩ := hNd.1 n hn
    obtain ⟨hw0, hivl⟩ := sameHeapAligned_node_head h hNd hn
    have hsz0 := nodeSize_ge32_mod8 (memW s n)
    have hhp := allocated_heap_of_below_limit h.1.2 hal hin (by dsimp [nodeIvl]; omega)
    dsimp only [Inside, nodeIvl] at hhp
    have hn8 : n % 8 = 0 := hw.1
    rw [hw0, hivl]
    refine ⟨hk3, hag.allocated hal, hin, wordsOK_transfer h.1.1 h.2.1.1 hw, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro h2
      have hsz : nodeSize (memW s n) = 56 := by unfold nodeSize; simp [h2]
      rw [sameHeapAligned_memW h (by omega) (by omega)]
      exact hext h2
    · intro h3 i hi
      have hsz : nodeSize (memW s n) = 176 := by unfold nodeSize; simp [h3]
      rw [sameHeapAligned_memW h (by omega) (by omega)]
      exact hbr h3 i hi
    · intro h12
      have hsz : 56 ≤ nodeSize (memW s n) := by
        unfold nodeSize
        rcases h12 with h1 | h2
        · simp [h1]
        · simp [h2]
      rw [sameHeapAligned_memW h (by omega) (by omega), sameHeapAligned_memW h (by omega) (by omega)]
      exact sameHeapAligned_keyIn h hNd (hpath h12)
    · rw [sameHeapAligned_memW h (by omega) (by omega)]
      exact hcache
    · intro h1
      have hsz : nodeSize (memW s n) = 64 := by simp [nodeSize, h1]
      rw [sameHeapAligned_memW h (by omega) (by omega)]
      exact hleaf h1
    · intro h3
      have hsz : nodeSize (memW s n) = 176 := by simp [nodeSize, h3]
      rw [sameHeapAligned_memW h (by omega) (by omega)]
      exact hbranch h3
  · rw [(sameHeapAligned_node_head h hNd hn).2, (sameHeapAligned_node_head h hNd hm).2]
    exact hNd.2 n hn m hm hne

private theorem sameAboveScratch_mptStack {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (h : SameHeapAligned s post) (hscr : SameAboveScratch s post)
    {Nd : List Nat} (hNd : NodeHeap s Nd) :
    ∀ (fs : List Nat) (p : Nat),
      MptStack s Nd p fs →
        MptStack post Nd p fs ∧ (∀ r ∈ fs, globN s "scratch_ptr" ≤ r)
  | [], p, hp => ⟨hp, fun _ hr => by simp at hr⟩
  | q :: qs, p, ⟨hpq, hne0, hfr, hord, htail⟩ => by
    subst hpq
    have hse : scratchEnd < 2 ^ 64 := by decide
    obtain ⟨hin_p, hw_p, hn_in, hkind_p⟩ := hfr
    have hin_p' := hin_p; dsimp only [Inside] at hin_p'
    have hp_eq : ∀ off, off ≤ 32 → memW post (p + off) = memW s (p + off) := by
      intro off hoff
      have hx264 : p + off < 2 ^ 64 := by omega
      have hmem := hscr (BitVec.ofNat 64 (p + off))
        (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx264]; omega)
        (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx264]; omega)
      unfold memW; rw [hmem]
    have hp0 : memW post p = memW s p := by simpa using hp_eq 0 (by omega)
    have hp8 := hp_eq 8 (by omega)
    have hp16 := hp_eq 16 (by omega)
    have hp24 := hp_eq 24 (by omega)
    have hp32 := hp_eq 32 (by omega)
    have hfn : memW post (memW s (p + 8)) = memW s (memW s (p + 8)) :=
      (sameHeapAligned_node_head h hNd hn_in).1
    obtain ⟨htail_post, _⟩ := sameAboveScratch_mptStack h hscr hNd qs (memW s p) htail
    refine ⟨⟨rfl, hne0, ⟨⟨Nat.le_trans h.2.2.2.2.1 hin_p.1, hin_p.2⟩,
      wordsOK_transfer h.1.1 h.2.1.1 hw_p, ?_⟩, hord, ?_⟩, ?_⟩
    · dsimp only
      rw [hp8]
      refine ⟨hn_in, ?_⟩
      rw [hp16, hp24, hp32, hfn]
      rcases hkind_p with ⟨h1, h2, hk⟩ | h3
      · exact Or.inl ⟨h1, h2, sameHeapAligned_keyIn h hNd hk⟩
      · exact Or.inr h3
    · rw [hp0]; exact htail_post
    · intro r hr
      simp only [List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact hin_p'.1
      · have := hord r hr; omega

private theorem keyIn_suffix {F : Type} {s : PanSemStateFiniteExact 64 F}
    {Nd : List Nat} {p len d : Nat} (hd : d ≤ len) (hk : KeyIn s Nd p len) :
    KeyIn s Nd (p + d) (len - d) := by
  by_cases hrem : len - d = 0
  · exact Or.inl hrem
  · rcases hk with rfl | ⟨hnib, hal, hin, hdisj⟩
    · omega
    · right
      refine ⟨fun k hklt => ?_, ?_, ⟨by have := hin.1; omega, by have := hin.2; omega⟩,
        fun n hn => ?_⟩
      · have hadd : p + d + k = p + (d + k) := by omega
        rw [hadd]
        exact hnib (d + k) (by omega)
      · rcases hal with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨by omega, by omega⟩
        · exact Or.inr ⟨by omega, by omega⟩
      · rcases hdisj n hn with h1 | h2
        · exact Or.inl (by dsimp at h1 ⊢; omega)
        · exact Or.inr (by dsimp at h2 ⊢; omega)

/-! #### 4c. Bundled heap/stack invariants & step helpers -/

private def HeapInv (Nd : List Nat) (node0 key0 klen0 level0 seg0 sl0 child0 : Nat)
    {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  ArenaReady s ∧ NodeHeap s Nd ∧ node0 ∈ Nd ∧
  memW s node0 = 2 ∧ memW s (node0 + 32) = seg0 ∧ memW s (node0 + 40) = sl0 ∧
  memW s (node0 + 48) = child0 ∧ RootIn Nd child0 ∧
  KeyIn s Nd (key0 + level0) (klen0 - level0) ∧ KeyIn s Nd seg0 sl0

private theorem heapInv_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat)
    (Nd : List Nat) (node0 key0 klen0 level0 seg0 sl0 child0 : Nat) :
    HeapInv Nd node0 key0 klen0 level0 seg0 sl0 child0 { s with locals := locals, clock := k } ↔
      HeapInv Nd node0 key0 klen0 level0 seg0 sl0 child0 s := by
  simp only [HeapInv, arenaReady_with_locals]
  exact Iff.rfl

private theorem clearCache_heapInv {F : Type} {s : PanSemStateFiniteExact 64 F}
    {Nd : List Nat} {node0 key0 klen0 level0 seg0 sl0 child0 : Nat}
    (hH : HeapInv Nd node0 key0 klen0 level0 seg0 sl0 child0 s) :
    HeapInv Nd node0 key0 klen0 level0 seg0 sl0 child0 (clearCache s node0) := by
  obtain ⟨hA, hNd, hn0, hk2, h32, h40, h48, hch, hKey, hSeg⟩ := hH
  have hlim : heapLimit < 2 ^ 64 := by decide
  have hin0 := (hNd.1 node0 hn0).2.2.1
  have hsz : nodeSize (memW s node0) = 56 := by unfold nodeSize; simp [hk2]
  dsimp only [Inside, nodeIvl] at hin0
  have hhi0 : node0 + 24 < 2 ^ 64 := by omega
  refine ⟨⟨guestInv_congr (s := s) rfl rfl rfl rfl hA.1, hA.2⟩,
    clearCache_nodeHeap hA.1 hNd hn0, hn0,
    (clearCache_node_head_eq hNd hn0 hn0).1.trans hk2,
    (clearCache_memW_eq s hhi0 (by omega) (by omega) (by omega) (by omega)).trans h32,
    (clearCache_memW_eq s hhi0 (by omega) (by omega) (by omega) (by omega)).trans h40,
    (clearCache_memW_eq s hhi0 (by omega) (by omega) (by omega) (by omega)).trans h48,
    hch,
    clearCache_keyIn hNd hn0 hKey,
    clearCache_keyIn hNd hn0 hSeg⟩

private theorem sameHeapAligned_heapInv {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (h : SameHeapAligned s post)
    {Nd : List Nat} {node0 key0 klen0 level0 seg0 sl0 child0 : Nat}
    (hH : HeapInv Nd node0 key0 klen0 level0 seg0 sl0 child0 s) :
    HeapInv Nd node0 key0 klen0 level0 seg0 sl0 child0 post := by
  obtain ⟨_, hNd, hn0, hk2, h32, h40, h48, hch, hKey, hSeg⟩ := hH
  obtain ⟨_, hal0, hin0, hw0, _⟩ := hNd.1 node0 hn0
  have hsz : nodeSize (memW s node0) = 56 := by unfold nodeSize; simp [hk2]
  have hhp := allocated_heap_of_below_limit h.1.2 hal0 hin0 (by dsimp [nodeIvl]; omega)
  dsimp only [Inside, nodeIvl] at hhp
  have hn8 : node0 % 8 = 0 := hw0.1
  refine ⟨h.2.1, sameHeapAligned_nodeHeap h hNd, hn0,
    (sameHeapAligned_memW h hn8 (by omega)).trans hk2,
    (sameHeapAligned_memW h (by omega) (by omega)).trans h32,
    (sameHeapAligned_memW h (by omega) (by omega)).trans h40,
    (sameHeapAligned_memW h (by omega) (by omega)).trans h48,
    hch,
    sameHeapAligned_keyIn h hNd hKey,
    sameHeapAligned_keyIn h hNd hSeg⟩

private theorem mptStack_congr_above {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (h : SameHeapAligned s post) {Nd : List Nat} (hNd : NodeHeap s Nd) {sp0 : Nat}
    (hmem : ∀ a : BitVec 64, sp0 ≤ a.toNat → a.toNat < scratchEnd → post.memory a = s.memory a) :
    ∀ (fs : List Nat) (p : Nat),
      MptStack s Nd p fs → (∀ r ∈ fs, sp0 ≤ r) → MptStack post Nd p fs
  | [], p, hp, _ => hp
  | q :: qs, p, ⟨hpq, hne0, hfr, hord, htail⟩, hge => by
    subst hpq
    have hse : scratchEnd < 2 ^ 64 := by decide
    have hsp_p : sp0 ≤ p := hge p (by simp)
    obtain ⟨hin_p, hw_p, hn_in, hkind_p⟩ := hfr
    have hin_p' := hin_p; dsimp only [Inside] at hin_p'
    have hp_eq : ∀ off, off ≤ 32 → memW post (p + off) = memW s (p + off) := by
      intro off hoff
      have hx264 : p + off < 2 ^ 64 := by omega
      have hm := hmem (BitVec.ofNat 64 (p + off))
        (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx264]; omega)
        (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx264]; omega)
      unfold memW; rw [hm]
    have hp0 : memW post p = memW s p := by simpa using hp_eq 0 (by omega)
    have hp8 := hp_eq 8 (by omega)
    have hp16 := hp_eq 16 (by omega)
    have hp24 := hp_eq 24 (by omega)
    have hp32 := hp_eq 32 (by omega)
    have hfn : memW post (memW s (p + 8)) = memW s (memW s (p + 8)) :=
      (sameHeapAligned_node_head h hNd hn_in).1
    refine ⟨rfl, hne0, ⟨⟨Nat.le_trans h.2.2.2.2.1 hin_p.1, hin_p.2⟩,
      wordsOK_transfer h.1.1 h.2.1.1 hw_p, ?_⟩, hord, ?_⟩
    · dsimp only
      rw [hp8]
      refine ⟨hn_in, ?_⟩
      rw [hp16, hp24, hp32, hfn]
      rcases hkind_p with ⟨h1, h2, hk⟩ | h3
      · exact Or.inl ⟨h1, h2, sameHeapAligned_keyIn h hNd hk⟩
      · exact Or.inr h3
    · rw [hp0]
      exact mptStack_congr_above h hNd hmem qs (memW s p) htail (fun r hr => hge r (by simp [hr]))

private theorem store_frame_memW_same {F : Type} (s : PanSemStateFiniteExact 64 F)
    (wb wv off : BitVec 64) (offN : Nat) (hoff : off.toNat = offN)
    (_hhi : wb.toNat + offN < 2 ^ 64) :
    memW { s with memory := fun a => if a = wb + off then .word wv else s.memory a }
      (wb.toNat + offN) = wv.toNat := by
  have heq : BitVec.ofNat 64 (wb.toNat + offN) = wb + off := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, BitVec.toNat_add, hoff]
  unfold memW
  simp [heq]

private theorem store_frame_memW_ne {F : Type} (s : PanSemStateFiniteExact 64 F)
    (wb wv off : BitVec 64) (offN x : Nat) (hoff : off.toNat = offN)
    (hhi : wb.toNat + offN < 2 ^ 64) (hx : x < 2 ^ 64)
    (hne : x ≠ wb.toNat + offN) :
    memW { s with memory := fun a => if a = wb + off then .word wv else s.memory a }
      x = memW s x := by
  have hneq : BitVec.ofNat 64 x ≠ wb + off := by
    intro hc
    have ht := congrArg BitVec.toNat hc
    simp only [BitVec.toNat_ofNat, BitVec.toNat_add, hoff] at ht
    omega
  unfold memW
  simp [hneq]

private theorem store_scratch_preserves {F : Type} {s : PanSemStateFiniteExact 64 F}
    {Nd fs : List Nat} {sp0 node0 top0 key0 klen0 level0 seg0 sl0 child0 : Nat}
    {wb wv off : BitVec 64} {offN : Nat} (hoff : off.toNat = offN)
    (hH : HeapInv Nd node0 key0 klen0 level0 seg0 sl0 child0 s)
    (hSt : MptStack s Nd top0 fs) (hge : ∀ r ∈ fs, sp0 ≤ r)
    (hfr_lo : scratchStart ≤ wb.toNat) (hoff_lt : offN < 40) (hfr_sp : wb.toNat + 40 ≤ sp0)
    (hsp_end : sp0 ≤ scratchEnd) :
    let s' := { s with memory := fun a => if a = wb + off then .word wv else s.memory a }
    HeapInv Nd node0 key0 klen0 level0 seg0 sl0 child0 s' ∧ MptStack s' Nd top0 fs := by
  intro s'
  have hse : scratchEnd < 2 ^ 64 := by decide
  have hsep : heapLimit = scratchStart := rfl
  have hhi : wb.toNat + offN < 2 ^ 64 := by omega
  have htoNat : (wb + off).toNat = wb.toNat + offN := by
    simp only [BitVec.toNat_add, hoff]; omega
  have hAs : ArenaReady s := hH.1
  have hAs' : ArenaReady s' := ⟨guestInv_congr (s := s) rfl rfl rfl rfl hAs.1, hAs.2⟩
  have hsame : SameHeapAligned s s' := by
    refine ⟨hAs, hAs', rfl, rfl, Nat.le_refl _, fun a _ hlt => ?_⟩
    have hhp := hAs.2.2.1
    have hne : a ≠ wb + off := by
      intro hc; rw [hc, htoNat] at hlt; omega
    exact if_neg hne
  have habove : ∀ a : BitVec 64, sp0 ≤ a.toNat → a.toNat < scratchEnd → s'.memory a = s.memory a := by
    intro a hlo _
    have hne : a ≠ wb + off := by
      intro hc; rw [hc, htoNat] at hlo; omega
    exact if_neg hne
  exact ⟨sameHeapAligned_heapInv hsame hH, mptStack_congr_above hsame hH.2.1 habove fs top0 hSt hge⟩

/-! #### 4d. State predicates along the `kind = 2` execution path -/

private def PreBody (Nd fs : List Nat)
    (sp0 node0 top0 res0 key0 klen0 level0 seg0 sl0 child0 : Nat) :
    ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s =>
    HeapInv Nd node0 key0 klen0 level0 seg0 sl0 child0 s ∧
    MptStack s Nd top0 fs ∧ RootIn Nd res0 ∧ level0 ≤ klen0 ∧ node0 ≠ 0 ∧
    globN s "scratch_ptr" = sp0 ∧
    locN s "node" = node0 ∧ locN s "top" = top0 ∧ locN s "res" = res0 ∧
    locN s "key" = key0 ∧ locN s "klen" = klen0 ∧ locN s "level" = level0 ∧
    ∃ wn : BitVec 64, s.locals.lookup (ofString "node") = some (.val (.word wn)) ∧ wn.toNat = node0

private def AfterInvalidate (Nd fs : List Nat)
    (sp0 node0 top0 res0 key0 klen0 level0 seg0 sl0 child0 : Nat) :
    ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s =>
    HeapInv Nd node0 key0 klen0 level0 seg0 sl0 child0 s ∧
    MptStack s Nd top0 fs ∧ RootIn Nd res0 ∧ level0 ≤ klen0 ∧
    globN s "scratch_ptr" = sp0 ∧
    locN s "go" = 0 ∧ locN s "k" = 2 ∧ locN s "node" = node0 ∧
    locN s "top" = top0 ∧ locN s "res" = res0 ∧
    locN s "key" = key0 ∧ locN s "klen" = klen0 ∧ locN s "level" = level0 ∧
    ∃ wn : BitVec 64, s.locals.lookup (ofString "node") = some (.val (.word wn)) ∧ wn.toNat = node0

private def BeforePrefix (Nd fs : List Nat)
    (sp0 node0 top0 res0 key0 klen0 level0 seg0 sl0 child0 : Nat) :
    ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s =>
    AfterInvalidate Nd fs sp0 node0 top0 res0 key0 klen0 level0 seg0 sl0 child0 s ∧
    locN s "seg" = seg0 ∧ locN s "sl" = sl0 ∧
    (∃ wseg : BitVec 64, s.locals.lookup (ofString "seg") = some (.val (.word wseg)) ∧ wseg.toNat = seg0) ∧
    (∃ wsl : BitVec 64, s.locals.lookup (ofString "sl") = some (.val (.word wsl)) ∧ wsl.toNat = sl0)

private def AfterPrefix (Nd fs : List Nat)
    (sp0 node0 top0 res0 key0 klen0 level0 seg0 sl0 child0 : Nat) :
    ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s =>
    BeforePrefix Nd fs sp0 node0 top0 res0 key0 klen0 level0 seg0 sl0 child0 s ∧
    locN s "pl" ≤ sl0 ∧ locN s "pl" ≤ klen0 - level0 ∧
    (∃ wlvl : BitVec 64, s.locals.lookup (ofString "level") = some (.val (.word wlvl)) ∧ wlvl.toNat = level0)

private def AfterAlloc (Nd fs : List Nat)
    (sp0 node0 top0 res0 key0 klen0 level0 seg0 sl0 child0 : Nat) :
    ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s =>
    HeapInv Nd node0 key0 klen0 level0 seg0 sl0 child0 s ∧
    MptStack s Nd top0 fs ∧ (∀ r ∈ fs, sp0 ≤ r) ∧ sp0 ≤ scratchEnd ∧
    RootIn Nd res0 ∧ level0 + sl0 ≤ klen0 ∧
    locN s "node" = node0 ∧ locN s "top" = top0 ∧ locN s "res" = res0 ∧
    locN s "key" = key0 ∧ locN s "klen" = klen0 ∧ locN s "level" = level0 ∧
    locN s "seg" = seg0 ∧ locN s "sl" = sl0 ∧
    (∃ wn : BitVec 64, s.locals.lookup (ofString "node") = some (.val (.word wn)) ∧ wn.toNat = node0) ∧
    (∃ wseg : BitVec 64, s.locals.lookup (ofString "seg") = some (.val (.word wseg)) ∧ wseg.toNat = seg0) ∧
    (∃ wsl : BitVec 64, s.locals.lookup (ofString "sl") = some (.val (.word wsl)) ∧ wsl.toNat = sl0) ∧
    (∃ wlvl : BitVec 64, s.locals.lookup (ofString "level") = some (.val (.word wlvl)) ∧ wlvl.toNat = level0) ∧
    (∃ wfr : BitVec 64,
      s.locals.lookup (ofString "fr") = some (.val (.word wfr)) ∧
      locN s "fr" = wfr.toNat ∧
      wfr.toNat % 8 = 0 ∧ scratchStart ≤ wfr.toNat ∧
      wfr.toNat + 40 ≤ sp0 ∧ globN s "scratch_ptr" = wfr.toNat ∧
      WordsOK s (wfr.toNat, 40))

private theorem resume_common_prefix_length (h : MptDeleteCallees)
    (Nd fs : List Nat) (sp0 node0 top0 res0 key0 klen0 level0 seg0 sl0 child0 : Nat) :
    DecCallResumeOn
      (BeforePrefix Nd fs sp0 node0 top0 res0 key0 klen0 level0 seg0 sl0 child0)
      (AfterPrefix Nd fs sp0 node0 top0 res0 key0 klen0 level0 seg0 sl0 child0)
      (ofString "pl") (ofString "common_prefix_length")
      [.var .local (ofString "seg"), .var .local (ofString "sl"),
       .op .add [.var .local (ofString "key"), .var .local (ofString "level")],
       .op .sub [.var .local (ofString "klen"), .var .local (ofString "level")]] := by
  intro F state values body callee ret value post hcode hP hargs hl hrun
  obtain ⟨hAI, hlSeg, hlSl, hWseg, hWsl⟩ := hP
  obtain ⟨hH, hSt, hRes, hLev, hSp, hgo, hk2, hlN, hlT, hlR, hlK, hlKl, hlLv, wn, hwn, hwnt⟩ := hAI
  obtain ⟨wseg, hwseg, hwsegt⟩ := hWseg
  obtain ⟨wsl, hwsl, hwslt⟩ := hWsl
  have hlk : state.code.lookup (ofString "common_prefix_length") =
      some ([(ofString "a", .one), (ofString "al", .one),
             (ofString "b", .one), (ofString "bl", .one)],
            (sourceFunctionEntry Guest.Software.guestFn_common_prefix_length).2.2.1, .one) := by
    rw [hcode, lookup_common_prefix_length]; rfl
  obtain ⟨v1, v2, v3, v4, _, hv2, _, hv4, hc_al, hc_bl⟩ :=
    callee_param_four_exp state _ _ _ _ _ _ _ _ _ _ _ hlk _ _ _ _ values body callee ret hargs hl
  have hv2_eq : v2 = .val (.word wsl) := by
    simp [evalAt, evalHOLExact, hwsl] at hv2; exact hv2.symm
  subst hv2_eq
  obtain ⟨wklen, wlvl, _, hwlvl, hwklen_t, hwlvl_t, rfl⟩ := evalAt_sub_locals state "klen" "level" v4 hv4
  rw [hlKl] at hwklen_t
  rw [hlLv] at hwlvl_t
  have hsub_t : (wklen - wlvl).toNat = klen0 - level0 := by
    have hle_bv : wlvl ≤ wklen := BitVec.le_def.mpr (by omega)
    rw [BitVec.toNat_sub_of_le hle_bv, hwklen_t, hwlvl_t]
  have hGin : GuestInv (callEntryStateHOLFinite state callee) :=
    guestInv_callEntry state callee hH.1.1
  have hro0 := FunSpec.at_lookup h.ro_common_prefix_length state hcode values body callee ret hl
    hGin (by rw [hrun]; simp)
  rw [hrun] at hro0
  have hro := hro0 (Or.inl ⟨value, rfl⟩)
  have hrv0 := FunSpec.at_lookup h.rv_common_prefix_length state hcode values body callee ret hl
    hGin (by rw [hrun]; simp)
  rw [hrun] at hrv0
  obtain ⟨wpl, rfl, hwpl_le⟩ := hrv0 value rfl
  have hal_eq : locN (callEntryStateHOLFinite state callee) "al" = sl0 := by
    simp [locN, callEntryStateHOLFinite, hc_al, hwslt]
  have hbl_eq : locN (callEntryStateHOLFinite state callee) "bl" = klen0 - level0 := by
    simp [locN, callEntryStateHOLFinite, hc_bl, hsub_t]
  dsimp only at hwpl_le
  rw [hal_eq, hbl_eq] at hwpl_le
  have hrest : ({ post with locals := state.locals } : PanSemStateFiniteExact 64 F) =
      { state with locals := state.locals, clock := post.clock } := by
    dsimp only at hro
    rw [hro]; rfl
  rw [hrest]
  refine ⟨⟨⟨(heapInv_with_locals state _ post.clock _ _ _ _ _ _ _ _).2 hH,
    (mptStack_with_locals state _ post.clock Nd fs top0).2 hSt,
    hRes, hLev, hSp,
    (locN_setVar_ne _ "go" (ofString "pl") _ (by decide)).trans hgo,
    (locN_setVar_ne _ "k" (ofString "pl") _ (by decide)).trans hk2,
    (locN_setVar_ne _ "node" (ofString "pl") _ (by decide)).trans hlN,
    (locN_setVar_ne _ "top" (ofString "pl") _ (by decide)).trans hlT,
    (locN_setVar_ne _ "res" (ofString "pl") _ (by decide)).trans hlR,
    (locN_setVar_ne _ "key" (ofString "pl") _ (by decide)).trans hlK,
    (locN_setVar_ne _ "klen" (ofString "pl") _ (by decide)).trans hlKl,
    (locN_setVar_ne _ "level" (ofString "pl") _ (by decide)).trans hlLv,
    wn, by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      (show ofString "pl" ≠ ofString "node" by decide), hwn], hwnt⟩,
    (locN_setVar_ne _ "seg" (ofString "pl") _ (by decide)).trans hlSeg,
    (locN_setVar_ne _ "sl" (ofString "pl") _ (by decide)).trans hlSl,
    ⟨wseg, by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      (show ofString "pl" ≠ ofString "seg" by decide), hwseg], hwsegt⟩,
    ⟨wsl, by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      (show ofString "pl" ≠ ofString "sl" by decide), hwsl], hwslt⟩⟩,
    ?_, ?_,
    ⟨wlvl, by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      (show ofString "pl" ≠ ofString "level" by decide), hwlvl], hwlvl_t⟩⟩
  · rw [locN_setVar_same]; omega
  · rw [locN_setVar_same]; omega

private theorem resume_scratch_alloc (h : MptDeleteCallees)
    (Nd fs : List Nat) (sp0 node0 top0 res0 key0 klen0 level0 seg0 sl0 child0 : Nat) :
    DecCallResumeOn
      (fun s => AfterPrefix Nd fs sp0 node0 top0 res0 key0 klen0 level0 seg0 sl0 child0 s ∧
        CondFalse (.cmp .lower (.var .local (ofString "pl")) (.var .local (ofString "sl"))) s)
      (AfterAlloc Nd fs sp0 node0 top0 res0 key0 klen0 level0 seg0 sl0 child0)
      (ofString "fr") (ofString "scratch_alloc")
      [.const 40] := by
  intro F state values body callee ret value post hcode ⟨hAP, hcf⟩ hargs hl hrun
  obtain ⟨⟨hAI, hlSeg, hlSl, ⟨wseg, hwseg, hwsegt⟩, ⟨wsl, hwsl, hwslt⟩⟩,
    hpl_sl, hpl_rem, ⟨wlvl, hwlvl, hwlvl_t⟩⟩ := hAP
  obtain ⟨hH, hSt, hRes, hLev, hSp, _, _, hlN, hlT, hlR, hlK, hlKl, hlLv, wn, hwn, hwnt⟩ := hAI
  have hsl_le_pl := condFalse_local_lower_local hcf
  rw [hlSl] at hsl_le_pl
  have hlev_add : level0 + sl0 ≤ klen0 := by omega
  have hlk : state.code.lookup (ofString "scratch_alloc") =
      some ([(ofString "n", .one)],
            (sourceFunctionEntry Guest.Software.guestFn_scratch_alloc).2.2.1, .one) := by
    rw [hcode, lookup_scratch_alloc]; rfl
  obtain ⟨v1, hv1, hc_n⟩ := callee_param_one_exp state _ _ _ _ _ hlk _ values body callee ret hargs hl
  cases evalAt_const state 40 v1 hv1
  have hn_eq : locN (callEntryStateHOLFinite state callee) "n" = 40 := by
    simp [locN, callEntryStateHOLFinite, hc_n]
  have hAin : ArenaReady (callEntryStateHOLFinite state callee) :=
    localsFree_arenaReady state callee (state.clock - 1) hH.1
  have hmeta_be : post.be = state.be := by
    have hm := (evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state callee) body).2.2.1
    rw [hrun] at hm; exact hm
  have hww0 := FunSpec.at_lookup h.ww_scratch_alloc state hcode values body callee ret hl
    hAin (by rw [hrun]; simp)
  rw [hrun] at hww0
  obtain ⟨hApost, _, hsp_le, hframe, hgkeep⟩ := hww0 (Or.inl ⟨value, rfl⟩)
  have hrt0 := FunSpec.at_lookup h.rt_scratch_alloc state hcode values body callee ret hl
    hAin (by rw [hrun]; simp)
  rw [hrun] at hrt0
  obtain ⟨wfr, rfl, _, _, ⟨hfr8, hfr_fmp, hfr_in, hfr_words⟩, hsp_post⟩ := hrt0 value rfl
  rw [hn_eq] at hfr_in hfr_words
  have hrnd40 : (40 + 7) / 8 * 8 = 40 := by decide
  rw [hrnd40] at hfr_in hfr_words
  have hhp_eq : globN post "heap_ptr" = globN state "heap_ptr" := by
    have hk := hgkeep (ofString "heap_ptr") (by decide)
    unfold globN; rw [← hk]; rfl
  have hsame : SameHeapAligned state post := by
    refine ⟨hH.1, hApost, hmeta_be, hhp_eq, hsp_le, fun a ha8 hlt => ?_⟩
    have hsep : heapLimit = scratchStart := rfl
    have hhp8 : globN state "heap_ptr" % 8 = 0 := hH.1.2.2.2.2.2.2.1
    have hhp_lim := hH.1.2.2.1
    have hfmp_lo := hH.1.2.2.2.1
    have hfmp_sp := hH.1.2.2.2.2.1
    apply hframe a
    · intro i hi hhit
      simp only [List.nil_append, List.mem_singleton] at hi
      subst hi
      unfold CellHits at hhit
      dsimp [callEntryStateHOLFinite, globN] at hhit
      change globN state "frame_mem_ptr" < a.toNat + 8 ∧
        a.toNat < globN state "frame_mem_ptr" + (globN state "scratch_ptr" - globN state "frame_mem_ptr") at hhit
      omega
    · intro hhit
      unfold CellHits at hhit
      change globN state "heap_ptr" < a.toNat + 8 ∧ _ at hhit
      omega
  have habove : SameAboveScratch state post := by
    intro a hlo hhi
    have hsep : heapLimit = scratchStart := rfl
    have hhp_lim := hH.1.2.2.1
    have hfmp_lo := hH.1.2.2.2.1
    have hfmp_sp := hH.1.2.2.2.2.1
    apply hframe a
    · intro i hi hhit
      simp only [List.nil_append, List.mem_singleton] at hi
      subst hi
      unfold CellHits at hhit
      change globN state "frame_mem_ptr" < a.toNat + 8 ∧
        a.toNat < globN state "frame_mem_ptr" + (globN state "scratch_ptr" - globN state "frame_mem_ptr") at hhit
      omega
    · intro hhit
      unfold CellHits at hhit
      change _ ∧ a.toNat < globN state "heap_ptr" + (heapLimit - globN state "heap_ptr") at hhit
      omega
  have hH_post := sameHeapAligned_heapInv hsame hH
  obtain ⟨hSt_post, hge_fs⟩ := sameAboveScratch_mptStack hsame habove hH.2.1 fs top0 hSt
  rw [hSp] at hge_fs
  have hsp0_end : sp0 ≤ scratchEnd := by rw [← hSp]; exact hH.1.2.2.2.2.2.1
  have hfr_lo : scratchStart ≤ wfr.toNat := Nat.le_trans hH.1.2.2.2.1 hfr_fmp
  have hfr_sp0 : wfr.toNat + 40 ≤ sp0 := by
    have := hfr_in.2; dsimp [callEntryStateHOLFinite] at this
    change wfr.toNat + 40 ≤ globN state "scratch_ptr" at this
    rwa [hSp] at this
  set u := setVarHOLFinite (ofString "fr") (.val (.word wfr)) { post with locals := state.locals }
  have hu_eq : u = { post with locals := state.locals.update (ofString "fr", .val (.word wfr)) } := rfl
  refine ⟨(heapInv_with_locals post _ post.clock _ _ _ _ _ _ _ _).2 hH_post,
    (mptStack_with_locals post _ post.clock Nd fs top0).2 hSt_post,
    hge_fs, hsp0_end, hRes, hlev_add,
    (locN_setVar_ne _ "node" (ofString "fr") _ (by decide)).trans hlN,
    (locN_setVar_ne _ "top" (ofString "fr") _ (by decide)).trans hlT,
    (locN_setVar_ne _ "res" (ofString "fr") _ (by decide)).trans hlR,
    (locN_setVar_ne _ "key" (ofString "fr") _ (by decide)).trans hlK,
    (locN_setVar_ne _ "klen" (ofString "fr") _ (by decide)).trans hlKl,
    (locN_setVar_ne _ "level" (ofString "fr") _ (by decide)).trans hlLv,
    (locN_setVar_ne _ "seg" (ofString "fr") _ (by decide)).trans hlSeg,
    (locN_setVar_ne _ "sl" (ofString "fr") _ (by decide)).trans hlSl,
    ⟨wn, by simp [hu_eq, HolFiniteMapExact.update, FUPDATE,
      (show ofString "fr" ≠ ofString "node" by decide), hwn], hwnt⟩,
    ⟨wseg, by simp [hu_eq, HolFiniteMapExact.update, FUPDATE,
      (show ofString "fr" ≠ ofString "seg" by decide), hwseg], hwsegt⟩,
    ⟨wsl, by simp [hu_eq, HolFiniteMapExact.update, FUPDATE,
      (show ofString "fr" ≠ ofString "sl" by decide), hwsl], hwslt⟩,
    ⟨wlvl, by simp [hu_eq, HolFiniteMapExact.update, FUPDATE,
      (show ofString "fr" ≠ ofString "level" by decide), hwlvl], hwlvl_t⟩,
    ⟨wfr, by simp [hu_eq, HolFiniteMapExact.update, FUPDATE],
      locN_setVar_same _ "fr" wfr, hfr8, hfr_lo, hfr_sp0, hsp_post, hfr_words⟩⟩

private def framePushProg : ProgHOL 64 :=
  .seq (.store (.op .add [.var .local (ofString "fr"), .const 0]) (.var .local (ofString "top")))
    (.seq (.store (.op .add [.var .local (ofString "fr"), .const 8]) (.var .local (ofString "node")))
      (.seq (.store (.op .add [.var .local (ofString "fr"), .const 16]) (.const 2))
        (.seq (.store (.op .add [.var .local (ofString "fr"), .const 24]) (.var .local (ofString "seg")))
          (.seq (.store (.op .add [.var .local (ofString "fr"), .const 32]) (.var .local (ofString "sl")))
            (.seq (.assign .local (ofString "top") (.var .local (ofString "fr")))
              (.seq (.assign .local (ofString "node") (.load .one (.op .add [.var .local (ofString "node"), .const 48])))
                (.seq (.assign .local (ofString "level") (.op .add [.var .local (ofString "level"), .var .local (ofString "sl")]))
                  (.assign .local (ofString "go") (.const 1)))))))))

private def StoredAt (Nd fs : List Nat)
    (sp0 node0 top0 res0 key0 klen0 level0 seg0 sl0 child0 : Nat)
    (k : Nat) : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s =>
    AfterAlloc Nd fs sp0 node0 top0 res0 key0 klen0 level0 seg0 sl0 child0 s ∧
    (∃ wtop : BitVec 64, s.locals.lookup (ofString "top") = some (.val (.word wtop)) ∧ wtop.toNat = top0) ∧
    (1 ≤ k → memW s (locN s "fr") = top0) ∧
    (2 ≤ k → memW s (locN s "fr" + 8) = node0) ∧
    (3 ≤ k → memW s (locN s "fr" + 16) = 2) ∧
    (4 ≤ k → memW s (locN s "fr" + 24) = seg0) ∧
    (5 ≤ k → memW s (locN s "fr" + 32) = sl0)

private theorem hoare_framePushProg_word
    (Nd fs : List Nat) (sp0 node0 top0 res0 key0 klen0 level0 seg0 sl0 child0 : Nat) :
    Hoare (StoredAt Nd fs sp0 node0 top0 res0 key0 klen0 level0 seg0 sl0 child0 0)
      framePushProg (fun r t => r = none → MptDeletePost sp0 t) := by
  have hse : scratchEnd < 2 ^ 64 := by decide
  unfold framePushProg
  -- Store 1: `[fr + 0] := top`
  refine hoare_seq_fall (R := StoredAt Nd fs sp0 node0 top0 res0 key0 klen0 level0 seg0 sl0 child0 1)
    (hoare_store_word_off "fr" 0 (.var .local (ofString "top"))
      (fun s v ⟨_, ⟨wtop, hwtop, _⟩, _⟩ hv => by
        simp [evalAt, evalHOLExact, hwtop] at hv; exact ⟨wtop, hv.symm⟩)
      (fun s wb wv ⟨hAA, hWtop, _⟩ hwb hv => by
        obtain ⟨hH, hSt, hge, hsp_e, hRes, hlev_add, hlN, hlT, hlR, hlK, hlKl, hlLv, hlSeg, hlSl,
          hWn, hWseg, hWsl, hWlvl, wfr, hwfr, hlFr, hfr8, hfr_lo, hfr_sp, hsp_eq, hfr_w⟩ := hAA
        obtain ⟨wtop, hwtop, hwtopt⟩ := hWtop
        have hwb_eq : wb = wfr := by rw [hwfr] at hwb; cases hwb; rfl
        subst hwb_eq
        have wv_eq : wtop = wv := by simp [evalAt, evalHOLExact, hwtop] at hv; exact hv
        subst wv_eq
        obtain ⟨hH', hSt'⟩ := store_scratch_preserves (off := 0) (offN := 0) rfl (wv := wtop)
          hH hSt hge hfr_lo (by omega) hfr_sp hsp_e
        have hm0 := store_frame_memW_same s wb wtop 0 0 rfl (by omega)
        refine ⟨⟨hH', hSt', hge, hsp_e, hRes, hlev_add, hlN, hlT, hlR, hlK, hlKl, hlLv, hlSeg, hlSl,
          hWn, hWseg, hWsl, hWlvl, wb, hwfr, hlFr, hfr8, hfr_lo, hfr_sp, hsp_eq,
          wordsOK_transfer hH.1.1 hH'.1.1 hfr_w⟩,
          ⟨wtop, hwtop, hwtopt⟩,
          fun _ => by change memW _ (locN s "fr") = _; rw [hlFr]; simpa [hwtopt] using hm0,
          fun h => by omega, fun h => by omega, fun h => by omega, fun h => by omega⟩))
    ?_
  -- Store 2: `[fr + 8] := node`
  refine hoare_seq_fall (R := StoredAt Nd fs sp0 node0 top0 res0 key0 klen0 level0 seg0 sl0 child0 2)
    (hoare_store_word_off "fr" 8 (.var .local (ofString "node"))
      (fun s v ⟨hAA, _⟩ hv => by
        obtain ⟨wn, hwn, _⟩ := hAA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        simp [evalAt, evalHOLExact, hwn] at hv; exact ⟨wn, hv.symm⟩)
      (fun s wb wv ⟨hAA, hWtop, hs1, _⟩ hwb hv => by
        obtain ⟨hH, hSt, hge, hsp_e, hRes, hlev_add, hlN, hlT, hlR, hlK, hlKl, hlLv, hlSeg, hlSl,
          ⟨wn, hwn, hwnt⟩, hWseg, hWsl, hWlvl, wfr, hwfr, hlFr, hfr8, hfr_lo, hfr_sp, hsp_eq, hfr_w⟩ := hAA
        have hwb_eq : wb = wfr := by rw [hwfr] at hwb; cases hwb; rfl
        subst hwb_eq
        have wv_eq : wn = wv := by simp [evalAt, evalHOLExact, hwn] at hv; exact hv
        subst wv_eq
        obtain ⟨hH', hSt'⟩ := store_scratch_preserves (off := 8) (offN := 8) rfl (wv := wn)
          hH hSt hge hfr_lo (by omega) hfr_sp hsp_e
        have hm8 := store_frame_memW_same s wb wn 8 8 rfl (by omega)
        have hm0 := store_frame_memW_ne s wb wn 8 8 wb.toNat rfl (by omega) (by omega) (by omega)
        refine ⟨⟨hH', hSt', hge, hsp_e, hRes, hlev_add, hlN, hlT, hlR, hlK, hlKl, hlLv, hlSeg, hlSl,
          ⟨wn, hwn, hwnt⟩, hWseg, hWsl, hWlvl, wb, hwfr, hlFr, hfr8, hfr_lo, hfr_sp, hsp_eq,
          wordsOK_transfer hH.1.1 hH'.1.1 hfr_w⟩,
          hWtop,
          fun _ => by change memW _ (locN s "fr") = _; rw [hlFr, hm0, ← hlFr]; exact hs1 (by omega),
          fun _ => by change memW _ (locN s "fr" + 8) = _; rw [hlFr, hm8, hwnt],
          fun h => by omega, fun h => by omega, fun h => by omega⟩))
    ?_
  -- Store 3: `[fr + 16] := 2`
  refine hoare_seq_fall (R := StoredAt Nd fs sp0 node0 top0 res0 key0 klen0 level0 seg0 sl0 child0 3)
    (hoare_store_word_off "fr" 16 (.const 2)
      (fun s v _ hv => ⟨2, evalAt_const s 2 v hv⟩)
      (fun s wb wv ⟨hAA, hWtop, hs1, hs2, _⟩ hwb hv => by
        obtain ⟨hH, hSt, hge, hsp_e, hRes, hlev_add, hlN, hlT, hlR, hlK, hlKl, hlLv, hlSeg, hlSl,
          hWn, hWseg, hWsl, hWlvl, wfr, hwfr, hlFr, hfr8, hfr_lo, hfr_sp, hsp_eq, hfr_w⟩ := hAA
        have hwb_eq : wb = wfr := by rw [hwfr] at hwb; cases hwb; rfl
        subst hwb_eq
        have wv_eq : wv = 2 := by cases evalAt_const s 2 _ hv; rfl
        subst wv_eq
        obtain ⟨hH', hSt'⟩ := store_scratch_preserves (off := 16) (offN := 16) rfl (wv := 2)
          hH hSt hge hfr_lo (by omega) hfr_sp hsp_e
        have hm16 := store_frame_memW_same s wb 2 16 16 rfl (by omega)
        have hm0 := store_frame_memW_ne s wb 2 16 16 wb.toNat rfl (by omega) (by omega) (by omega)
        have hm8 := store_frame_memW_ne s wb 2 16 16 (wb.toNat + 8) rfl (by omega) (by omega) (by omega)
        refine ⟨⟨hH', hSt', hge, hsp_e, hRes, hlev_add, hlN, hlT, hlR, hlK, hlKl, hlLv, hlSeg, hlSl,
          hWn, hWseg, hWsl, hWlvl, wb, hwfr, hlFr, hfr8, hfr_lo, hfr_sp, hsp_eq,
          wordsOK_transfer hH.1.1 hH'.1.1 hfr_w⟩,
          hWtop,
          fun _ => by change memW _ (locN s "fr") = _; rw [hlFr, hm0, ← hlFr]; exact hs1 (by omega),
          fun _ => by change memW _ (locN s "fr" + 8) = _; rw [hlFr, hm8, ← hlFr]; exact hs2 (by omega),
          fun _ => by change memW _ (locN s "fr" + 16) = _; rw [hlFr, hm16]; rfl,
          fun h => by omega, fun h => by omega⟩))
    ?_
  -- Store 4: `[fr + 24] := seg`
  refine hoare_seq_fall (R := StoredAt Nd fs sp0 node0 top0 res0 key0 klen0 level0 seg0 sl0 child0 4)
    (hoare_store_word_off "fr" 24 (.var .local (ofString "seg"))
      (fun s v ⟨hAA, _⟩ hv => by
        obtain ⟨wseg, hwseg, _⟩ := hAA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        simp [evalAt, evalHOLExact, hwseg] at hv; exact ⟨wseg, hv.symm⟩)
      (fun s wb wv ⟨hAA, hWtop, hs1, hs2, hs3, _⟩ hwb hv => by
        obtain ⟨hH, hSt, hge, hsp_e, hRes, hlev_add, hlN, hlT, hlR, hlK, hlKl, hlLv, hlSeg, hlSl,
          hWn, ⟨wseg, hwseg, hwsegt⟩, hWsl, hWlvl, wfr, hwfr, hlFr, hfr8, hfr_lo, hfr_sp, hsp_eq, hfr_w⟩ := hAA
        have hwb_eq : wb = wfr := by rw [hwfr] at hwb; cases hwb; rfl
        subst hwb_eq
        have wv_eq : wseg = wv := by simp [evalAt, evalHOLExact, hwseg] at hv; exact hv
        subst wv_eq
        obtain ⟨hH', hSt'⟩ := store_scratch_preserves (off := 24) (offN := 24) rfl (wv := wseg)
          hH hSt hge hfr_lo (by omega) hfr_sp hsp_e
        have hm24 := store_frame_memW_same s wb wseg 24 24 rfl (by omega)
        have hm0 := store_frame_memW_ne s wb wseg 24 24 wb.toNat rfl (by omega) (by omega) (by omega)
        have hm8 := store_frame_memW_ne s wb wseg 24 24 (wb.toNat + 8) rfl (by omega) (by omega) (by omega)
        have hm16 := store_frame_memW_ne s wb wseg 24 24 (wb.toNat + 16) rfl (by omega) (by omega) (by omega)
        refine ⟨⟨hH', hSt', hge, hsp_e, hRes, hlev_add, hlN, hlT, hlR, hlK, hlKl, hlLv, hlSeg, hlSl,
          hWn, ⟨wseg, hwseg, hwsegt⟩, hWsl, hWlvl, wb, hwfr, hlFr, hfr8, hfr_lo, hfr_sp, hsp_eq,
          wordsOK_transfer hH.1.1 hH'.1.1 hfr_w⟩,
          hWtop,
          fun _ => by change memW _ (locN s "fr") = _; rw [hlFr, hm0, ← hlFr]; exact hs1 (by omega),
          fun _ => by change memW _ (locN s "fr" + 8) = _; rw [hlFr, hm8, ← hlFr]; exact hs2 (by omega),
          fun _ => by change memW _ (locN s "fr" + 16) = _; rw [hlFr, hm16, ← hlFr]; exact hs3 (by omega),
          fun _ => by change memW _ (locN s "fr" + 24) = _; rw [hlFr, hm24, hwsegt],
          fun h => by omega⟩))
    ?_
  -- Store 5: `[fr + 32] := sl`
  refine hoare_seq_fall (R := StoredAt Nd fs sp0 node0 top0 res0 key0 klen0 level0 seg0 sl0 child0 5)
    (hoare_store_word_off "fr" 32 (.var .local (ofString "sl"))
      (fun s v ⟨hAA, _⟩ hv => by
        obtain ⟨wsl, hwsl, _⟩ := hAA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        simp [evalAt, evalHOLExact, hwsl] at hv; exact ⟨wsl, hv.symm⟩)
      (fun s wb wv ⟨hAA, hWtop, hs1, hs2, hs3, hs4, _⟩ hwb hv => by
        obtain ⟨hH, hSt, hge, hsp_e, hRes, hlev_add, hlN, hlT, hlR, hlK, hlKl, hlLv, hlSeg, hlSl,
          hWn, hWseg, ⟨wsl, hwsl, hwslt⟩, hWlvl, wfr, hwfr, hlFr, hfr8, hfr_lo, hfr_sp, hsp_eq, hfr_w⟩ := hAA
        have hwb_eq : wb = wfr := by rw [hwfr] at hwb; cases hwb; rfl
        subst hwb_eq
        have wv_eq : wsl = wv := by simp [evalAt, evalHOLExact, hwsl] at hv; exact hv
        subst wv_eq
        obtain ⟨hH', hSt'⟩ := store_scratch_preserves (off := 32) (offN := 32) rfl (wv := wsl)
          hH hSt hge hfr_lo (by omega) hfr_sp hsp_e
        have hm32 := store_frame_memW_same s wb wsl 32 32 rfl (by omega)
        have hm0 := store_frame_memW_ne s wb wsl 32 32 wb.toNat rfl (by omega) (by omega) (by omega)
        have hm8 := store_frame_memW_ne s wb wsl 32 32 (wb.toNat + 8) rfl (by omega) (by omega) (by omega)
        have hm16 := store_frame_memW_ne s wb wsl 32 32 (wb.toNat + 16) rfl (by omega) (by omega) (by omega)
        have hm24 := store_frame_memW_ne s wb wsl 32 32 (wb.toNat + 24) rfl (by omega) (by omega) (by omega)
        refine ⟨⟨hH', hSt', hge, hsp_e, hRes, hlev_add, hlN, hlT, hlR, hlK, hlKl, hlLv, hlSeg, hlSl,
          hWn, hWseg, ⟨wsl, hwsl, hwslt⟩, hWlvl, wb, hwfr, hlFr, hfr8, hfr_lo, hfr_sp, hsp_eq,
          wordsOK_transfer hH.1.1 hH'.1.1 hfr_w⟩,
          hWtop,
          fun _ => by change memW _ (locN s "fr") = _; rw [hlFr, hm0, ← hlFr]; exact hs1 (by omega),
          fun _ => by change memW _ (locN s "fr" + 8) = _; rw [hlFr, hm8, ← hlFr]; exact hs2 (by omega),
          fun _ => by change memW _ (locN s "fr" + 16) = _; rw [hlFr, hm16, ← hlFr]; exact hs3 (by omega),
          fun _ => by change memW _ (locN s "fr" + 24) = _; rw [hlFr, hm24, ← hlFr]; exact hs4 (by omega),
          fun _ => by change memW _ (locN s "fr" + 32) = _; rw [hlFr, hm32, hwslt]⟩))
    ?_
  -- Assemble `MptStack s Nd fr0 (fr0 :: fs)` right before the 4 local assignments!
  let Ready4 : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop := fun s =>
    HeapInv Nd node0 key0 klen0 level0 seg0 sl0 child0 s ∧
    RootIn Nd res0 ∧ level0 + sl0 ≤ klen0 ∧
    globN s "scratch_ptr" + 40 ≤ sp0 ∧
    MptStack s Nd (locN s "fr") (locN s "fr" :: fs) ∧
    locN s "node" = node0 ∧ locN s "res" = res0 ∧
    locN s "key" = key0 ∧ locN s "klen" = klen0 ∧
    locN s "level" = level0 ∧ locN s "sl" = sl0 ∧
    (∃ wfr : BitVec 64, s.locals.lookup (ofString "fr") = some (.val (.word wfr)) ∧ wfr.toNat = locN s "fr")
  refine Hoare.mono (P' := Ready4) ?_ (fun s ⟨hAA, _, hs1, hs2, hs3, hs4, hs5⟩ => by
    obtain ⟨hH, hSt, hge, hsp_e, hRes, hlev_add, hlN, _, hlR, hlK, hlKl, hlLv, _, hlSl,
      _, _, _, _, wfr, hwfr, hlFr, _, hfr_lo, hfr_sp, hsp_eq, hfr_w⟩ := hAA
    have hfr_ne0 : locN s "fr" ≠ 0 := by
      have : 0 < scratchStart := by decide
      omega
    have hFrameOK : MptFrameOK s Nd (locN s "fr") := by
      refine ⟨⟨by rw [hsp_eq, hlFr], by omega⟩, by rw [hlFr]; exact hfr_w, ?_⟩
      dsimp only
      rw [hs2 (by omega)]
      refine ⟨hH.2.2.1, Or.inl ⟨hs3 (by omega), hH.2.2.2.1, ?_⟩⟩
      rw [hs4 (by omega), hs5 (by omega)]
      exact hH.2.2.2.2.2.2.2.2.2
    refine ⟨hH, hRes, hlev_add, by omega,
      ⟨rfl, hfr_ne0, hFrameOK, fun r hr => by have := hge r hr; omega,
        by rw [hs1 (by omega)]; exact hSt⟩,
      hlN, hlR, hlK, hlKl, hlLv, hlSl, wfr, hwfr, hlFr.symm⟩)
  -- Assign 1: `top := fr`
  let Ready3 : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop := fun s =>
    HeapInv Nd node0 key0 klen0 level0 seg0 sl0 child0 s ∧
    RootIn Nd res0 ∧ level0 + sl0 ≤ klen0 ∧
    globN s "scratch_ptr" + 40 ≤ sp0 ∧
    MptStack s Nd (locN s "top") (locN s "top" :: fs) ∧
    locN s "node" = node0 ∧ locN s "res" = res0 ∧
    locN s "key" = key0 ∧ locN s "klen" = klen0 ∧
    locN s "level" = level0 ∧ locN s "sl" = sl0
  refine hoare_seq_fall (R := Ready3)
    (hoare_assign_fall fun s v hs hv _ => by
      obtain ⟨hH, hRes, hlev_add, hsp_le, hStF, hlN, hlR, hlK, hlKl, hlLv, hlSl,
        wfr, hwfr, hwfrt⟩ := hs
      have hv_eq : v = .val (.word wfr) := by
        simp [evalAt, evalHOLExact, hwfr] at hv; exact hv.symm
      subst hv_eq
      have htop' : locN (setKvarHOLFinite .local (ofString "top") (.val (.word wfr)) s) "top" =
          locN s "fr" := by
        simpa [setKvarHOLFinite, hwfrt] using locN_setVar_same s "top" wfr
      refine ⟨(heapInv_with_locals s _ s.clock _ _ _ _ _ _ _ _).2 hH,
        hRes, hlev_add, hsp_le, ?_,
        by simpa [setKvarHOLFinite] using (locN_setVar_ne s "node" (ofString "top") _ (by decide)).trans hlN,
        by simpa [setKvarHOLFinite] using (locN_setVar_ne s "res" (ofString "top") _ (by decide)).trans hlR,
        by simpa [setKvarHOLFinite] using (locN_setVar_ne s "key" (ofString "top") _ (by decide)).trans hlK,
        by simpa [setKvarHOLFinite] using (locN_setVar_ne s "klen" (ofString "top") _ (by decide)).trans hlKl,
        by simpa [setKvarHOLFinite] using (locN_setVar_ne s "level" (ofString "top") _ (by decide)).trans hlLv,
        by simpa [setKvarHOLFinite] using (locN_setVar_ne s "sl" (ofString "top") _ (by decide)).trans hlSl⟩
      rw [htop']
      exact (mptStack_with_locals s _ s.clock Nd (locN s "fr" :: fs) (locN s "fr")).2 hStF)
    ?_
  -- Assign 2: `node := load (node + 48)`
  let Ready2 : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop := fun s =>
    HeapInv Nd node0 key0 klen0 level0 seg0 sl0 child0 s ∧
    RootIn Nd res0 ∧ level0 + sl0 ≤ klen0 ∧
    globN s "scratch_ptr" + 40 ≤ sp0 ∧
    MptStack s Nd (locN s "top") (locN s "top" :: fs) ∧
    locN s "node" = child0 ∧ locN s "res" = res0 ∧
    locN s "key" = key0 ∧ locN s "klen" = klen0 ∧
    locN s "level" = level0 ∧ locN s "sl" = sl0
  refine hoare_seq_fall (R := Ready2)
    (hoare_assign_fall fun s v hs hv _ => by
      obtain ⟨hH, hRes, hlev_add, hsp_le, hStF, hlN, hlR, hlK, hlKl, hlLv, hlSl⟩ := hs
      obtain ⟨wch, rfl, hwch⟩ := evalAt_loadL s "node" 48 v hv
      have hch_eq : wch.toNat = child0 := by
        simpa [hlN, hH.2.2.2.2.2.2.1] using hwch
      have htop_eq : locN (setKvarHOLFinite .local (ofString "node") (.val (.word wch)) s) "top" =
          locN s "top" := locN_setVar_ne s "top" (ofString "node") _ (by decide)
      refine ⟨(heapInv_with_locals s _ s.clock _ _ _ _ _ _ _ _).2 hH,
        hRes, hlev_add, hsp_le, ?_,
        by simpa [setKvarHOLFinite, hch_eq] using locN_setVar_same s "node" wch,
        by simpa [setKvarHOLFinite] using (locN_setVar_ne s "res" (ofString "node") _ (by decide)).trans hlR,
        by simpa [setKvarHOLFinite] using (locN_setVar_ne s "key" (ofString "node") _ (by decide)).trans hlK,
        by simpa [setKvarHOLFinite] using (locN_setVar_ne s "klen" (ofString "node") _ (by decide)).trans hlKl,
        by simpa [setKvarHOLFinite] using (locN_setVar_ne s "level" (ofString "node") _ (by decide)).trans hlLv,
        by simpa [setKvarHOLFinite] using (locN_setVar_ne s "sl" (ofString "node") _ (by decide)).trans hlSl⟩
      rw [htop_eq]
      exact (mptStack_with_locals s _ s.clock Nd (locN s "top" :: fs) (locN s "top")).2 hStF)
    ?_
  -- Assign 3: `level := level + sl`
  let Ready1 : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop := fun s =>
    HeapInv Nd node0 key0 klen0 level0 seg0 sl0 child0 s ∧
    RootIn Nd res0 ∧ level0 + sl0 ≤ klen0 ∧
    globN s "scratch_ptr" + 40 ≤ sp0 ∧
    MptStack s Nd (locN s "top") (locN s "top" :: fs) ∧
    locN s "node" = child0 ∧ locN s "res" = res0 ∧
    locN s "key" = key0 ∧ locN s "klen" = klen0 ∧
    locN s "level" = level0 + sl0
  refine hoare_seq_fall (R := Ready1)
    (hoare_assign_fall fun s v hs hv _ => by
      obtain ⟨hH, hRes, hlev_add, hsp_le, hStF, hlN, hlR, hlK, hlKl, hlLv, hlSl⟩ := hs
      obtain ⟨wl, wsl, _, _, hwl_t, hwsl_t, rfl⟩ := evalAt_add_locals s "level" "sl" v hv
      have hklen_lt : klen0 < 2 ^ 64 := by
        rw [← hlKl]
        unfold locN
        split
        · rename_i w _; exact w.isLt
        · decide
      have hadd_t : (wl + wsl).toNat = level0 + sl0 := by
        rw [BitVec.toNat_add, hwl_t, hwsl_t, hlLv, hlSl, Nat.mod_eq_of_lt (by omega)]
      have htop_eq : locN (setKvarHOLFinite .local (ofString "level") (.val (.word (wl + wsl))) s) "top" =
          locN s "top" := locN_setVar_ne s "top" (ofString "level") _ (by decide)
      refine ⟨(heapInv_with_locals s _ s.clock _ _ _ _ _ _ _ _).2 hH,
        hRes, hlev_add, hsp_le, ?_,
        by simpa [setKvarHOLFinite] using (locN_setVar_ne s "node" (ofString "level") _ (by decide)).trans hlN,
        by simpa [setKvarHOLFinite] using (locN_setVar_ne s "res" (ofString "level") _ (by decide)).trans hlR,
        by simpa [setKvarHOLFinite] using (locN_setVar_ne s "key" (ofString "level") _ (by decide)).trans hlK,
        by simpa [setKvarHOLFinite] using (locN_setVar_ne s "klen" (ofString "level") _ (by decide)).trans hlKl,
        by simpa [setKvarHOLFinite, hadd_t] using locN_setVar_same s "level" (wl + wsl)⟩
      rw [htop_eq]
      exact (mptStack_with_locals s _ s.clock Nd (locN s "top" :: fs) (locN s "top")).2 hStF)
    ?_
  -- Assign 4: `go := 1`
  refine hoare_assign_fall fun s v hs hv _ => by
    obtain ⟨hH, hRes, hlev_add, hsp_le, hStF, hlN, hlR, hlK, hlKl, hlLv⟩ := hs
    cases evalAt_const s 1 v hv
    set t := setKvarHOLFinite .local (ofString "go") (.val (.word 1)) s
    have hH_t : HeapInv Nd node0 key0 klen0 level0 seg0 sl0 child0 t :=
      (heapInv_with_locals s _ s.clock _ _ _ _ _ _ _ _).2 hH
    have htop_t : locN t "top" = locN s "top" :=
      locN_setVar_ne s "top" (ofString "go") _ (by decide)
    have hres_t : locN t "res" = res0 :=
      (locN_setVar_ne s "res" (ofString "go") _ (by decide)).trans hlR
    have hnode_t : locN t "node" = child0 :=
      (locN_setVar_ne s "node" (ofString "go") _ (by decide)).trans hlN
    have hkey_t : locN t "key" = key0 :=
      (locN_setVar_ne s "key" (ofString "go") _ (by decide)).trans hlK
    have hklen_t : locN t "klen" = klen0 :=
      (locN_setVar_ne s "klen" (ofString "go") _ (by decide)).trans hlKl
    have hlev_t : locN t "level" = level0 + sl0 :=
      (locN_setVar_ne s "level" (ofString "go") _ (by decide)).trans hlLv
    have hSt_t : MptStack t Nd (locN t "top") (locN s "top" :: fs) := by
      rw [htop_t]
      exact (mptStack_with_locals s _ s.clock Nd (locN s "top" :: fs) (locN s "top")).2 hStF
    refine ⟨⟨hH_t.1, Nd, locN s "top" :: fs, hH_t.2.1, hSt_t,
      by rw [hres_t]; exact hRes,
      fun _ => ⟨by rw [hlev_t, hklen_t]; exact hlev_add,
        by rw [hnode_t]; exact hH_t.2.2.2.2.2.2.2.1, ?_⟩⟩,
      Or.inr hsp_le⟩
    rw [hkey_t, hlev_t, hklen_t]
    have hadd_eq : key0 + (level0 + sl0) = (key0 + level0) + sl0 := by omega
    have hsub_eq : klen0 - (level0 + sl0) = (klen0 - level0) - sl0 := by omega
    rw [hadd_eq, hsub_eq]
    exact keyIn_suffix (by omega) hH_t.2.2.2.2.2.2.2.2.1

private theorem hoare_framePushProg_nonword (sp0 : Nat) :
    Hoare (fun s =>
        (¬ ∃ wtop : BitVec 64, s.locals.lookup (ofString "top") = some (.val (.word wtop))) ∧
        (∃ wfr : BitVec 64, s.locals.lookup (ofString "fr") = some (.val (.word wfr))))
      framePushProg (fun r t => r = none → MptDeletePost sp0 t) := by
  let Bad : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop := fun s =>
    (¬ ∃ wtop : BitVec 64, s.locals.lookup (ofString "top") = some (.val (.word wtop))) ∧
    (∃ wfr : BitVec 64, s.locals.lookup (ofString "fr") = some (.val (.word wfr)))
  have hkeep : ∀ {F : Type} (s t : PanSemStateFiniteExact 64 F),
      t.locals = s.locals → Bad s → Bad t := by
    intro F s t heq hb
    dsimp only [Bad] at hb ⊢
    rw [heq]; exact hb
  unfold framePushProg
  refine hoare_seq_fall (hoare_store_locals_fall _ _ hkeep)
    (hoare_seq_fall (hoare_store_locals_fall _ _ hkeep)
      (hoare_seq_fall (hoare_store_locals_fall _ _ hkeep)
        (hoare_seq_fall (hoare_store_locals_fall _ _ hkeep)
          (hoare_seq_fall (hoare_store_locals_fall _ _ hkeep) ?_))))
  refine hoare_seq_fall (R := fun _ => False)
    (hoare_assign_fall fun s v ⟨hnot, wfr, hwfr⟩ hv hval => by
      have hv_eq : v = .val (.word wfr) := by
        simp [evalAt, evalHOLExact, hwfr] at hv; exact hv.symm
      subst hv_eq
      exact hnot (isValid_local_word_iff s (ofString "top") wfr hval))
    (Hoare.of_false fun _ hf => hf)

private theorem hoare_framePushProg
    (Nd fs : List Nat) (sp0 node0 top0 res0 key0 klen0 level0 seg0 sl0 child0 : Nat) :
    Hoare (AfterAlloc Nd fs sp0 node0 top0 res0 key0 klen0 level0 seg0 sl0 child0)
      framePushProg (fun r t => r = none → MptDeletePost sp0 t) := by
  refine ⟨fun {F} s hcode hAA hnt hr => ?_⟩
  by_cases htop : ∃ wtop : BitVec 64, s.locals.lookup (ofString "top") = some (.val (.word wtop))
  · obtain ⟨wtop, hwtop⟩ := htop
    have hwtopt : wtop.toNat = top0 := by
      have hlT := hAA.2.2.2.2.2.2.2.1
      unfold locN at hlT
      rw [hwtop] at hlT
      exact hlT
    exact (hoare_framePushProg_word Nd fs sp0 node0 top0 res0 key0 klen0 level0 seg0 sl0 child0).run
      s hcode ⟨hAA, ⟨wtop, hwtop, hwtopt⟩, fun h => by omega, fun h => by omega,
        fun h => by omega, fun h => by omega, fun h => by omega⟩ hnt hr
  · obtain ⟨wfr, hwfr, _⟩ := hAA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    exact (hoare_framePushProg_nonword sp0).run s hcode ⟨htop, wfr, hwfr⟩ hnt hr

/-! ### 5. Main `kind = 2` iteration walk -/

private theorem mptDelete_kind2_hoare (h : MptDeleteCallees) {F₀ : Type}
    (s0 : PanSemStateFiniteExact 64 F₀)
    (hc0 : s0.code = originalRuntimeCode)
    (hp0 : MptDeleteActive s0) (hk0 : mptKind s0 = 2)
    (hnt0 : (evaluateHOLFiniteState s0 mptDeleteBody).1 ≠ some .timeOut)
    (hnone0 : (evaluateHOLFiniteState s0 mptDeleteBody).1 = none) :
    MptDeleteHead (evaluateHOLFiniteState s0 mptDeleteBody).2 ∧
      MptDeleteEffect s0 (evaluateHOLFiniteState s0 mptDeleteBody).2 := by
  obtain ⟨⟨hA0, Nd, fs, hNd0, hSt0, hRes0, hAct0⟩, hGo0⟩ := hp0
  obtain ⟨hLev0, hNodeRoot0, hKey0⟩ := hAct0 hGo0
  have hNodeNe0 : locN s0 "node" ≠ 0 := by
    intro hz; simp [mptKind, hz] at hk0
  have hNodeKind0 : memW s0 (locN s0 "node") = 2 := by
    simpa [mptKind, hNodeNe0] using hk0
  have hNodeIn0 : locN s0 "node" ∈ Nd := hNodeRoot0.resolve_left hNodeNe0
  have hNodeWord0 : ∃ wn : BitVec 64,
      s0.locals.lookup (ofString "node") = some (.val (.word wn)) ∧ wn.toNat = locN s0 "node" := by
    unfold locN at hNodeNe0 ⊢
    rcases hl : s0.locals.lookup (ofString "node") with _ | v
    · simp [hl] at hNodeNe0
    · rcases v with wl | _ | _
      · cases wl with
        | word wn => exact ⟨wn, rfl, by simp⟩
      · simp [hl] at hNodeNe0
      · simp [hl] at hNodeNe0
  obtain ⟨_, _, _, _, hext0, _, hpath0, _⟩ := hNd0.1 (locN s0 "node") hNodeIn0
  set sp0 := globN s0 "scratch_ptr"
  set node0 := locN s0 "node"
  set top0 := locN s0 "top"
  set res0 := locN s0 "res"
  set key0 := locN s0 "key"
  set klen0 := locN s0 "klen"
  set level0 := locN s0 "level"
  set seg0 := memW s0 (node0 + 32)
  set sl0 := memW s0 (node0 + 40)
  set child0 := memW s0 (node0 + 48)
  have hH0 : HeapInv Nd node0 key0 klen0 level0 seg0 sl0 child0 s0 :=
    ⟨hA0, hNd0, hNodeIn0, hNodeKind0, rfl, rfl, rfl, hext0 hNodeKind0,
      hKey0, hpath0 (Or.inr hNodeKind0)⟩
  let P0 : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
    PreBody Nd fs sp0 node0 top0 res0 key0 klen0 level0 seg0 sl0 child0
  suffices hmain : Hoare P0 mptDeleteBody (fun r t => r = none → MptDeletePost sp0 t) by
    exact hmain.run s0 hc0
      ⟨hH0, hSt0, hRes0, hLev0, hNodeNe0, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hNodeWord0⟩
      hnt0 hnone0
  dsimp only [mptDeleteBody, mptWhileBody, mptLeft, mptDeleteTail, mptDecBody, mptDeleteCode,
    sourceFunctionEntry, Guest.Software.guestFn__mpt_delete_node_body,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    List.map, Option.map]
  -- Step 1: `go := 0`
  refine hoare_seq_fall (R := fun s => P0 s ∧ locN s "go" = 0)
    (hoare_assign_fall fun s v hs hv _ => by
      cases evalAt_const s 0 v hv
      obtain ⟨hH, hSt, hRes, hLev, hN0, hSp, hlN, hlT, hlR, hlK, hlKl, hlLv, wn, hwn, hwnt⟩ := hs
      refine ⟨⟨(heapInv_with_locals s _ s.clock _ _ _ _ _ _ _ _).2 hH,
        by simpa [setKvarHOLFinite, setVarHOLFinite, mptStack_with_locals] using hSt,
        hRes, hLev, hN0, hSp,
        by simpa [setKvarHOLFinite] using (locN_setVar_ne s "node" (ofString "go") _ (by decide)).trans hlN,
        by simpa [setKvarHOLFinite] using (locN_setVar_ne s "top" (ofString "go") _ (by decide)).trans hlT,
        by simpa [setKvarHOLFinite] using (locN_setVar_ne s "res" (ofString "go") _ (by decide)).trans hlR,
        by simpa [setKvarHOLFinite] using (locN_setVar_ne s "key" (ofString "go") _ (by decide)).trans hlK,
        by simpa [setKvarHOLFinite] using (locN_setVar_ne s "klen" (ofString "go") _ (by decide)).trans hlKl,
        by simpa [setKvarHOLFinite] using (locN_setVar_ne s "level" (ofString "go") _ (by decide)).trans hlLv,
        wn, by simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
          (show ofString "go" ≠ ofString "node" by decide), hwn], hwnt⟩,
        by simpa [setKvarHOLFinite] using locN_setVar_same s "go" 0⟩)
    ?_
  -- Step 2: `if node == 0` (`yes` impossible since `node0 ≠ 0`)
  refine hoare_ite_fall
    (Hoare.of_false fun s ⟨⟨hs, _⟩, hct⟩ => by
      have hz := condTrue_local_eq_const hct
      rw [hs.2.2.2.2.2.2.1] at hz
      exact hs.2.2.2.2.1 hz)
    ?_
  -- Step 3: `dec k := load (node + 0)`
  refine hoare_dec_fall (P' := fun s => P0 s ∧ locN s "go" = 0 ∧ locN s "k" = 2)
    (by decide) (localsOnly_mptDeletePost sp0)
    (fun s v ⟨⟨hs, hgo⟩, _⟩ hv => by
      obtain ⟨wk, rfl, hwk⟩ := evalAt_loadL s "node" 0 v hv
      obtain ⟨hH, hSt, hRes, hLev, hN0, hSp, hlN, hlT, hlR, hlK, hlKl, hlLv, wn, hwn, hwnt⟩ := hs
      have hk2 : wk.toNat = 2 := by
        simpa [hlN, Nat.add_zero, hH.2.2.2.1] using hwk
      refine ⟨⟨(heapInv_with_locals s _ s.clock _ _ _ _ _ _ _ _).2 hH,
        by simpa [setVarHOLFinite, mptStack_with_locals] using hSt,
        hRes, hLev, hN0, hSp,
        (locN_setVar_ne s "node" (ofString "k") _ (by decide)).trans hlN,
        (locN_setVar_ne s "top" (ofString "k") _ (by decide)).trans hlT,
        (locN_setVar_ne s "res" (ofString "k") _ (by decide)).trans hlR,
        (locN_setVar_ne s "key" (ofString "k") _ (by decide)).trans hlK,
        (locN_setVar_ne s "klen" (ofString "k") _ (by decide)).trans hlKl,
        (locN_setVar_ne s "level" (ofString "k") _ (by decide)).trans hlLv,
        wn, by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
          (show ofString "k" ≠ ofString "node" by decide), hwn], hwnt⟩,
        (locN_setVar_ne s "go" (ofString "k") _ (by decide)).trans hgo,
        by rw [locN_setVar_same]; exact hk2⟩)
    ?_
  -- Step 4: `if k == 0` (`yes` impossible since `k = 2`)
  refine hoare_seq_fall (R := fun s => P0 s ∧ locN s "go" = 0 ∧ locN s "k" = 2)
    (hoare_ite_fall
      (Hoare.of_false fun s ⟨⟨_, _, hk2⟩, hct⟩ => by
        have hz := condTrue_local_eq_const hct
        rw [hk2] at hz; simp at hz)
      (Hoare.skip fun _ hs _ => hs.1))
    ?_
  -- Step 5: `call node_invalidate(node)` via `h.iz_node_invalidate`
  refine hoare_seq_fall
    (R := AfterInvalidate Nd fs sp0 node0 top0 res0 key0 klen0 level0 seg0 sl0 child0)
    (hoare_call0_fall fun state values body callee ret value post hcode ⟨hs, hgo, hk2⟩ hargs hl hb => by
      obtain ⟨hH, hSt, hRes, hLev, _, hSp, hlN, hlT, hlR, hlK, hlKl, hlLv, wn, hwn, hwnt⟩ := hs
      have hlk : state.code.lookup (ofString "node_invalidate") =
          some ([(ofString "nd", .one)],
            (sourceFunctionEntry Guest.Software.guestFn_node_invalidate).2.2.1, .one) := by
        rw [hcode, lookup_node_invalidate]; rfl
      obtain ⟨v1, hv1, hc_nd⟩ := callee_param_one_exp state _ _ _ _ _ hlk _ values body
        callee ret hargs hl
      have hv1_eq : v1 = .val (.word wn) := by
        simp [evalAt, evalHOLExact, hwn] at hv1; exact hv1.symm
      subst hv1_eq
      have hloc_nd : locN (callEntryStateHOLFinite state callee) "nd" = node0 := by
        simp [locN, callEntryStateHOLFinite, hc_nd, hwnt]
      have hNodeArgs : NodeArgs ["nd"] (fun _ _ => True) (callEntryStateHOLFinite state callee) := by
        refine ⟨localsFree_arenaReady state callee (state.clock - 1) hH.1, Nd, hH.2.1, ?_, trivial⟩
        intro nm hnm; simp at hnm; subst hnm
        rw [hloc_nd]; exact Or.inr hH.2.2.1
      have hiz0 := FunSpec.at_lookup h.iz_node_invalidate state hcode values body callee ret hl
        hNodeArgs (by rw [hb]; simp)
      rw [hb] at hiz0
      have hiz := hiz0 (Or.inl ⟨value, rfl⟩)
      change post = { clearCache (callEntryStateHOLFinite state callee)
          (locN (callEntryStateHOLFinite state callee) "nd") with
        locals := post.locals, clock := post.clock } at hiz
      rw [hloc_nd] at hiz
      have heq_post : { post with locals := state.locals } =
          { clearCache state node0 with locals := state.locals, clock := post.clock } := by
        rw [hiz]; rfl
      rw [heq_post]
      exact ⟨(heapInv_with_locals (clearCache state node0) _ post.clock _ _ _ _ _ _ _ _).2
          (clearCache_heapInv hH),
        (mptStack_with_locals (clearCache state node0) _ post.clock Nd fs top0).2
          (clearCache_mptStack hH.1 hH.2.1 hH.2.2.1 fs top0 hSt),
        hRes, hLev, hSp, hgo, hk2, hlN, hlT, hlR, hlK, hlKl, hlLv, wn, hwn, hwnt⟩)
    ?_
  -- Step 6: `if k == 1` (`yes` impossible), then `if k == 2` (`no` impossible)
  refine hoare_ite_fall
    (Hoare.of_false fun s ⟨hAI, hct⟩ => by
      have hz := condTrue_local_eq_const hct
      rw [hAI.2.2.2.2.2.2.1] at hz; simp at hz)
    (hoare_ite_fall ?_
      (Hoare.of_false fun s ⟨⟨hAI, _⟩, hcf⟩ => by
        have hne := condFalse_local_eq_const hcf
        exact hne hAI.2.2.2.2.2.2.1))
  -- Step 7: `dec seg := load (node + 32)`, `dec sl := load (node + 40)`
  refine hoare_dec_fall
    (P' := fun s => AfterInvalidate Nd fs sp0 node0 top0 res0 key0 klen0 level0 seg0 sl0 child0 s ∧
      locN s "seg" = seg0 ∧
      ∃ wseg : BitVec 64, s.locals.lookup (ofString "seg") = some (.val (.word wseg)) ∧ wseg.toNat = seg0)
    (by decide) (localsOnly_mptDeletePost sp0)
    (fun s v ⟨⟨hAI, _⟩, _⟩ hv => by
      obtain ⟨wseg, rfl, hwseg⟩ := evalAt_loadL s "node" 32 v hv
      obtain ⟨hH, hSt, hRes, hLev, hSp, hgo, hk2, hlN, hlT, hlR, hlK, hlKl, hlLv, wn, hwn, hwnt⟩ := hAI
      have hseg_eq : wseg.toNat = seg0 := by
        simpa [hlN, hH.2.2.2.2.1] using hwseg
      refine ⟨⟨(heapInv_with_locals s _ s.clock _ _ _ _ _ _ _ _).2 hH,
        by simpa [setVarHOLFinite, mptStack_with_locals] using hSt,
        hRes, hLev, hSp,
        (locN_setVar_ne s "go" (ofString "seg") _ (by decide)).trans hgo,
        (locN_setVar_ne s "k" (ofString "seg") _ (by decide)).trans hk2,
        (locN_setVar_ne s "node" (ofString "seg") _ (by decide)).trans hlN,
        (locN_setVar_ne s "top" (ofString "seg") _ (by decide)).trans hlT,
        (locN_setVar_ne s "res" (ofString "seg") _ (by decide)).trans hlR,
        (locN_setVar_ne s "key" (ofString "seg") _ (by decide)).trans hlK,
        (locN_setVar_ne s "klen" (ofString "seg") _ (by decide)).trans hlKl,
        (locN_setVar_ne s "level" (ofString "seg") _ (by decide)).trans hlLv,
        wn, by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
          (show ofString "seg" ≠ ofString "node" by decide), hwn], hwnt⟩,
        by rw [locN_setVar_same]; exact hseg_eq,
        wseg, by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE], hseg_eq⟩)
    ?_
  refine hoare_dec_fall
    (P' := BeforePrefix Nd fs sp0 node0 top0 res0 key0 klen0 level0 seg0 sl0 child0)
    (by decide) (localsOnly_mptDeletePost sp0)
    (fun s v ⟨hAI, hlSeg, wseg, hwseg, hwsegt⟩ hv => by
      obtain ⟨wsl, rfl, hwsl⟩ := evalAt_loadL s "node" 40 v hv
      obtain ⟨hH, hSt, hRes, hLev, hSp, hgo, hk2, hlN, hlT, hlR, hlK, hlKl, hlLv, wn, hwn, hwnt⟩ := hAI
      have hsl_eq : wsl.toNat = sl0 := by
        simpa [hlN, hH.2.2.2.2.2.1] using hwsl
      refine ⟨⟨(heapInv_with_locals s _ s.clock _ _ _ _ _ _ _ _).2 hH,
        by simpa [setVarHOLFinite, mptStack_with_locals] using hSt,
        hRes, hLev, hSp,
        (locN_setVar_ne s "go" (ofString "sl") _ (by decide)).trans hgo,
        (locN_setVar_ne s "k" (ofString "sl") _ (by decide)).trans hk2,
        (locN_setVar_ne s "node" (ofString "sl") _ (by decide)).trans hlN,
        (locN_setVar_ne s "top" (ofString "sl") _ (by decide)).trans hlT,
        (locN_setVar_ne s "res" (ofString "sl") _ (by decide)).trans hlR,
        (locN_setVar_ne s "key" (ofString "sl") _ (by decide)).trans hlK,
        (locN_setVar_ne s "klen" (ofString "sl") _ (by decide)).trans hlKl,
        (locN_setVar_ne s "level" (ofString "sl") _ (by decide)).trans hlLv,
        wn, by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
          (show ofString "sl" ≠ ofString "node" by decide), hwn], hwnt⟩,
        (locN_setVar_ne s "seg" (ofString "sl") _ (by decide)).trans hlSeg,
        by rw [locN_setVar_same]; exact hsl_eq,
        ⟨wseg, by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
          (show ofString "sl" ≠ ofString "seg" by decide), hwseg], hwsegt⟩,
        ⟨wsl, by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE], hsl_eq⟩⟩)
    ?_
  -- Step 8: `decCall pl := common_prefix_length(seg, sl, key + level, klen - level)`
  refine hoare_decCall_fall (by decide) (localsOnly_mptDeletePost sp0)
    (resume_common_prefix_length h Nd fs sp0 node0 top0 res0 key0 klen0 level0 seg0 sl0 child0)
    ?_
  -- Step 9: `if pl < sl`
  refine hoare_ite_fall
    -- Branch 9A (`pl < sl`): `res := node` (`go` remains `0`)
    (hoare_assign_fall fun s v ⟨hAP, _⟩ hv _ => by
      obtain ⟨⟨hAI, _⟩, _⟩ := hAP
      obtain ⟨hH, hSt, _, _, _, hgo, _, _, hlT, _, _, _, _, wn, hwn, hwnt⟩ := hAI
      have hv_eq : v = .val (.word wn) := by
        simp [evalAt, evalHOLExact, hwn] at hv; exact hv.symm
      subst hv_eq
      set t := setKvarHOLFinite .local (ofString "res") (.val (.word wn)) s
      have hH_t : HeapInv Nd node0 key0 klen0 level0 seg0 sl0 child0 t :=
        (heapInv_with_locals s _ s.clock _ _ _ _ _ _ _ _).2 hH
      have hgo_t : locN t "go" = 0 :=
        (locN_setVar_ne s "go" (ofString "res") _ (by decide)).trans hgo
      have htop_t : locN t "top" = top0 :=
        (locN_setVar_ne s "top" (ofString "res") _ (by decide)).trans hlT
      have hres_t : locN t "res" = node0 := by
        change locN (setVarHOLFinite (ofString "res") (.val (.word wn)) s) "res" = node0
        rw [locN_setVar_same]
        exact hwnt
      refine ⟨⟨hH_t.1, Nd, fs, hH_t.2.1, ?_,
        by rw [hres_t]; exact Or.inr hH_t.2.2.1,
        fun hnz => absurd hgo_t hnz⟩,
        Or.inl hgo_t⟩
      rw [htop_t]
      exact (mptStack_with_locals s _ s.clock Nd fs top0).2 hSt)
    -- Branch 9B (`¬ (pl < sl)`): `decCall fr := scratch_alloc(40)` + frame push
    (hoare_decCall_fall (by decide) (localsOnly_mptDeletePost sp0)
      (resume_scratch_alloc h Nd fs sp0 node0 top0 res0 key0 klen0 level0 seg0 sl0 child0)
      (hoare_framePushProg Nd fs sp0 node0 top0 res0 key0 klen0 level0 seg0 sl0 child0))

end MptDeleteKind2

/-- One iteration with node tag 2; shard 0 includes the null-root case.
Prove the bound and the continuing-state effect. No other kind shard is imported. -/
theorem mptDelete_kind2 (h : MptDeleteCallees) :
    MptStepAt MptDeleteActive MptDeleteHead MptDeleteEffect mptDeleteBody mptDeleteCost 2 := by
  intro F s hc hp hk
  have hb := MptDeleteKind2.mptDeleteBody_bounded h s hc hp.1.1.1
  refine ⟨hb, fun hflow => ?_⟩
  have hnc := evaluate_noTopContinue mptDeleteBody MptDeleteKind2.mptDeleteBody_noTopContinue s
  have hnone : (evaluateHOLFiniteState s mptDeleteBody).1 = none := by
    rcases hflow with hnone | hcont
    · exact hnone
    · exact absurd hcont hnc
  have hnt : (evaluateHOLFiniteState s mptDeleteBody).1 ≠ some .timeOut := by
    rw [hnone]; simp
  exact MptDeleteKind2.mptDelete_kind2_hoare h s hc hp hk hnt hnone


end InitECandidate.Solver.Wave8GuestInv.R10Shards.GbodyMptDelete
