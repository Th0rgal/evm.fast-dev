import InitECandidate.Solver.UniformSourceClock
import InitECandidate.Solver.PanRunBounded
import InitECandidate.Solver.GuestUniformClockBound

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace InitECandidate.Solver.PanRunBoundedExt

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestGlobalKeep
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.GuestUniformClockBound

abbrev StaticEnv := List (MlS × Nat)

def lookupStaticCost : StaticEnv → MlS → Option Nat
  | [], _ => none
  | (name, cost) :: rest, target =>
    if name == target then some cost else lookupStaticCost rest target

def EnvValid : StaticEnv → Prop
  | [] => True
  | (name, cost) :: rest => FunBounded name cost ∧ EnvValid rest

theorem lookupStaticCost_sound {env : StaticEnv} (hvalid : EnvValid env)
    {target : MlS} {cost : Nat} (hlook : lookupStaticCost env target = some cost) :
    FunBounded target cost := by
  induction env with
  | nil => cases hlook
  | cons entry rest ih =>
    rcases entry with ⟨name, c⟩
    rcases hvalid with ⟨hfun, hrest⟩
    simp only [lookupStaticCost] at hlook
    by_cases heq : (name == target) = true
    · rw [if_pos heq] at hlook
      cases hlook
      have hname : name = target := by simpa using heq
      subst hname
      exact hfun
    · rw [if_neg heq] at hlook
      exact ih hrest hlook

def findCountedStep (counter : MlS) : ProgHOL 64 → Option (BitVec 64)
  | .assign .local nm (.op .add [.var .local src, .const s]) =>
    if (nm == counter) && (src == counter) then some s else none
  | .dec _ _ _ b => findCountedStep counter b
  | .seq _ t => findCountedStep counter t
  | _ => none

def asAssignLocalConst : ProgHOL 64 → Option (MlS × BitVec 64)
  | .assign .local counter (.const start) => some (counter, start)
  | _ => none

def asWhileCmpConstSeq : ProgHOL 64 → Option (Cmp × MlS × BitVec 64 × ProgHOL 64 × ProgHOL 64)
  | .seq (.while (.cmp op (.var .local counter) (.const K)) lbody) tail =>
    some (op, counter, K, lbody, tail)
  | _ => none

private theorem asAssignLocalConst_eq {p : ProgHOL 64} {counter : MlS} {start : BitVec 64}
    (h : asAssignLocalConst p = some (counter, start)) :
    p = .assign .local counter (.const start) := by
  cases p with
  | assign k nm val =>
    cases k <;> cases val <;> simp [asAssignLocalConst] at h
    rcases h with ⟨rfl, rfl⟩
    rfl
  | _ => simp [asAssignLocalConst] at h

private theorem asWhileCmpConstSeq_eq {p : ProgHOL 64}
    {op : Cmp} {counter : MlS} {K : BitVec 64} {lbody tail : ProgHOL 64}
    (h : asWhileCmpConstSeq p = some (op, counter, K, lbody, tail)) :
    p = .seq (.while (.cmp op (.var .local counter) (.const K)) lbody) tail ∧
      sizeOf lbody < sizeOf p ∧ sizeOf tail < sizeOf p := by
  cases p with
  | seq a b =>
    cases a with
    | «while» cond lb =>
      cases cond with
      | cmp op' e1 e2 =>
        cases e1 with
        | var k nm =>
          cases k <;> cases e2 <;> simp [asWhileCmpConstSeq] at h
          rcases h with ⟨rfl, rfl, rfl, rfl, rfl⟩
          refine ⟨rfl, ?_, ?_⟩
          · simp_wf; omega
          · simp_wf
        | _ => simp [asWhileCmpConstSeq] at h
      | _ => simp [asWhileCmpConstSeq] at h
    | _ => simp [asWhileCmpConstSeq] at h
  | _ => simp [asWhileCmpConstSeq] at h

def specialCallCost (fn : MlS) : List (ExpHOL 64) → Option Nat
  | [_dst, .const K] =>
    if (fn == ofString "memzero") && decide (K.toNat + 32 < 2 ^ 64) then
      some (K.toNat / 8 + 8)
    else if fn == ofString "is_zero_bytes" then
      some (K.toNat + 1)
    else none
  | [_dst, .panop .mul [.const a, .const b]] =>
    if (fn == ofString "memzero") && decide ((a * b).toNat + 32 < 2 ^ 64) then
      some ((a * b).toNat / 8 + 8)
    else none
  | [_dst, _src, .const K] =>
    if ((fn == ofString "memcpy") || (fn == ofString "memeq")) &&
        decide (K.toNat + 32 < 2 ^ 64) then
      some (K.toNat / 8 + 8)
    else none
  | _ => none

theorem specialCallCost_sound (dest : Option (VarKind × MlS)) (fn : MlS)
    (args : List (ExpHOL 64)) {cost : Nat}
    (h : specialCallCost fn args = some cost) :
    ProgBounded (.call (some (dest, none)) fn args) cost := by
  rcases args with _ | ⟨e1, _ | ⟨e2, _ | ⟨e3, _ | _⟩⟩⟩
  · simp [specialCallCost] at h
  · simp [specialCallCost] at h
  · cases e2 with
    | const K =>
      simp only [specialCallCost] at h
      by_cases hm : ((fn == ofString "memzero") && decide (K.toNat + 32 < 2 ^ 64)) = true
      · rw [if_pos hm] at h
        cases h
        have hm' := (Bool.and_eq_true _ _).mp hm
        have hfn : fn = ofString "memzero" := by simpa using hm'.1
        subst hfn
        exact progBounded_memzero_const dest e1 K (of_decide_eq_true hm'.2)
      · rw [if_neg hm] at h
        by_cases hz : (fn == ofString "is_zero_bytes") = true
        · rw [if_pos hz] at h
          cases h
          have hfn : fn = ofString "is_zero_bytes" := by simpa using hz
          subst hfn
          exact progBounded_is_zero_bytes_const dest e1 K
        · rw [if_neg hz] at h; cases h
    | panop op es =>
      cases op with
      | mul =>
        rcases es with _ | ⟨x1, _ | ⟨x2, _ | _⟩⟩
        · simp [specialCallCost] at h
        · simp [specialCallCost] at h
        · cases x1 with
          | const a =>
            cases x2 with
            | const b =>
              simp only [specialCallCost] at h
              by_cases hm : ((fn == ofString "memzero") && decide ((a * b).toNat + 32 < 2 ^ 64)) = true
              · rw [if_pos hm] at h
                cases h
                have hm' := (Bool.and_eq_true _ _).mp hm
                have hfn : fn = ofString "memzero" := by simpa using hm'.1
                subst hfn
                exact progBounded_memzero_mul_const dest e1 a b (of_decide_eq_true hm'.2)
              · rw [if_neg hm] at h; cases h
            | _ => simp [specialCallCost] at h
          | _ => simp [specialCallCost] at h
        · simp [specialCallCost] at h
    | _ => simp [specialCallCost] at h
  · cases e3 with
    | const K =>
      simp only [specialCallCost] at h
      by_cases hm : (((fn == ofString "memcpy") || (fn == ofString "memeq")) &&
          decide (K.toNat + 32 < 2 ^ 64)) = true
      · rw [if_pos hm] at h
        cases h
        have hm' := (Bool.and_eq_true _ _).mp hm
        have hsmall := of_decide_eq_true hm'.2
        rcases (Bool.or_eq_true _ _).mp hm'.1 with hcp | heq
        · have hfn : fn = ofString "memcpy" := by simpa using hcp
          subst hfn
          exact progBounded_memcpy_const dest e1 e2 K hsmall
        · have hfn : fn = ofString "memeq" := by simpa using heq
          subst hfn
          exact progBounded_memeq_const dest e1 e2 K hsmall
      · rw [if_neg hm] at h; cases h
    | _ => simp [specialCallCost] at h
  · simp [specialCallCost] at h

def specialDecCallOverhead (fn : MlS) : List (ExpHOL 64) → Option Nat
  | [_a, _b, .const K] =>
    if (fn == ofString "memeq") && decide (K.toNat + 32 < 2 ^ 64) then
      some (K.toNat / 8 + 8)
    else none
  | [_p, .const K] =>
    if fn == ofString "is_zero_bytes" then
      some (K.toNat + 1)
    else none
  | _ => none

theorem specialDecCallOverhead_sound (name : MlS) (shape : ShapeHOL) (fn : MlS)
    (args : List (ExpHOL 64)) {cont : ProgHOL 64} {ov tCost : Nat}
    (h : specialDecCallOverhead fn args = some ov)
    (hcont : ProgBounded cont tCost) :
    ProgBounded (.decCall name shape fn args cont) (ov + tCost) := by
  rcases args with _ | ⟨e1, _ | ⟨e2, _ | ⟨e3, _ | _⟩⟩⟩
  · simp [specialDecCallOverhead] at h
  · simp [specialDecCallOverhead] at h
  · cases e2 with
    | const K =>
      simp only [specialDecCallOverhead] at h
      by_cases hz : (fn == ofString "is_zero_bytes") = true
      · rw [if_pos hz] at h
        cases h
        have hfn : fn = ofString "is_zero_bytes" := by simpa using hz
        subst hfn
        exact progBounded_is_zero_bytes_decCall_const name shape e1 K hcont
      · rw [if_neg hz] at h; cases h
    | _ => simp [specialDecCallOverhead] at h
  · cases e3 with
    | const K =>
      simp only [specialDecCallOverhead] at h
      by_cases hm : ((fn == ofString "memeq") && decide (K.toNat + 32 < 2 ^ 64)) = true
      · rw [if_pos hm] at h
        cases h
        have hm' := (Bool.and_eq_true _ _).mp hm
        have hfn : fn = ofString "memeq" := by simpa using hm'.1
        subst hfn
        exact progBounded_memeq_decCall_const name shape e1 e2 K (of_decide_eq_true hm'.2) hcont
      · rw [if_neg hm] at h; cases h
    | _ => simp [specialDecCallOverhead] at h
  · simp [specialDecCallOverhead] at h

def asIncrAssign (counter : MlS) (step : BitVec 64) : ProgHOL 64 → Bool
  | .assign .local nm (.op .add [.var .local src, .const s]) =>
    (nm == counter) && (src == counter) && (s == step)
  | _ => false

private theorem asIncrAssign_eq {p : ProgHOL 64} {counter : MlS} {step : BitVec 64}
    (h : asIncrAssign counter step p = true) :
    p = .assign .local counter (.op .add [.var .local counter, .const step]) := by
  cases p with
  | assign k nm val =>
    cases k with
    | global => simp [asIncrAssign] at h
    | «local» =>
      cases val with
      | op bop es =>
        cases bop with
        | add =>
          rcases es with _ | ⟨x1, _ | ⟨x2, _ | _⟩⟩
          · simp [asIncrAssign] at h
          · simp [asIncrAssign] at h
          · cases x1 with
            | var vk src =>
              cases vk with
              | global => simp [asIncrAssign] at h
              | «local» =>
                cases x2 with
                | const s =>
                  simp only [asIncrAssign, Bool.and_eq_true, beq_iff_eq] at h
                  rcases h with ⟨⟨rfl, rfl⟩, rfl⟩
                  rfl
                | _ => simp [asIncrAssign] at h
            | _ => simp [asIncrAssign] at h
          · simp [asIncrAssign] at h
        | _ => simp [asIncrAssign] at h
      | _ => simp [asIncrAssign] at h
  | _ => simp [asIncrAssign] at h

private theorem cmp_less_or_lower_of_beq {op : Cmp}
    (h : ((op == .less) || (op == .lower)) = true) :
    op = .less ∨ op = .lower := by
  cases op <;> simp at h ⊢

def isOneConst : ShapeHOL → ExpHOL 64 → Option (BitVec 64)
  | .one, .const start => some start
  | _, _ => none

private theorem isOneConst_eq {shape : ShapeHOL} {init : ExpHOL 64} {start : BitVec 64}
    (h : isOneConst shape init = some start) :
    shape = .one ∧ init = .const start := by
  cases shape with
  | one =>
    cases init with
    | const start' =>
      simp [isOneConst] at h
      subst h
      exact ⟨rfl, rfl⟩
    | _ => simp [isOneConst] at h
  | _ => simp [isOneConst] at h

mutual

def evalStaticBound (env : StaticEnv) : ProgHOL 64 → Option Nat
  | .skip | .assign _ _ _ | .storeByte _ _ | .store _ _ | .store32 _ _
  | .shMemLoad _ _ _ _ | .shMemStore _ _ _ | .break | .continue | .annot _ _
  | .raise _ _ | .return _ | .primitive _ _ _ | .extCall _ _ _ _ _ => some 0
  | .tick | .while _ _ => none
  | .ite _ yes no =>
    match evalStaticBound env yes, evalStaticBound env no with
    | some a, some b => some (max a b)
    | _, _ => none
  | .dec name shape init body =>
    match isOneConst shape init, hw : asWhileCmpConstSeq body with
    | some start, some (op, counter, K, lbody, tail) =>
      have _hsz := (asWhileCmpConstSeq_eq hw).2
      if (name == counter) && ((op == .less) || (op == .lower)) then
        match findCountedStep counter lbody with
        | some step =>
          if decide (K.toNat + step.toNat < 2 ^ 63) && decide (0 < step.toNat) &&
              decide (start.toNat ≤ K.toNat) then
            match evalCountedBody env counter step lbody, evalStaticBound env tail with
            | some bCost, some tCost => some (K.toNat * (bCost + 1) + tCost)
            | _, _ => evalStaticBound env body
          else evalStaticBound env body
        | none => evalStaticBound env body
      else evalStaticBound env body
    | _, _ => evalStaticBound env body
  | .seq first second =>
    let fallback :=
      match evalStaticBound env first, evalStaticBound env second with
      | some a, some b => some (a + b)
      | _, _ => none
    match asAssignLocalConst first, hw : asWhileCmpConstSeq second with
    | some (counter, start), some (op, counter2, K, lbody, tail) =>
      have _hsz := (asWhileCmpConstSeq_eq hw).2
      if (counter == counter2) && ((op == .less) || (op == .lower)) then
        match findCountedStep counter lbody with
        | some step =>
          if decide (K.toNat + step.toNat < 2 ^ 63) && decide (0 < step.toNat) &&
              decide (start.toNat ≤ K.toNat) then
            match evalCountedBody env counter step lbody, evalStaticBound env tail with
            | some bCost, some tCost => some (K.toNat * (bCost + 1) + tCost)
            | _, _ => fallback
          else fallback
        | none => fallback
      else fallback
    | _, _ => fallback
  | .call info fn args =>
    match info with
    | none =>
      match lookupStaticCost env fn with
      | some c => some (c + 1)
      | none => none
    | some (_dest, none) =>
      match specialCallCost fn args with
      | some sc => some sc
      | none =>
        match lookupStaticCost env fn with
        | some c => some (c + 1)
        | none => none
    | some (_dest, some (_hid, _hvar, handler)) =>
      match lookupStaticCost env fn, evalStaticBound env handler with
      | some c, some h => some (c + 1 + h)
      | _, _ => none
  | .decCall _ _ fn args cont =>
    match specialDecCallOverhead fn args with
    | some ov =>
      match evalStaticBound env cont with
      | some t => some (ov + t)
      | none => none
    | none =>
      match lookupStaticCost env fn, evalStaticBound env cont with
      | some c, some t => some (c + 1 + t)
      | _, _ => none
termination_by p => sizeOf p
decreasing_by
  all_goals
    simp_wf
    try simp only [Option.sizeOf_spec, Prod.sizeOf_spec]
    try omega

def evalCountedBody (env : StaticEnv) (counter : MlS) (step : BitVec 64) : ProgHOL 64 → Option Nat
  | .dec name _ _ body =>
    if !(counter == name) then evalCountedBody env counter step body else none
  | .seq first tail =>
    if avoidsLocal counter first && noTopContinue first then
      match evalStaticBound env first, evalCountedBody env counter step tail with
      | some a, some b => some (a + b)
      | _, _ => none
    else none
  | p =>
    if asIncrAssign counter step p then some 0 else none
termination_by p => sizeOf p
decreasing_by
  all_goals
    simp_wf
    try omega

end

mutual

theorem evalStaticBound_sound {env : StaticEnv} (hvalid : EnvValid env) :
    (p : ProgHOL 64) → (cost : Nat) → evalStaticBound env p = some cost →
    ProgBounded p cost
  | .skip, cost, h => by rw [evalStaticBound.eq_def] at h; cases h; exact ProgBounded.straight _ rfl
  | .assign _ _ _, cost, h => by rw [evalStaticBound.eq_def] at h; cases h; exact ProgBounded.straight _ rfl
  | .storeByte _ _, cost, h => by rw [evalStaticBound.eq_def] at h; cases h; exact ProgBounded.straight _ rfl
  | .store _ _, cost, h => by rw [evalStaticBound.eq_def] at h; cases h; exact ProgBounded.straight _ rfl
  | .store32 _ _, cost, h => by rw [evalStaticBound.eq_def] at h; cases h; exact ProgBounded.straight _ rfl
  | .shMemLoad _ _ _ _, cost, h => by rw [evalStaticBound.eq_def] at h; cases h; exact ProgBounded.straight _ rfl
  | .shMemStore _ _ _, cost, h => by rw [evalStaticBound.eq_def] at h; cases h; exact ProgBounded.straight _ rfl
  | .break, cost, h => by rw [evalStaticBound.eq_def] at h; cases h; exact ProgBounded.straight _ rfl
  | .continue, cost, h => by rw [evalStaticBound.eq_def] at h; cases h; exact ProgBounded.straight _ rfl
  | .annot _ _, cost, h => by rw [evalStaticBound.eq_def] at h; cases h; exact ProgBounded.straight _ rfl
  | .raise _ _, cost, h => by rw [evalStaticBound.eq_def] at h; cases h; exact ProgBounded.straight _ rfl
  | .return _, cost, h => by rw [evalStaticBound.eq_def] at h; cases h; exact ProgBounded.straight _ rfl
  | .primitive _ _ _, cost, h => by rw [evalStaticBound.eq_def] at h; cases h; exact ProgBounded.straight _ rfl
  | .extCall _ _ _ _ _, cost, h => by rw [evalStaticBound.eq_def] at h; cases h; exact ProgBounded.straight _ rfl
  | .tick, _, h => by rw [evalStaticBound.eq_def] at h; cases h
  | .while _ _, _, h => by rw [evalStaticBound.eq_def] at h; cases h
  | .ite cond yes no, cost, h => by
    rw [evalStaticBound.eq_def] at h
    dsimp only at h
    rcases hy : evalStaticBound env yes with _ | a <;>
      rcases hn : evalStaticBound env no with _ | b <;>
      rw [hy, hn] at h <;> cases h
    exact ProgBounded.iteMax cond (evalStaticBound_sound hvalid yes a hy)
      (evalStaticBound_sound hvalid no b hn)
  | .dec name shape init body, cost, h => by
    rw [evalStaticBound.eq_def] at h
    dsimp only at h
    rcases h1 : isOneConst shape init with _ | start
    · rw [h1] at h
      exact ProgBounded.dec name shape init (evalStaticBound_sound hvalid body cost h)
    · rcases h2 : asWhileCmpConstSeq body with _ | ⟨op, counter, K, lbody, tail⟩
      · rw [h1, h2] at h
        exact ProgBounded.dec name shape init (evalStaticBound_sound hvalid body cost h)
      · rw [h1, h2] at h
        dsimp only at h
        by_cases hcond : ((name == counter) && ((op == .less) || (op == .lower))) = true
        · rw [if_pos hcond] at h
          rcases hstep : findCountedStep counter lbody with _ | step
          · rw [hstep] at h
            exact ProgBounded.dec name shape init (evalStaticBound_sound hvalid body cost h)
          · rw [hstep] at h
            dsimp only at h
            by_cases hbounds : (decide (K.toNat + step.toNat < 2 ^ 63) && decide (0 < step.toNat) &&
                decide (start.toNat ≤ K.toNat)) = true
            · rw [if_pos hbounds] at h
              rcases hb : evalCountedBody env counter step lbody with _ | bCost
              · rw [hb] at h
                exact ProgBounded.dec name shape init (evalStaticBound_sound hvalid body cost h)
              · rcases ht : evalStaticBound env tail with _ | tCost
                · rw [hb, ht] at h
                  exact ProgBounded.dec name shape init (evalStaticBound_sound hvalid body cost h)
                · rw [hb, ht] at h
                  cases h
                  have ⟨hsh_eq, hinit_eq⟩ := isOneConst_eq h1
                  have ⟨hbody_eq, _hsz_lb, _hsz_tl⟩ := asWhileCmpConstSeq_eq h2
                  have hcond' := (Bool.and_eq_true _ _).mp hcond
                  have hnc : name = counter := by simpa using hcond'.1
                  subst hnc
                  have hop := cmp_less_or_lower_of_beq hcond'.2
                  have hb12 := (Bool.and_eq_true _ _).mp hbounds
                  have hb1 := (Bool.and_eq_true _ _).mp hb12.1
                  have hcb := evalCountedBody_sound hvalid name step lbody bCost hb
                  have htb : ProgBounded tail tCost := evalStaticBound_sound hvalid tail tCost ht
                  rw [hsh_eq, hinit_eq, hbody_eq]
                  exact ProgBounded.countedDec name op hop K step start
                    (of_decide_eq_true hb1.1) (of_decide_eq_true hb1.2) (of_decide_eq_true hb12.2)
                    hcb htb
            · rw [if_neg hbounds] at h
              exact ProgBounded.dec name shape init (evalStaticBound_sound hvalid body cost h)
        · rw [if_neg hcond] at h
          exact ProgBounded.dec name shape init (evalStaticBound_sound hvalid body cost h)
  | .seq first second, cost, h => by
    rw [evalStaticBound.eq_def] at h
    dsimp only at h
    have hfb : (match evalStaticBound env first, evalStaticBound env second with
        | some a, some b => some (a + b)
        | _, _ => none) = some cost → ProgBounded (.seq first second) cost := by
      intro hc
      rcases hf : evalStaticBound env first with _ | a <;>
        rcases hs : evalStaticBound env second with _ | b <;>
        rw [hf, hs] at hc <;> cases hc
      exact ProgBounded.seq (evalStaticBound_sound hvalid first a hf)
        (evalStaticBound_sound hvalid second b hs)
    rcases h1 : asAssignLocalConst first with _ | ⟨counter, start⟩
    · rw [h1] at h
      exact hfb h
    · rcases h2 : asWhileCmpConstSeq second with _ | ⟨op, counter2, K, lbody, tail⟩
      · rw [h1, h2] at h
        exact hfb h
      · rw [h1, h2] at h
        dsimp only at h
        by_cases hcond : ((counter == counter2) && ((op == .less) || (op == .lower))) = true
        · rw [if_pos hcond] at h
          rcases hstep : findCountedStep counter lbody with _ | step
          · rw [hstep] at h
            exact hfb h
          · rw [hstep] at h
            dsimp only at h
            by_cases hbounds : (decide (K.toNat + step.toNat < 2 ^ 63) && decide (0 < step.toNat) &&
                decide (start.toNat ≤ K.toNat)) = true
            · rw [if_pos hbounds] at h
              rcases hb : evalCountedBody env counter step lbody with _ | bCost
              · rw [hb] at h
                exact hfb h
              · rcases ht : evalStaticBound env tail with _ | tCost
                · rw [hb, ht] at h
                  exact hfb h
                · rw [hb, ht] at h
                  cases h
                  have hfirst_eq := asAssignLocalConst_eq h1
                  have ⟨hsec_eq, _hsz_lb, _hsz_tl⟩ := asWhileCmpConstSeq_eq h2
                  have hcond' := (Bool.and_eq_true _ _).mp hcond
                  have hcc : counter = counter2 := by simpa using hcond'.1
                  subst hcc
                  have hop := cmp_less_or_lower_of_beq hcond'.2
                  have hb12 := (Bool.and_eq_true _ _).mp hbounds
                  have hb1 := (Bool.and_eq_true _ _).mp hb12.1
                  have hcb := evalCountedBody_sound hvalid counter step lbody bCost hb
                  have htb : ProgBounded tail tCost := evalStaticBound_sound hvalid tail tCost ht
                  rw [hfirst_eq, hsec_eq]
                  exact ProgBounded.countedAssign counter op hop K step start
                    (of_decide_eq_true hb1.1) (of_decide_eq_true hb1.2) (of_decide_eq_true hb12.2)
                    hcb htb
            · rw [if_neg hbounds] at h
              exact hfb h
        · rw [if_neg hcond] at h
          exact hfb h
  | .call none fn args, cost, h => by
    rw [evalStaticBound.eq_def] at h
    dsimp only at h
    rcases hl : lookupStaticCost env fn with _ | c <;> rw [hl] at h <;> cases h
    exact ProgBounded.tail (lookupStaticCost_sound hvalid hl) args
  | .call (some (dest, none)) fn args, cost, h => by
    rw [evalStaticBound.eq_def] at h
    dsimp only at h
    rcases hs : specialCallCost fn args with _ | sc
    · rw [hs] at h
      rcases hl : lookupStaticCost env fn with _ | c <;> rw [hl] at h <;> cases h
      exact ProgBounded.call (lookupStaticCost_sound hvalid hl) dest args
    · rw [hs] at h
      cases h
      exact specialCallCost_sound dest fn args hs
  | .call (some (dest, some (hid, hvar, handler))) fn args, cost, h => by
    rw [evalStaticBound.eq_def] at h
    dsimp only at h
    rcases hl : lookupStaticCost env fn with _ | c <;>
      rcases hh : evalStaticBound env handler with _ | hc <;>
      rw [hl, hh] at h <;> cases h
    exact ProgBounded.handledCall (lookupStaticCost_sound hvalid hl) hid hvar dest args
      (evalStaticBound_sound hvalid handler hc hh)
  | .decCall name shape fn args cont, cost, h => by
    rw [evalStaticBound.eq_def] at h
    dsimp only at h
    rcases hs : specialDecCallOverhead fn args with _ | ov
    · rw [hs] at h
      rcases hl : lookupStaticCost env fn with _ | c <;>
        rcases ht : evalStaticBound env cont with _ | t <;>
        rw [hl, ht] at h <;> cases h
      exact ProgBounded.decCall (lookupStaticCost_sound hvalid hl) name shape args
        (evalStaticBound_sound hvalid cont t ht)
    · rw [hs] at h
      rcases ht : evalStaticBound env cont with _ | t <;> rw [ht] at h <;> cases h
      exact specialDecCallOverhead_sound name shape fn args hs
        (evalStaticBound_sound hvalid cont t ht)
termination_by p _ _ => sizeOf p
decreasing_by
  all_goals
    simp_wf
    try simp only [Option.sizeOf_spec, Prod.sizeOf_spec]
    try omega

theorem evalCountedBody_sound {env : StaticEnv} (hvalid : EnvValid env)
    (counter : MlS) (step : BitVec 64) :
    (p : ProgHOL 64) → (cost : Nat) → evalCountedBody env counter step p = some cost →
    CountedBody counter step p cost
  | .dec name shape init body, cost, h => by
    rw [evalCountedBody.eq_def] at h
    change (if (!(counter == name)) = true then evalCountedBody env counter step body else none) = some cost at h
    by_cases hne : (!(counter == name)) = true
    · rw [if_pos hne] at h
      have hne' : counter ≠ name := by
        intro heq; subst heq; simp at hne
      exact CountedBody.dec name shape init hne'
        (evalCountedBody_sound hvalid counter step body cost h)
    · rw [if_neg hne] at h; cases h
  | .seq first tail, cost, h => by
    rw [evalCountedBody.eq_def] at h
    change (if (avoidsLocal counter first && noTopContinue first) = true then
        match evalStaticBound env first, evalCountedBody env counter step tail with
        | some a, some b => some (a + b)
        | _, _ => none
      else none) = some cost at h
    by_cases hcond : (avoidsLocal counter first && noTopContinue first) = true
    · rw [if_pos hcond] at h
      rcases hf : evalStaticBound env first with _ | a <;>
        rcases ht : evalCountedBody env counter step tail with _ | b <;>
        rw [hf, ht] at h <;> cases h
      have hc := (Bool.and_eq_true _ _).mp hcond
      exact CountedBody.seq first (evalStaticBound_sound hvalid first a hf) hc.1 hc.2
        (evalCountedBody_sound hvalid counter step tail b ht)
    · rw [if_neg hcond] at h; cases h
  | .assign kind name val, cost, h => by
    rw [evalCountedBody.eq_def] at h
    change (if asIncrAssign counter step (.assign kind name val) = true then some 0 else none) = some cost at h
    by_cases hinc : asIncrAssign counter step (.assign kind name val) = true
    · rw [if_pos hinc] at h
      cases h
      rw [asIncrAssign_eq hinc]
      exact CountedBody.incr
    · rw [if_neg hinc] at h; cases h
  | .skip, _, h | .storeByte _ _, _, h | .store _ _, _, h | .store32 _ _, _, h
  | .shMemLoad _ _ _ _, _, h | .shMemStore _ _ _, _, h | .break, _, h | .continue, _, h
  | .annot _ _, _, h | .raise _ _, _, h | .return _, _, h | .primitive _ _ _, _, h
  | .extCall _ _ _ _ _, _, h | .tick, _, h | .while _ _, _, h | .ite _ _ _, _, h
  | .call _ _ _, _, h | .decCall _ _ _ _ _, _, h => by
    rw [evalCountedBody.eq_def] at h
    cases h
termination_by p _ _ => sizeOf p
decreasing_by
  all_goals
    simp_wf
    try omega

end

theorem funBounded_of_staticChecker
    {env : StaticEnv} (hvalid : EnvValid env)
    (i : Nat) (hi : i < Guest.Software.guestAst.length)
    (d : Decl (BitVec 64)) (cost : Nat)
    (hd : Guest.Software.guestAst[i] = .function (extractFn d))
    (hcheck : evalStaticBound env
      (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural (extractFn d).body) = some cost) :
    FunBounded (ofString (extractFn d).name) cost :=
  funBounded_of_guestAst i hi d cost hd (evalStaticBound_sound hvalid _ cost hcheck)

end InitECandidate.Solver.PanRunBoundedExt
