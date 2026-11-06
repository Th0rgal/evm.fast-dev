import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.StateAccountOps
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers.CalldataloadSpecs

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.GuestGlobalKeep
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R11Shards
open InitECandidate.Solver.Wave8GuestInv.R11Shards.OpDispatchSpec
open InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA
open InitECandidate.Solver.Wave8GuestInv.R16Shards (evmInvAt_of_htab_step evaluate_be_eq)
open InitECandidate.Solver.Wave8GuestInv.R16Shards.StateRestoreEpilogue (noCatchableRaise evaluate_noCatchableRaise)
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers
open InitECandidate.Solver.Wave8Contracts.M23

namespace Group10

def ChainLinks (m : Nat → Nat) : List Ivl → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => m (b.1 + 24) + m (b.1 + 40) = m (a.2 + 56) ∧ ChainLinks m (b :: rest)

def HeadMemChainWF {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  (∀ ec ∈ evmChain s, memW s (ec.1 + 32) % 32 = 0 ∧ memW s (ec.1 + 40) % 8 = 0) ∧
  memW s (globN s "ev" + 24) + memW s (globN s "ev" + 40) = globN s "frame_mem_ptr" ∧
  ChainLinks (memW s) (evmChain s)

def HeadMemAligned {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  memW s (globN s "ev" + 32) % 32 = 0 ∧
  memW s (globN s "ev" + 24) + memW s (globN s "ev" + 40) = globN s "frame_mem_ptr"

def ExtendMemoryPre {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ ebw : BitVec 64, s.locals.lookup (ofString "expand_by") = some (.val (.word ebw)) ∧
    (ebw = 0#64 ∨ (memW s (globN s "ev" + 32) + ebw.toNat < 2 ^ 37 ∧
      (memW s (globN s "ev" + 32) + ebw.toNat) % 32 = 0 ∧
      memW s (globN s "ev" + 24) + memW s (globN s "ev" + 40) = globN s "frame_mem_ptr"))

theorem headMemChainWF_headMemAligned {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : HeadMemChainWF s) : HeadMemAligned s := by
  have hhead : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by
    simp [evmChain, evmChainFrom]
  exact ⟨(h.1 _ hhead).1, h.2.1⟩

theorem headMemChainWF_congr {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (hm : t.memory = s.memory) (hg : t.globals = s.globals) :
    HeadMemChainWF t ↔ HeadMemChainWF s := by
  unfold HeadMemChainWF
  rw [evmChain_congr hm hg, memW_congr hm, globN_congr hg]

theorem headMemChainWF_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) (h : HeadMemChainWF s) :
    HeadMemChainWF { s with locals := locals, clock := k } :=
  (headMemChainWF_congr (s := s) (t := { s with locals := locals, clock := k }) rfl rfl).2 h

theorem chainLinks_transport (m n : Nat → Nat) (xs : List Ivl)
    (hmem : ∀ ec ∈ xs, n (ec.1 + 24) = m (ec.1 + 24) ∧
      n (ec.1 + 40) = m (ec.1 + 40) ∧ n (ec.2 + 56) = m (ec.2 + 56))
    (h : ChainLinks m xs) : ChainLinks n xs := by
  induction xs with
  | nil => trivial
  | cons a xs ih =>
    cases xs with
    | nil => trivial
    | cons b rest =>
      refine ⟨?_, ih (fun ec hec => hmem ec (List.mem_cons_of_mem _ hec)) h.2⟩
      rw [(hmem b (by simp)).1, (hmem b (by simp)).2.1,
        (hmem a List.mem_cons_self).2.2]
      exact h.1

theorem headMemChainWF_of_agree {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hs : HeadMemChainWF s)
    (hchain : evmChain post = evmChain s)
    (hmem : ∀ ec ∈ evmChain s, memW post (ec.1 + 24) = memW s (ec.1 + 24) ∧
      memW post (ec.1 + 32) = memW s (ec.1 + 32) ∧
      memW post (ec.1 + 40) = memW s (ec.1 + 40) ∧
      memW post (ec.2 + 56) = memW s (ec.2 + 56))
    (hev : globN post "ev" = globN s "ev")
    (hfmp : globN post "frame_mem_ptr" = globN s "frame_mem_ptr") :
    HeadMemChainWF post := by
  obtain ⟨hal, hhd, hlk⟩ := hs
  refine ⟨?_, ?_, ?_⟩
  · intro ec hec
    rw [hchain] at hec
    have hm := hmem ec hec
    rw [hm.2.1, hm.2.2.1]
    exact hal ec hec
  · have hh : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by
      simp [evmChain, evmChainFrom]
    have hm := hmem _ hh
    rw [hev, hm.1, hm.2.2.1, hfmp]
    exact hhd
  · rw [hchain]
    exact chainLinks_transport (memW s) (memW post) _
      (fun ec hec => ⟨(hmem ec hec).1, (hmem ec hec).2.2.1,
        (hmem ec hec).2.2.2⟩) hlk

theorem headMemChainWF_extend {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hs : HeadMemChainWF s)
    (hchain : evmChain post = evmChain s)
    (hk : ∀ ec ∈ (evmChain s).tail,
      memW post (ec.1 + 24) = memW s (ec.1 + 24) ∧
      memW post (ec.1 + 32) = memW s (ec.1 + 32) ∧
      memW post (ec.1 + 40) = memW s (ec.1 + 40))
    (hc : ∀ ec ∈ evmChain s, memW post (ec.2 + 56) = memW s (ec.2 + 56))
    (hev : globN post "ev" = globN s "ev")
    (hmem0 : memW post (globN s "ev" + 24) = memW s (globN s "ev" + 24))
    (hlen0 : memW post (globN s "ev" + 32) % 32 = 0)
    (hcap0 : memW post (globN s "ev" + 40) % 8 = 0)
    (hfmp : memW s (globN s "ev" + 24) + memW post (globN s "ev" + 40) =
      globN post "frame_mem_ptr") :
    HeadMemChainWF post := by
  obtain ⟨hal, _, hlk⟩ := hs
  obtain ⟨tl, hcs⟩ : ∃ tl, evmChain s = (globN s "ev", globN s "cur_cont") :: tl :=
    ⟨_, rfl⟩
  rw [hcs] at hal hlk hk hc
  rw [List.tail_cons] at hk
  refine ⟨?_, ?_, ?_⟩
  · intro ec hec
    rw [hchain, hcs] at hec
    rcases List.mem_cons.mp hec with rfl | hec'
    · exact ⟨hlen0, hcap0⟩
    · have hm := hk ec hec'
      rw [hm.2.1, hm.2.2]
      exact hal ec (List.mem_cons_of_mem _ hec')
  · rw [hev, hmem0]
    exact hfmp
  · rw [hchain, hcs]
    cases tl with
    | nil => trivial
    | cons b rest =>
      have hb := hk b List.mem_cons_self
      refine ⟨?_, chainLinks_transport (memW s) (memW post) _ (fun ec hec => ?_) hlk.2⟩
      · rw [hb.1, hb.2.2, hc _ List.mem_cons_self]
        exact hlk.1
      · have hm := hk ec hec
        exact ⟨hm.1, hm.2.2, hc ec (List.mem_cons_of_mem _ hec)⟩

theorem extendMemoryPre_of_headMemAligned {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : HeadMemAligned s) (ebw : BitVec 64)
    (hl : s.locals.lookup (ofString "expand_by") = some (.val (.word ebw)))
    (hb : memW s (globN s "ev" + 32) + ebw.toNat < 2 ^ 37)
    (h32 : (memW s (globN s "ev" + 32) + ebw.toNat) % 32 = 0) :
    ExtendMemoryPre s :=
  ⟨ebw, hl, Or.inr ⟨hb, h32, h.2⟩⟩

theorem lookup_ceil32 :
    originalRuntimeCode.lookup (ofString "ceil32") =
      some ([(ofString "v", .one)], sourceFnBody Guest.Software.guestFn_ceil32, .one) :=
  lookup_of_guestAst_getElem 442 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_ceil32) rfl

theorem lookup_mul64x64 :
    originalRuntimeCode.lookup (ofString "mul64x64") =
      some ([(ofString "a", .one), (ofString "b", .one)],
        sourceFnBody Guest.Software.guestFn_mul64x64, .comb [.one, .one]) :=
  lookup_of_guestAst_getElem 59 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_mul64x64) rfl

theorem lookup_memory_gas_cost :
    originalRuntimeCode.lookup (ofString "memory_gas_cost") =
      some ([(ofString "size", .one)], sourceFnBody Guest.Software.guestFn_memory_gas_cost, .one) :=
  lookup_of_guestAst_getElem 457 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_memory_gas_cost) rfl

theorem lookup_extend_memory_cost1 :
    originalRuntimeCode.lookup (ofString "extend_memory_cost1") =
      some ([(ofString "start", .comb [.one, .one, .one, .one]),
             (ofString "size", .comb [.one, .one, .one, .one])],
        sourceFnBody Guest.Software.guestFn_extend_memory_cost1, .comb [.one, .one]) :=
  lookup_of_guestAst_getElem 458 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_extend_memory_cost1) rfl

theorem lookup_extend_memory :
    originalRuntimeCode.lookup (ofString "extend_memory") =
      some ([(ofString "expand_by", .one)],
        sourceFnBody Guest.Software.guestFn_extend_memory, .one) :=
  lookup_of_guestAst_getElem 460 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_extend_memory) rfl

private theorem add_sat_body_exact {F : Type} (s : PanSemStateFiniteExact 64 F) {aw bw : BitVec 64}
    (ha : s.locals.lookup (ofString "a") = some (.val (.word aw)))
    (hb : s.locals.lookup (ofString "b") = some (.val (.word bw)))
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_add_sat)).1 =
      some (.returned v)) :
    ∃ rw : BitVec 64, v = .val (.word rw) ∧
      rw.toNat = if aw.toNat + bw.toNat < 2 ^ 64 then aw.toNat + bw.toNat else 2 ^ 64 - 1 := by
  have hbody : sourceFnBody Guest.Software.guestFn_add_sat =
      .dec (ofString "s") .one (.op .add [.var .local (ofString "a"), .var .local (ofString "b")])
        (.seq
          (.ite (.cmp .lower (.var .local (ofString "s")) (.var .local (ofString "a")))
            (.return (.const 18446744073709551615#64))
            .skip)
          (.return (.var .local (ofString "s")))) := rfl
  rw [hbody, evaluateHOLFiniteState_dec_total] at hret; dsimp only at hret
  have hsum : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x))
      (.op .add [.var .local (ofString "a"), .var .local (ofString "b")]) =
      some (.val (.word (aw + bw))) := by
    simp [evalHOLExact, evalListHOLExact, ha, hb, wordOpHOL, wordOp, valueIsWord, valueWord]
  rw [hsum] at hret; dsimp only at hret
  have hsh : shapeEqHOL .one (shapeOfHOLExact (.val (.word (aw + bw)))) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  rw [if_pos hsh] at hret; dsimp only at hret
  set s1 := setVarHOLFinite (ofString "s") (.val (.word (aw + bw))) s
  have hs1_s : s1.locals.lookup (ofString "s") = some (.val (.word (aw + bw))) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs1_a : s1.locals.lookup (ofString "a") = some (.val (.word aw)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ha,
      show ofString "s" ≠ ofString "a" by decide]
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hret
  have hcmp : @evalHOLExact 64 F _ s1.toExact (fun x => Classical.propDecidable (s1.memaddrs x))
      (.cmp .lower (.var .local (ofString "s")) (.var .local (ofString "a"))) =
      some (.val (.word (if (aw + bw) < aw then 1 else 0))) := by
    simp [evalHOLExact, hs1_s, hs1_a, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  rw [hcmp] at hret; dsimp only at hret
  have haw_lt := aw.isLt
  have hbw_lt := bw.isLt
  by_cases hlt : (aw + bw) < aw
  · have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
    simp only [hlt, ↓reduceIte, h10] at hret
    rw [evaluateHOLFiniteState_return] at hret; dsimp only [evalHOLExact] at hret
    have hsz : sizeOfShapeWithContextHOL s1.structs
        (shapeOfHOLExact (.val (.word 18446744073709551615#64))) ≤ 32 := by
      simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
    rw [if_pos hsz] at hret; dsimp only at hret
    injection hret with h1; injection h1 with hv
    refine ⟨18446744073709551615#64, hv.symm, ?_⟩
    rw [BitVec.lt_def, BitVec.toNat_add] at hlt
    have hover : ¬ (aw.toNat + bw.toNat < 2 ^ 64) := by
      intro hok; rw [Nat.mod_eq_of_lt hok] at hlt; omega
    rw [if_neg hover]; decide
  · simp only [hlt, ↓reduceIte, evaluateHOLFiniteState_skip] at hret
    rw [evaluateHOLFiniteState_return] at hret
    have hev_s : @evalHOLExact 64 F _ s1.toExact (fun x => Classical.propDecidable (s1.memaddrs x))
        (.var .local (ofString "s")) = some (.val (.word (aw + bw))) := hs1_s
    rw [hev_s] at hret; dsimp only at hret
    split at hret
    · injection hret with h1; injection h1 with hv
      refine ⟨aw + bw, hv.symm, ?_⟩
      rw [BitVec.lt_def, BitVec.toNat_add] at hlt
      have hok : aw.toNat + bw.toNat < 2 ^ 64 := by
        by_contra hover
        have hmod : (aw.toNat + bw.toNat) % 2 ^ 64 = aw.toNat + bw.toNat - 2 ^ 64 := by omega
        omega
      rw [if_pos hok, BitVec.toNat_add, Nat.mod_eq_of_lt hok]
    · simp at hret

/-- Saturating addition preserves a positive left operand, including overflow. -/
theorem add_sat_return_positive_g10 {F : Type} (s : PanSemStateFiniteExact 64 F)
    {aw bw : BitVec 64}
    (ha : s.locals.lookup (ofString "a") = some (.val (.word aw)))
    (hb : s.locals.lookup (ofString "b") = some (.val (.word bw)))
    (hpos : 0 < aw.toNat) (v : ValueHOL 64)
    (hr : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_add_sat)).1 =
      some (.returned v)) :
    ∃ rw : BitVec 64, v = .val (.word rw) ∧ 0 < rw.toNat := by
  obtain ⟨rw, hv, hn⟩ := add_sat_body_exact s ha hb v hr
  refine ⟨rw, hv, ?_⟩
  rw [hn]
  split <;> omega

private theorem ceil32_body_exact {F : Type} (s : PanSemStateFiniteExact 64 F) {vw : BitVec 64}
    (hcode : s.code = originalRuntimeCode)
    (hv_lk : s.locals.lookup (ofString "v") = some (.val (.word vw)))
    (ret : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_ceil32)).1 =
      some (.returned ret)) :
    ∃ cw : BitVec 64, ret = .val (.word cw) ∧
      (vw.toNat ≤ 2 ^ 64 - 32 →
        cw.toNat = ((vw.toNat + 31) / 32) * 32 ∧ vw.toNat ≤ cw.toNat ∧
        cw.toNat ≤ 2 ^ 64 - 32 ∧ cw.toNat % 32 = 0 ∧ (vw.toNat % 32 = 0 → cw.toNat = vw.toNat)) ∧
      (2 ^ 64 - 31 ≤ vw.toNat → cw.toNat = 2 ^ 64 - 1) := by
  have hbody : sourceFnBody Guest.Software.guestFn_ceil32 =
      .dec (ofString "r") .one (.op .and [.var .local (ofString "v"), .const 31#64])
        (.seq
          (.ite (.cmp .equal (.var .local (ofString "r")) (.const 0#64))
            (.return (.var .local (ofString "v")))
            .skip)
          (.decCall (ofString "s") .one (ofString "add_sat")
            [.var .local (ofString "v"), .op .sub [.const 32#64, .var .local (ofString "r")]]
            (.return (.var .local (ofString "s"))))) := rfl
  rw [hbody, evaluateHOLFiniteState_dec_total] at hret; dsimp only at hret
  have hand : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x))
      (.op .and [.var .local (ofString "v"), .const 31#64]) =
      some (.val (.word (vw &&& 31#64))) := by
    simp [evalHOLExact, evalListHOLExact, hv_lk, wordOpHOL, wordOp, valueIsWord, valueWord]
  rw [hand] at hret; dsimp only at hret
  have hsh_r : shapeEqHOL .one (shapeOfHOLExact (.val (.word (vw &&& 31#64)))) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  rw [if_pos hsh_r] at hret; dsimp only at hret
  set rw := vw &&& 31#64
  have hrw_nat : rw.toNat = vw.toNat % 32 := by
    change (vw &&& 31#64).toNat = vw.toNat % 32
    rw [BitVec.toNat_and, show (31#64 : BitVec 64).toNat = 2 ^ 5 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  set s1 := setVarHOLFinite (ofString "r") (.val (.word rw)) s
  have hs1_r : s1.locals.lookup (ofString "r") = some (.val (.word rw)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs1_v : s1.locals.lookup (ofString "v") = some (.val (.word vw)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hv_lk,
      show ofString "r" ≠ ofString "v" by decide]
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hret
  have hcmp : @evalHOLExact 64 F _ s1.toExact (fun x => Classical.propDecidable (s1.memaddrs x))
      (.cmp .equal (.var .local (ofString "r")) (.const 0#64)) =
      some (.val (.word (if rw = 0#64 then 1 else 0))) := by
    simp [evalHOLExact, hs1_r, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  rw [hcmp] at hret; dsimp only at hret
  have hvw_lt := vw.isLt
  by_cases hr0 : rw = 0#64
  · have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
    simp only [hr0, ↓reduceIte, h10] at hret
    rw [evaluateHOLFiniteState_return] at hret
    have hev_v : @evalHOLExact 64 F _ s1.toExact (fun x => Classical.propDecidable (s1.memaddrs x))
        (.var .local (ofString "v")) = some (.val (.word vw)) := hs1_v
    rw [hev_v] at hret; dsimp only at hret
    have hsz : sizeOfShapeWithContextHOL s1.structs
        (shapeOfHOLExact (.val (.word vw))) ≤ 32 := by
      simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
    rw [if_pos hsz] at hret; dsimp only at hret
    injection hret with h1; injection h1 with hv
    have hmod0 : vw.toNat % 32 = 0 := by rw [← hrw_nat, hr0]; rfl
    refine ⟨vw, hv.symm, ?_, ?_⟩
    · intro hle; exact ⟨by omega, le_rfl, hle, hmod0, fun _ => rfl⟩
    · intro hge; omega
  · simp only [hr0, ↓reduceIte, evaluateHOLFiniteState_skip] at hret
    have hmod_pos : 0 < vw.toNat % 32 := by
      rw [← hrw_nat]
      by_contra hz
      apply hr0
      apply BitVec.eq_of_toNat_eq
      change rw.toNat = 0; omega
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hret
    have hargs : evalListHOLFinite s1 (h := fun x => Classical.propDecidable (s1.memaddrs x))
        [.var .local (ofString "v"), .op .sub [.const 32#64, .var .local (ofString "r")]] =
        some [.val (.word vw), .val (.word (32#64 - rw))] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hs1_v, hs1_r, wordOpHOL, wordOp, valueIsWord, valueWord]
    rw [hargs] at hret; dsimp only at hret
    have hlk := pan_two_word_lookup s1.code.lookup (ofString "add_sat") (ofString "a") (ofString "b")
      (sourceFnBody Guest.Software.guestFn_add_sat) vw (32#64 - rw) (by decide)
      (by change s.code.lookup _ = _; rw [hcode]; exact lookup_add_sat)
    rw [hlk] at hret; dsimp only at hret
    split at hret
    · simp at hret
    · let cal := (HolFiniteMapExact.empty.update (ofString "a", ValueHOL.val (.word vw))).update
        (ofString "b", ValueHOL.val (.word (32#64 - rw)))
      rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s1 cal)
          (sourceFnBody Guest.Software.guestFn_add_sat) with ⟨rb, pb⟩
      rw [hrun] at hret
      rcases rb with _ | rb
      · simp at hret
      · cases rb with
        | returned vb =>
          dsimp only at hret
          split at hret
          · dsimp only at hret
            have ha_lk : (callEntryStateHOLFinite s1 cal).locals.lookup (ofString "a") = some (.val (.word vw)) := by
              have hne : ofString "b" ≠ ofString "a" := by decide
              simp [cal, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne]
            have hb_lk : (callEntryStateHOLFinite s1 cal).locals.lookup (ofString "b") = some (.val (.word (32#64 - rw))) := by
              simp [cal, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
            obtain ⟨sw, rfl, hsw_nat⟩ := add_sat_body_exact (callEntryStateHOLFinite s1 cal) ha_lk hb_lk vb
              (by rw [hrun])
            set cs := setVarHOLFinite (ofString "s") (.val (.word sw)) { pb with locals := s1.locals }
            rw [evaluateHOLFiniteState_return] at hret
            have hev_s : @evalHOLExact 64 F _ cs.toExact (fun x => Classical.propDecidable (cs.memaddrs x))
                (.var .local (ofString "s")) = some (.val (.word sw)) := by
              simp [evalHOLExact, cs, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
            rw [hev_s] at hret; dsimp only at hret
            split at hret
            · injection hret with h1; injection h1 with hv
              have hsub_nat : (32#64 - rw).toNat = 32 - vw.toNat % 32 := by
                have hle_rw : rw.toNat ≤ 32 := by omega
                rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr hle_rw), hrw_nat]
                rfl
              rw [hsub_nat] at hsw_nat
              refine ⟨sw, hv.symm, ?_, ?_⟩
              · intro hle
                have hok : vw.toNat + (32 - vw.toNat % 32) < 2 ^ 64 := by omega
                rw [if_pos hok] at hsw_nat
                refine ⟨by omega, by omega, by omega, by omega, fun hm => by omega⟩
              · intro hge
                have hover : ¬ (vw.toNat + (32 - vw.toNat % 32) < 2 ^ 64) := by omega
                rw [if_neg hover] at hsw_nat
                exact hsw_nat
            · simp at hret
          · simp at hret
        | _ => simp at hret

private theorem eval_mul64x64_hi_nonzero {F : Type}
    (s : PanSemStateFiniteExact 64 F) {ww : BitVec 64}
    (hw_ge : 2 ^ 32 ≤ ww.toNat) (hw_lt : ww.toNat < 2 ^ 59)
    (ha : s.locals.lookup (ofString "a") = some (.val (.word ww)))
    (hb : s.locals.lookup (ofString "b") = some (.val (.word ww)))
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_mul64x64)).1 =
      some (.returned v)) :
    ∃ lo hi : BitVec 64, v = .rStruct [.val (.word lo), .val (.word hi)] ∧ hi ≠ 0#64 := by
  have hbody : sourceFnBody Guest.Software.guestFn_mul64x64 =
      .dec (ofString "a0") .one (.op .and [.var .local (ofString "a"), .const (4294967295#64)])
        (.dec (ofString "a1") .one (.shift .lsr (.var .local (ofString "a")) (.const (32#64)))
          (.dec (ofString "b0") .one (.op .and [.var .local (ofString "b"), .const (4294967295#64)])
            (.dec (ofString "b1") .one (.shift .lsr (.var .local (ofString "b")) (.const (32#64)))
              (.dec (ofString "p00") .one (.panop .mul [.var .local (ofString "a0"), .var .local (ofString "b0")])
                (.dec (ofString "p11") .one (.panop .mul [.var .local (ofString "a1"), .var .local (ofString "b1")])
                  (.dec (ofString "mid") (.comb [.one, .one]) (.rstruct [.const (0#64), .const (0#64)])
                    (.seq
                      (.primitive (ofString "mid") .addCarry
                        [.panop .mul [.var .local (ofString "a0"), .var .local (ofString "b1")],
                         .panop .mul [.var .local (ofString "a1"), .var .local (ofString "b0")],
                         .const (0#64)])
                      (.dec (ofString "lo") (.comb [.one, .one]) (.rstruct [.const (0#64), .const (0#64)])
                        (.seq
                          (.primitive (ofString "lo") .addCarry
                            [.var .local (ofString "p00"),
                             .shift .lsl (.rfield 0 (.var .local (ofString "mid"))) (.const (32#64)),
                             .const (0#64)])
                          (.dec (ofString "hi") .one
                            (.op .add
                              [.var .local (ofString "p11"),
                               .shift .lsr (.rfield 0 (.var .local (ofString "mid"))) (.const (32#64)),
                               .shift .lsl (.rfield 1 (.var .local (ofString "mid"))) (.const (32#64)),
                               .rfield 1 (.var .local (ofString "lo"))])
                            (.return (.rstruct [.rfield 0 (.var .local (ofString "lo")), .var .local (ofString "hi")])))))))))))) := rfl
  let a0 := ww &&& 4294967295#64
  let a1 := ww >>> (32 : Nat)
  let p00 := a0 * a0
  let p11 := a1 * a1
  let p01 := a0 * a1
  let mid := wordAddCarryHOL p01 p01 0#64
  let lo := wordAddCarryHOL p00 (mid.1 <<< (32 : Nat)) 0#64
  let hi := p11 + (mid.1 >>> (32 : Nat)) + (mid.2 <<< (32 : Nat)) + lo.2
  have h32 : (32#64 : BitVec 64).toNat = 32 := rfl
  have hand_w : wordOpHOL .and [ww, 4294967295#64] = some a0 := rfl
  have hlsr_w : wordShiftHOL .lsr ww 32 = some a1 := by simp [wordShiftHOL, a1]
  have hpo_mid : panPrimopHOLExact PrimOp.addCarry
      ([.val (.word p01), .val (.word p01), .val (.word 0#64)] : List (ValueHOL 64)) =
      some (.rStruct [.val (.word mid.1), .val (.word mid.2)]) := by
    simp [panPrimopHOLExact, mid]
  have hlsl_mid0 : wordShiftHOL .lsl mid.1 32 = some (mid.1 <<< (32 : Nat)) := by simp [wordShiftHOL]
  have hlsr_mid0 : wordShiftHOL .lsr mid.1 32 = some (mid.1 >>> (32 : Nat)) := by simp [wordShiftHOL]
  have hlsl_mid1 : wordShiftHOL .lsl mid.2 32 = some (mid.2 <<< (32 : Nat)) := by simp [wordShiftHOL]
  have hpo_lo : panPrimopHOLExact PrimOp.addCarry
      ([.val (.word p00), .val (.word (mid.1 <<< (32 : Nat))), .val (.word 0#64)] : List (ValueHOL 64)) =
      some (.rStruct [.val (.word lo.1), .val (.word lo.2)]) := by
    simp [panPrimopHOLExact, lo]
  have hadd4 : wordOpHOL .add [p11, mid.1 >>> (32 : Nat), mid.2 <<< (32 : Nat), lo.2] = some hi := by
    simp [wordOpHOL, wordOp, hi, BitVec.add_assoc]
  have hlk_eq {st : PanSemStateFiniteExact 64 F} (k : MlS) (u : ValueHOL 64) :
      (setVarHOLFinite k u st).locals.lookup k = some u := by
    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hlk_ne {st : PanSemStateFiniteExact 64 F} (k1 k2 : MlS) (u : ValueHOL 64) (hne : k1 ≠ k2) :
      (setVarHOLFinite k1 u st).locals.lookup k2 = st.locals.lookup k2 := by
    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne]
  have step_dec : ∀ {nm : MlS} {sh : ShapeHOL} {e : ExpHOL 64} {b : ProgHOL 64}
      {st : PanSemStateFiniteExact 64 F} {u : ValueHOL 64},
      @evalHOLExact 64 F _ st.toExact (fun x => Classical.propDecidable (st.memaddrs x)) e = some u →
      shapeEqHOL sh (shapeOfHOLExact u) = true →
      (evaluateHOLFiniteState st (.dec nm sh e b)).1 =
        (evaluateHOLFiniteState (setVarHOLFinite nm u st) b).1 := by
    intro nm sh e b st u hev hsh
    rw [evaluateHOLFiniteState_dec_total]; dsimp only
    rw [hev]; dsimp only; rw [if_pos hsh]
  have step_prim : ∀ {nm : MlS} {op : PrimOp} {args : List (ExpHOL 64)} {tl : ProgHOL 64}
      {st : PanSemStateFiniteExact 64 F} {vals : List (ValueHOL 64)} {u : ValueHOL 64},
      @evalListHOLExact 64 F _ st.toExact (fun x => Classical.propDecidable (st.memaddrs x)) args = some vals →
      panPrimopHOLExact op vals = some u →
      st.isValidValueHOLFinite .local nm u = true →
      (evaluateHOLFiniteState st (.seq (.primitive nm op args) tl)).1 =
        (evaluateHOLFiniteState (setVarHOLFinite nm u st) tl).1 := by
    intro nm op args tl st vals u hargs hpo hval
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_primitive, hargs]; dsimp only
    rw [hpo]; dsimp only; rw [if_pos hval]
  have hsh1 : ∀ w : BitVec 64, shapeEqHOL .one (shapeOfHOLExact (.val (.word w) : ValueHOL 64)) = true :=
    fun _ => by simp [shapeEqHOL, shapeOfHOLExact]
  have hsh2 : shapeEqHOL (.comb [.one, .one]) (shapeOfHOLExact (.rStruct [.val (.word (0#64)), .val (.word (0#64))] : ValueHOL 64)) = true := by
    simp [shapeEqHOL, shapeEqHOL.shapeEqListHOL, shapeOfHOLExact]
  rw [hbody] at hret
  rw [step_dec (u := .val (.word a0)) (by simp [evalHOLExact, evalListHOLExact, ha, valueIsWord, valueWord, hand_w]) (hsh1 _)] at hret
  set s1 := setVarHOLFinite (ofString "a0") (.val (.word a0)) s
  have hs1_a0 : s1.locals.lookup (ofString "a0") = some (.val (.word a0)) := hlk_eq _ _
  have hs1_a : s1.locals.lookup (ofString "a") = some (.val (.word ww)) := by
    rw [hlk_ne (ofString "a0") (ofString "a") _ (by decide)]; exact ha
  have hs1_b : s1.locals.lookup (ofString "b") = some (.val (.word ww)) := by
    rw [hlk_ne (ofString "a0") (ofString "b") _ (by decide)]; exact hb
  rw [step_dec (u := .val (.word a1)) (by simp [evalHOLExact, hs1_a, h32, hlsr_w]) (hsh1 _)] at hret
  set s2 := setVarHOLFinite (ofString "a1") (.val (.word a1)) s1
  have hs2_a1 : s2.locals.lookup (ofString "a1") = some (.val (.word a1)) := hlk_eq _ _
  have hs2_a0 : s2.locals.lookup (ofString "a0") = some (.val (.word a0)) := by
    rw [hlk_ne (ofString "a1") (ofString "a0") _ (by decide)]; exact hs1_a0
  have hs2_b : s2.locals.lookup (ofString "b") = some (.val (.word ww)) := by
    rw [hlk_ne (ofString "a1") (ofString "b") _ (by decide)]; exact hs1_b
  rw [step_dec (u := .val (.word a0)) (by simp [evalHOLExact, evalListHOLExact, hs2_b, valueIsWord, valueWord, hand_w]) (hsh1 _)] at hret
  set s3 := setVarHOLFinite (ofString "b0") (.val (.word a0)) s2
  have hs3_b0 : s3.locals.lookup (ofString "b0") = some (.val (.word a0)) := hlk_eq _ _
  have hs3_a1 : s3.locals.lookup (ofString "a1") = some (.val (.word a1)) := by
    rw [hlk_ne (ofString "b0") (ofString "a1") _ (by decide)]; exact hs2_a1
  have hs3_a0 : s3.locals.lookup (ofString "a0") = some (.val (.word a0)) := by
    rw [hlk_ne (ofString "b0") (ofString "a0") _ (by decide)]; exact hs2_a0
  have hs3_b : s3.locals.lookup (ofString "b") = some (.val (.word ww)) := by
    rw [hlk_ne (ofString "b0") (ofString "b") _ (by decide)]; exact hs2_b
  rw [step_dec (u := .val (.word a1)) (by simp [evalHOLExact, hs3_b, h32, hlsr_w]) (hsh1 _)] at hret
  set s4 := setVarHOLFinite (ofString "b1") (.val (.word a1)) s3
  have hs4_b1 : s4.locals.lookup (ofString "b1") = some (.val (.word a1)) := hlk_eq _ _
  have hs4_b0 : s4.locals.lookup (ofString "b0") = some (.val (.word a0)) := by
    rw [hlk_ne (ofString "b1") (ofString "b0") _ (by decide)]; exact hs3_b0
  have hs4_a1 : s4.locals.lookup (ofString "a1") = some (.val (.word a1)) := by
    rw [hlk_ne (ofString "b1") (ofString "a1") _ (by decide)]; exact hs3_a1
  have hs4_a0 : s4.locals.lookup (ofString "a0") = some (.val (.word a0)) := by
    rw [hlk_ne (ofString "b1") (ofString "a0") _ (by decide)]; exact hs3_a0
  rw [step_dec (u := .val (.word p00)) (by simp [evalHOLExact, evalListHOLExact, hs4_a0, hs4_b0, valueIsWord, valueWord, panOpHOL, p00]) (hsh1 _)] at hret
  set s5 := setVarHOLFinite (ofString "p00") (.val (.word p00)) s4
  have hs5_p00 : s5.locals.lookup (ofString "p00") = some (.val (.word p00)) := hlk_eq _ _
  have hs5_b1 : s5.locals.lookup (ofString "b1") = some (.val (.word a1)) := by
    rw [hlk_ne (ofString "p00") (ofString "b1") _ (by decide)]; exact hs4_b1
  have hs5_b0 : s5.locals.lookup (ofString "b0") = some (.val (.word a0)) := by
    rw [hlk_ne (ofString "p00") (ofString "b0") _ (by decide)]; exact hs4_b0
  have hs5_a1 : s5.locals.lookup (ofString "a1") = some (.val (.word a1)) := by
    rw [hlk_ne (ofString "p00") (ofString "a1") _ (by decide)]; exact hs4_a1
  have hs5_a0 : s5.locals.lookup (ofString "a0") = some (.val (.word a0)) := by
    rw [hlk_ne (ofString "p00") (ofString "a0") _ (by decide)]; exact hs4_a0
  rw [step_dec (u := .val (.word p11)) (by simp [evalHOLExact, evalListHOLExact, hs5_a1, hs5_b1, valueIsWord, valueWord, panOpHOL, p11]) (hsh1 _)] at hret
  set s6 := setVarHOLFinite (ofString "p11") (.val (.word p11)) s5
  have hs6_p11 : s6.locals.lookup (ofString "p11") = some (.val (.word p11)) := hlk_eq _ _
  have hs6_p00 : s6.locals.lookup (ofString "p00") = some (.val (.word p00)) := by
    rw [hlk_ne (ofString "p11") (ofString "p00") _ (by decide)]; exact hs5_p00
  have hs6_b1 : s6.locals.lookup (ofString "b1") = some (.val (.word a1)) := by
    rw [hlk_ne (ofString "p11") (ofString "b1") _ (by decide)]; exact hs5_b1
  have hs6_b0 : s6.locals.lookup (ofString "b0") = some (.val (.word a0)) := by
    rw [hlk_ne (ofString "p11") (ofString "b0") _ (by decide)]; exact hs5_b0
  have hs6_a1 : s6.locals.lookup (ofString "a1") = some (.val (.word a1)) := by
    rw [hlk_ne (ofString "p11") (ofString "a1") _ (by decide)]; exact hs5_a1
  have hs6_a0 : s6.locals.lookup (ofString "a0") = some (.val (.word a0)) := by
    rw [hlk_ne (ofString "p11") (ofString "a0") _ (by decide)]; exact hs5_a0
  rw [step_dec (u := .rStruct [.val (.word 0#64), .val (.word 0#64)]) (by simp [evalHOLExact, evalListHOLExact]) hsh2] at hret
  set s7 := setVarHOLFinite (ofString "mid") (.rStruct [.val (.word 0#64), .val (.word 0#64)]) s6
  have hs7_mid : s7.locals.lookup (ofString "mid") = some (.rStruct [.val (.word 0#64), .val (.word 0#64)]) := hlk_eq _ _
  have hs7_p11 : s7.locals.lookup (ofString "p11") = some (.val (.word p11)) := by
    rw [hlk_ne (ofString "mid") (ofString "p11") _ (by decide)]; exact hs6_p11
  have hs7_p00 : s7.locals.lookup (ofString "p00") = some (.val (.word p00)) := by
    rw [hlk_ne (ofString "mid") (ofString "p00") _ (by decide)]; exact hs6_p00
  have hs7_b1 : s7.locals.lookup (ofString "b1") = some (.val (.word a1)) := by
    rw [hlk_ne (ofString "mid") (ofString "b1") _ (by decide)]; exact hs6_b1
  have hs7_b0 : s7.locals.lookup (ofString "b0") = some (.val (.word a0)) := by
    rw [hlk_ne (ofString "mid") (ofString "b0") _ (by decide)]; exact hs6_b0
  have hs7_a1 : s7.locals.lookup (ofString "a1") = some (.val (.word a1)) := by
    rw [hlk_ne (ofString "mid") (ofString "a1") _ (by decide)]; exact hs6_a1
  have hs7_a0 : s7.locals.lookup (ofString "a0") = some (.val (.word a0)) := by
    rw [hlk_ne (ofString "mid") (ofString "a0") _ (by decide)]; exact hs6_a0
  have hp10 : a1 * a0 = p01 := BitVec.mul_comm a1 a0
  rw [step_prim
    (by simp [evalListHOLExact, evalHOLExact, hs7_a0, hs7_a1, hs7_b0, hs7_b1, valueIsWord, valueWord, panOpHOL, p01, hp10])
    hpo_mid
    (by simp [isValidValueHOLFinite, lookupKvarHOLFinite, hs7_mid, shapeEqHOL, shapeEqHOL.shapeEqListHOL, shapeOfHOLExact])] at hret
  set s8 := setVarHOLFinite (ofString "mid") (.rStruct [.val (.word mid.1), .val (.word mid.2)]) s7
  have hs8_mid : s8.locals.lookup (ofString "mid") = some (.rStruct [.val (.word mid.1), .val (.word mid.2)]) := hlk_eq _ _
  have hs8_p11 : s8.locals.lookup (ofString "p11") = some (.val (.word p11)) := by
    rw [hlk_ne (ofString "mid") (ofString "p11") _ (by decide)]; exact hs7_p11
  have hs8_p00 : s8.locals.lookup (ofString "p00") = some (.val (.word p00)) := by
    rw [hlk_ne (ofString "mid") (ofString "p00") _ (by decide)]; exact hs7_p00
  rw [step_dec (u := .rStruct [.val (.word 0#64), .val (.word 0#64)]) (by simp [evalHOLExact, evalListHOLExact]) hsh2] at hret
  set s9 := setVarHOLFinite (ofString "lo") (.rStruct [.val (.word 0#64), .val (.word 0#64)]) s8
  have hs9_lo : s9.locals.lookup (ofString "lo") = some (.rStruct [.val (.word 0#64), .val (.word 0#64)]) := hlk_eq _ _
  have hs9_mid : s9.locals.lookup (ofString "mid") = some (.rStruct [.val (.word mid.1), .val (.word mid.2)]) := by
    rw [hlk_ne (ofString "lo") (ofString "mid") _ (by decide)]; exact hs8_mid
  have hs9_p11 : s9.locals.lookup (ofString "p11") = some (.val (.word p11)) := by
    rw [hlk_ne (ofString "lo") (ofString "p11") _ (by decide)]; exact hs8_p11
  have hs9_p00 : s9.locals.lookup (ofString "p00") = some (.val (.word p00)) := by
    rw [hlk_ne (ofString "lo") (ofString "p00") _ (by decide)]; exact hs8_p00
  rw [step_prim
    (by simp [evalListHOLExact, evalHOLExact, hs9_p00, hs9_mid, h32, hlsl_mid0])
    hpo_lo
    (by simp [isValidValueHOLFinite, lookupKvarHOLFinite, hs9_lo, shapeEqHOL, shapeEqHOL.shapeEqListHOL, shapeOfHOLExact])] at hret
  set s10 := setVarHOLFinite (ofString "lo") (.rStruct [.val (.word lo.1), .val (.word lo.2)]) s9
  have hs10_lo : s10.locals.lookup (ofString "lo") = some (.rStruct [.val (.word lo.1), .val (.word lo.2)]) := hlk_eq _ _
  have hs10_mid : s10.locals.lookup (ofString "mid") = some (.rStruct [.val (.word mid.1), .val (.word mid.2)]) := by
    rw [hlk_ne (ofString "lo") (ofString "mid") _ (by decide)]; exact hs9_mid
  have hs10_p11 : s10.locals.lookup (ofString "p11") = some (.val (.word p11)) := by
    rw [hlk_ne (ofString "lo") (ofString "p11") _ (by decide)]; exact hs9_p11
  rw [step_dec (u := .val (.word hi))
    (by simp [evalHOLExact, evalListHOLExact, hs10_p11, hs10_mid, hs10_lo, valueIsWord, valueWord, h32, hlsr_mid0, hlsl_mid1, hadd4]) (hsh1 _)] at hret
  set s11 := setVarHOLFinite (ofString "hi") (.val (.word hi)) s10
  have hs11_hi : s11.locals.lookup (ofString "hi") = some (.val (.word hi)) := hlk_eq _ _
  have hs11_lo : s11.locals.lookup (ofString "lo") = some (.rStruct [.val (.word lo.1), .val (.word lo.2)]) := by
    rw [hlk_ne (ofString "hi") (ofString "lo") _ (by decide)]; exact hs10_lo
  rw [evaluateHOLFiniteState_return] at hret
  have hev_ret : @evalHOLExact 64 F _ s11.toExact (fun a => Classical.propDecidable (s11.memaddrs a))
      (.rstruct [.rfield 0 (.var .local (ofString "lo")), .var .local (ofString "hi")]) =
      some (.rStruct [.val (.word lo.1), .val (.word hi)]) := by
    simp [evalHOLExact, evalListHOLExact, hs11_lo, hs11_hi]
  rw [hev_ret] at hret; dsimp only at hret
  have hsz : sizeOfShapeWithContextHOL s11.structs
      (shapeOfHOLExact (.rStruct [.val (.word lo.1), .val (.word hi)] : ValueHOL 64)) ≤ 32 := by
    simp [shapeOfHOLExact, sizeOfShapeWithContextHOL, sizeOfShapesWithContextHOL]
  rw [if_pos hsz] at hret; dsimp only at hret
  injection hret with h1; injection h1 with hv
  refine ⟨lo.1, hi, hv.symm, ?_⟩
  have ha1_nat : a1.toNat = ww.toNat / 2 ^ 32 := by
    dsimp only [a1]; rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have ha1_pos : 1 ≤ a1.toNat := by omega
  have ha1_lt : a1.toNat < 2 ^ 27 := by
    have : (2 ^ 59 : Nat) = 2 ^ 27 * 2 ^ 32 := by decide
    omega
  have hp11_lt : a1.toNat * a1.toNat < 2 ^ 54 := by
    have hmul : a1.toNat * a1.toNat < 2 ^ 27 * 2 ^ 27 := Nat.mul_lt_mul'' ha1_lt ha1_lt
    have : (2 ^ 27 : Nat) * 2 ^ 27 = 2 ^ 54 := by decide
    omega
  have hp11_nat : p11.toNat = a1.toNat * a1.toNat := by
    dsimp only [p11]; rw [BitVec.toNat_mul, Nat.mod_eq_of_lt (by omega)]
  have hp11_pos : 1 ≤ p11.toNat := by
    rw [hp11_nat]; exact Nat.mul_le_mul ha1_pos ha1_pos
  have hmid0_lsr : (mid.1 >>> (32 : Nat)).toNat < 2 ^ 32 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have := mid.1.isLt
    have : (2 ^ 64 : Nat) = 2 ^ 32 * 2 ^ 32 := by decide
    omega
  have hcarry_bit : ∀ x y z : BitVec 64, (wordAddCarryHOL x y z).2 = 0 ∨ (wordAddCarryHOL x y z).2 = 1 := by
    intro x y z; unfold wordAddCarryHOL; split_ifs <;> simp <;> omega
  have hmid2_le : mid.2.toNat ≤ 1 := by
    rcases hcarry_bit p01 p01 0#64 with h | h
    · dsimp only [mid]; rw [h]; decide
    · dsimp only [mid]; rw [h]; decide
  have hmid2_lsl : (mid.2 <<< (32 : Nat)).toNat ≤ 2 ^ 32 := by
    rw [BitVec.toNat_shiftLeft]
    have : mid.2.toNat <<< 32 = mid.2.toNat * 2 ^ 32 := Nat.shiftLeft_eq mid.2.toNat 32
    rw [this, Nat.mod_eq_of_lt (by omega)]
    omega
  have hlo2_le : lo.2.toNat ≤ 1 := by
    rcases hcarry_bit p00 (mid.1 <<< (32 : Nat)) 0#64 with h | h
    · dsimp only [lo]; rw [h]; decide
    · dsimp only [lo]; rw [h]; decide
  have hhi_pos : 0 < hi.toNat := by
    dsimp only [hi]
    have hsum1 : (p11 + (mid.1 >>> (32 : Nat))).toNat = p11.toNat + (mid.1 >>> (32 : Nat)).toNat := by
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
    have hsum2 : (p11 + (mid.1 >>> (32 : Nat)) + (mid.2 <<< (32 : Nat))).toNat =
        p11.toNat + (mid.1 >>> (32 : Nat)).toNat + (mid.2 <<< (32 : Nat)).toNat := by
      rw [BitVec.toNat_add, hsum1, Nat.mod_eq_of_lt (by omega)]
    have hsum3 : (p11 + (mid.1 >>> (32 : Nat)) + (mid.2 <<< (32 : Nat)) + lo.2).toNat =
        p11.toNat + (mid.1 >>> (32 : Nat)).toNat + (mid.2 <<< (32 : Nat)).toNat + lo.2.toNat := by
      rw [BitVec.toNat_add, hsum2, Nat.mod_eq_of_lt (by omega)]
    omega
  intro hz; rw [hz] at hhi_pos; simp at hhi_pos

private theorem words_of_ge_of_ge {F : Type}
    (s : PanSemStateFiniteExact 64 F) {nw : BitVec 64}
    (hn_ge : 2 ^ 37 ≤ nw.toNat)
    (hcode : s.code = originalRuntimeCode)
    (hn : s.locals.lookup (ofString "n") = some (.val (.word nw)))
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_words_of)).1 =
      some (.returned v)) :
    ∃ ww : BitVec 64, v = .val (.word ww) ∧ 2 ^ 32 ≤ ww.toNat ∧ ww.toNat < 2 ^ 59 := by
  have hbody : sourceFnBody Guest.Software.guestFn_words_of =
      .decCall (ofString "c") .one (ofString "ceil32") [.var .local (ofString "n")]
        (.return (.shift .lsr (.var .local (ofString "c")) (.const 5#64))) := rfl
  rw [hbody, evaluateHOLFiniteState_decCall_fixClockRewrite] at hret
  have hargs : evalListHOLFinite s (h := fun x => Classical.propDecidable (s.memaddrs x))
      [.var .local (ofString "n")] = some [.val (.word nw)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hn]
  rw [hargs] at hret; dsimp only at hret
  have hlk := pan_one_word_lookup s.code.lookup (ofString "ceil32") (ofString "v")
    (sourceFnBody Guest.Software.guestFn_ceil32) nw
    (by rw [hcode]; exact lookup_ceil32)
  rw [hlk] at hret; dsimp only at hret
  split at hret
  · simp at hret
  · let cal := HolFiniteMapExact.empty.update (ofString "v", ValueHOL.val (.word nw))
    rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s cal)
        (sourceFnBody Guest.Software.guestFn_ceil32) with ⟨rb, pb⟩
    rw [hrun] at hret
    rcases rb with _ | rb
    · simp at hret
    · cases rb with
      | returned vb =>
        dsimp only at hret
        split at hret
        · dsimp only at hret
          have hv_lk : (callEntryStateHOLFinite s cal).locals.lookup (ofString "v") =
              some (.val (.word nw)) := by
            simp [cal, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          obtain ⟨cw, rfl, hlo, hhi⟩ := ceil32_body_exact (callEntryStateHOLFinite s cal) hcode hv_lk vb
            (by rw [hrun])
          have hcw_ge : 2 ^ 37 ≤ cw.toNat := by
            by_cases hle : nw.toNat ≤ 2 ^ 64 - 32
            · have := (hlo hle).1; omega
            · have := hhi (by omega); omega
          set cs := setVarHOLFinite (ofString "c") (.val (.word cw)) { pb with locals := s.locals }
          rw [evaluateHOLFiniteState_return] at hret
          have hcs_c : cs.locals.lookup (ofString "c") = some (.val (.word cw)) := by
            simp [cs, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          have h5 : (5#64 : BitVec 64).toNat = 5 := rfl
          have hshf : wordShiftHOL .lsr cw 5 = some (cw >>> (5 : Nat)) := by simp [wordShiftHOL]
          have hev : @evalHOLExact 64 F _ cs.toExact (fun a => Classical.propDecidable (cs.memaddrs a))
              (.shift .lsr (.var .local (ofString "c")) (.const 5#64)) =
              some (.val (.word (cw >>> (5 : Nat)))) := by
            simp [evalHOLExact, hcs_c, h5, hshf]
          rw [hev] at hret; dsimp only at hret
          split at hret
          · injection hret with h1; injection h1 with hv
            refine ⟨cw >>> (5 : Nat), hv.symm, ?_, ?_⟩
            · rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
              have : (2 ^ 37 : Nat) = 2 ^ 32 * 2 ^ 5 := by decide
              omega
            · rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
              have := cw.isLt
              have : (2 ^ 64 : Nat) = 2 ^ 59 * 2 ^ 5 := by decide
              omega
          · simp at hret
        · simp at hret
      | _ => simp at hret

private theorem memory_gas_cost_ge_twoPow37 {F : Type}
    (s : PanSemStateFiniteExact 64 F) {szw : BitVec 64}
    (hsz_ge : 2 ^ 37 ≤ szw.toNat)
    (hcode : s.code = originalRuntimeCode)
    (hsz_lk : s.locals.lookup (ofString "size") = some (.val (.word szw)))
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_memory_gas_cost)).1 =
      some (.returned v)) :
    v = .val (.word 18446744073709551615#64) := by
  have hbody : sourceFnBody Guest.Software.guestFn_memory_gas_cost =
      .decCall (ofString "w") .one (ofString "words_of") [.var .local (ofString "size")]
        (.decCall (ofString "sq") (.comb [.one, .one]) (ofString "mul64x64")
          [.var .local (ofString "w"), .var .local (ofString "w")]
          (.seq
            (.ite (.cmp .notEqual (.rfield 1 (.var .local (ofString "sq"))) (.const 0#64))
              (.return (.const 18446744073709551615#64))
              .skip)
            (.decCall (ofString "a") .one (ofString "add_sat")
              [.panop .mul [.var .local (ofString "w"), .const 3#64],
               .shift .lsr (.rfield 0 (.var .local (ofString "sq"))) (.const 9#64)]
              (.return (.var .local (ofString "a")))))) := rfl
  rw [hbody, evaluateHOLFiniteState_decCall_fixClockRewrite] at hret
  have hargs1 : evalListHOLFinite s (h := fun x => Classical.propDecidable (s.memaddrs x))
      [.var .local (ofString "size")] = some [.val (.word szw)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hsz_lk]
  rw [hargs1] at hret; dsimp only at hret
  have hlk1 := pan_one_word_lookup s.code.lookup (ofString "words_of") (ofString "n")
    (sourceFnBody Guest.Software.guestFn_words_of) szw
    (by rw [hcode]; exact lookup_words_of)
  rw [hlk1] at hret; dsimp only at hret
  split at hret
  · simp at hret
  · let cal1 := HolFiniteMapExact.empty.update (ofString "n", ValueHOL.val (.word szw))
    rcases hrun1 : evaluateHOLFiniteState (callEntryStateHOLFinite s cal1)
        (sourceFnBody Guest.Software.guestFn_words_of) with ⟨rb1, pb1⟩
    rw [hrun1] at hret
    have hpb1_code : pb1.code = originalRuntimeCode := by
      have hm := (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s cal1)
        (sourceFnBody Guest.Software.guestFn_words_of)).1
      rw [hrun1] at hm; exact hm.trans hcode
    rcases rb1 with _ | rb1
    · simp at hret
    · cases rb1 with
      | returned vb1 =>
        dsimp only at hret
        split at hret
        · dsimp only at hret
          have hn1 : (callEntryStateHOLFinite s cal1).locals.lookup (ofString "n") =
              some (.val (.word szw)) := by
            simp [cal1, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          obtain ⟨ww, rfl, hww_ge, hww_lt⟩ :=
            words_of_ge_of_ge (callEntryStateHOLFinite s cal1) hsz_ge hcode hn1 vb1 (by rw [hrun1])
          set s1 := setVarHOLFinite (ofString "w") (.val (.word ww)) { pb1 with locals := s.locals }
          have hs1_w : s1.locals.lookup (ofString "w") = some (.val (.word ww)) := by
            simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          have hs1_code : s1.code = originalRuntimeCode := hpb1_code
          rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hret
          have hargs2 : evalListHOLFinite s1 (h := fun x => Classical.propDecidable (s1.memaddrs x))
              [.var .local (ofString "w"), .var .local (ofString "w")] =
              some [.val (.word ww), .val (.word ww)] := by
            simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hs1_w]
          rw [hargs2] at hret; dsimp only at hret
          have hlk2 : lookupCodeHOLFinite s1.code.lookup (ofString "mul64x64")
              [.val (.word ww), .val (.word ww)] =
              some (sourceFnBody Guest.Software.guestFn_mul64x64,
                (HolFiniteMapExact.empty.update (ofString "a", ValueHOL.val (.word ww))).update
                  (ofString "b", ValueHOL.val (.word ww)),
                .comb [.one, .one]) := by
            have hd : ofString "a" ≠ ofString "b" := by decide
            have raw : lookupCodeHOLExact s1.code.lookup (ofString "mul64x64")
                [.val (.word ww), .val (.word ww)] =
                some (sourceFnBody Guest.Software.guestFn_mul64x64,
                  (fun key => if key = ofString "b" then some (.val (.word ww))
                    else if key = ofString "a" then some (.val (.word ww)) else none),
                  .comb [.one, .one]) := by
              simp [lookupCodeHOLExact, hs1_code, lookup_mul64x64, shapeOfHOLExact, shapeEqHOL, hd]
            unfold PanSemStateFiniteExact.lookupCodeHOLFinite
            split
            · rename_i missing; rw [raw] at missing; cases missing
            · rename_i foundBody foundLocals foundShape found
              have equal := Option.some.inj (found.symm.trans raw)
              obtain ⟨rfl, rest⟩ := Prod.mk.inj equal
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj rest
              apply congrArg (fun locals => some (sourceFnBody Guest.Software.guestFn_mul64x64, locals, ShapeHOL.comb [.one, .one]))
              apply HolFiniteMapExact.ext
              funext key
              by_cases hb_k : key = ofString "b"
              · subst key; simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY]
              · have hb_k' : ofString "b" ≠ key := Ne.symm hb_k
                by_cases ha_k : key = ofString "a"
                · subst key; simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY, hd, Ne.symm hd]
                · have ha_k' : ofString "a" ≠ key := Ne.symm ha_k
                  simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY, ha_k, hb_k, ha_k', hb_k']
          rw [hlk2] at hret; dsimp only at hret
          split at hret
          · simp at hret
          · let cal2 := (HolFiniteMapExact.empty.update (ofString "a", ValueHOL.val (.word ww))).update
              (ofString "b", ValueHOL.val (.word ww))
            rcases hrun2 : evaluateHOLFiniteState (callEntryStateHOLFinite s1 cal2)
                (sourceFnBody Guest.Software.guestFn_mul64x64) with ⟨rb2, pb2⟩
            rw [hrun2] at hret
            rcases rb2 with _ | rb2
            · simp at hret
            · cases rb2 with
              | returned vb2 =>
                dsimp only at hret
                split at hret
                · dsimp only at hret
                  have ha2 : (callEntryStateHOLFinite s1 cal2).locals.lookup (ofString "a") =
                      some (.val (.word ww)) := by
                    have hne : ofString "b" ≠ ofString "a" := by decide
                    simp [cal2, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne]
                  have hb2 : (callEntryStateHOLFinite s1 cal2).locals.lookup (ofString "b") =
                      some (.val (.word ww)) := by
                    simp [cal2, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                  obtain ⟨low, hiw, rfl, hhi_ne0⟩ :=
                    eval_mul64x64_hi_nonzero (callEntryStateHOLFinite s1 cal2) hww_ge hww_lt ha2 hb2 vb2 (by rw [hrun2])
                  set s2 := setVarHOLFinite (ofString "sq")
                    (.rStruct [.val (.word low), .val (.word hiw)]) { pb2 with locals := s1.locals }
                  have hs2_sq : s2.locals.lookup (ofString "sq") =
                      some (.rStruct [.val (.word low), .val (.word hiw)]) := by
                    simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hret
                  have h10 : ¬ ((1#64 : BitVec 64) = 0) := by decide
                  have hcmp : @evalHOLExact 64 F _ s2.toExact (fun x => Classical.propDecidable (s2.memaddrs x))
                      (.cmp .notEqual (.rfield 1 (.var .local (ofString "sq"))) (.const 0#64)) =
                      some (.val (.word 1#64)) := by
                    simp [evalHOLExact, hs2_sq, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hhi_ne0]
                  rw [hcmp] at hret; dsimp only at hret
                  rw [if_neg h10] at hret
                  rw [evaluateHOLFiniteState_return] at hret; dsimp only [evalHOLExact] at hret
                  have hsz : sizeOfShapeWithContextHOL s2.structs
                      (shapeOfHOLExact (.val (.word 18446744073709551615#64))) ≤ 32 := by
                    simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
                  rw [if_pos hsz] at hret; dsimp only at hret
                  injection hret with h1; injection h1 with hv; exact hv.symm
                · simp at hret
              | _ => simp at hret
        · simp at hret
      | _ => simp at hret

private theorem extend_memory_cost1_body_bounds {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode)
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_extend_memory_cost1)).1 =
      some (.returned v)) :
    ∃ cw ebw : BitVec 64,
      v = .rStruct [.val (.word cw), .val (.word ebw)] ∧
      (ebw = 0#64 ∨
        ∃ before after : Nat,
          after < 2 ^ 37 ∧
          after % 32 = 0 ∧
          before < after ∧
          ebw.toNat = after - before ∧
          (memW s (globN s "ev" + 32) % 32 = 0 → before = memW s (globN s "ev" + 32))) := by
  have hbody : sourceFnBody Guest.Software.guestFn_extend_memory_cost1 =
      .decCall (ofString "z") .one (ofString "u256_is_zero") [.var .local (ofString "size")]
        (.seq
          (.ite (.cmp .notEqual (.var .local (ofString "z")) (.const 0#64))
            (.return (.rstruct [.const 0#64, .const 0#64]))
            .skip)
          (.decCall (ofString "s") .one (ofString "sat_word") [.var .local (ofString "start")]
            (.decCall (ofString "n") .one (ofString "sat_word") [.var .local (ofString "size")]
              (.decCall (ofString "endp") .one (ofString "add_sat") [.var .local (ofString "s"), .var .local (ofString "n")]
                (.seq
                  (.ite (.cmp .equal (.var .local (ofString "endp")) (.const 18446744073709551615#64))
                    (.return (.rstruct [.const 18446744073709551615#64, .const 0#64]))
                    .skip)
                  (.dec (ofString "cur") .one (.load .one (.op .add [.var .global (ofString "ev"), .const 32#64]))
                    (.decCall (ofString "before") .one (ofString "ceil32") [.var .local (ofString "cur")]
                      (.decCall (ofString "after") .one (ofString "ceil32") [.var .local (ofString "endp")]
                        (.seq
                          (.ite (.cmp .notLower (.var .local (ofString "before")) (.var .local (ofString "after")))
                            (.return (.rstruct [.const 0#64, .const 0#64]))
                            .skip)
                          (.decCall (ofString "ca") .one (ofString "memory_gas_cost") [.var .local (ofString "after")]
                            (.decCall (ofString "cb") .one (ofString "memory_gas_cost") [.var .local (ofString "before")]
                              (.seq
                                (.ite (.cmp .equal (.var .local (ofString "ca")) (.const 18446744073709551615#64))
                                  (.return (.rstruct [.const 18446744073709551615#64, .const 0#64]))
                                  .skip)
                                (.return (.rstruct
                                  [.op .sub [.var .local (ofString "ca"), .var .local (ofString "cb")],
                                   .op .sub [.var .local (ofString "after"), .var .local (ofString "before")]])))))))))))))) := rfl
  have hret_rstruct : ∀ (st : PanSemStateFiniteExact 64 F) (w1 w2 : BitVec 64),
      evaluateHOLFiniteState st (.return (.rstruct [.const w1, .const w2])) =
        (some (.returned (.rStruct [.val (.word w1), .val (.word w2)])), st.emptyLocalsHOLFinite) := by
    intro st w1 w2
    rw [evaluateHOLFiniteState_return]
    have hev : @evalHOLExact 64 F _ st.toExact (fun x => Classical.propDecidable (st.memaddrs x))
        (.rstruct [.const w1, .const w2]) =
        some (.rStruct [.val (.word w1), .val (.word w2)]) := by
      simp [evalHOLExact, evalListHOLExact]
    rw [hev]; dsimp only
    have hsz : sizeOfShapeWithContextHOL st.structs
        (shapeOfHOLExact (.rStruct [.val (.word w1), .val (.word w2)] : ValueHOL 64)) ≤ 32 := by
      simp [shapeOfHOLExact, sizeOfShapeWithContextHOL, sizeOfShapesWithContextHOL]
    rw [if_pos hsz]
  have step_ro_call : ∀ {st : PanSemStateFiniteExact 64 F} {nm fname : MlS} {args : List (ExpHOL 64)} {cont : ProgHOL 64},
      opRoCallees fname = true →
      st.code = originalRuntimeCode →
      LocFrame s st →
      (evaluateHOLFiniteState st (.decCall nm .one fname args cont)).1 = some (.returned v) →
      ∃ (w : BitVec 64) (st' : PanSemStateFiniteExact 64 F),
        st'.code = originalRuntimeCode ∧
        LocFrame s st' ∧
        st'.locals = st.locals.update (nm, .val (.word w)) ∧
        (∃ vals body callee rs,
          evalListHOLFinite st (h := fun x => Classical.propDecidable (st.memaddrs x)) args = some vals ∧
          lookupCodeHOLFinite originalRuntimeCode.lookup fname vals = some (body, callee, rs) ∧
          (evaluateHOLFiniteState (callEntryStateHOLFinite st callee) body).1 = some (.returned (.val (.word w)))) ∧
        (evaluateHOLFiniteState st' cont).1 = some (.returned v) := by
    intro st nm fname args cont hfn hst_c hst_lf hr
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hr
    rcases hargs : evalListHOLFinite st (h := fun x => Classical.propDecidable (st.memaddrs x)) args with _ | vals
    · rw [hargs] at hr; simp at hr
    · rw [hargs] at hr; dsimp only at hr
      rcases hl : lookupCodeHOLFinite st.code.lookup fname vals with _ | ⟨body, callee, rs⟩
      · rw [hl] at hr; simp at hr
      · rw [hl] at hr; dsimp only at hr
        split at hr
        · simp at hr
        · have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup fname vals = some (body, callee, rs) := by
            rwa [← hst_c]
          have hbody_ro := opRoCallees_good fname hfn vals body callee rs hl_orig
          have hsafe := evaluate_readOnlyProg opRoCallees opRoCallees_good body hbody_ro
            (callEntryStateHOLFinite st callee) hst_c
          rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite st callee) body with ⟨rb, pb⟩
          rw [hrun] at hr
          have hpb_c : pb.code = originalRuntimeCode := by
            have hm := (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite st callee) body).1
            rw [hrun] at hm; exact hm.trans hst_c
          rcases rb with _ | rb
          · simp at hr
          · cases rb with
            | returned vb =>
              dsimp only at hr
              split at hr
              · rename_i hsh_vb
                dsimp only at hr
                have hsh_one : shapeEqHOL (shapeOfHOLExact vb) .one = true := by
                  simp [Bool.and_eq_true] at hsh_vb; exact hsh_vb.1
                rcases vb with ⟨⟨w⟩⟩ | _ | _
                · have hlf_ce : LocFrame (callEntryStateHOLFinite st callee) pb := by
                    have hres := hsafe.to_resumes (by rw [hrun]; exact Or.inl ⟨.val (.word w), rfl⟩)
                    simpa [hrun] using hres
                  have hlf_st : LocFrame st pb := by
                    unfold LocFrame at hlf_ce ⊢; rw [hlf_ce]; rfl
                  let st' := setVarHOLFinite nm (.val (.word w)) { pb with locals := st.locals }
                  have hlf_st' : LocFrame s st' :=
                    hst_lf.trans (hlf_st.with_locals_clock (st.locals.update (nm, .val (.word w))) pb.clock)
                  exact ⟨w, st', hpb_c, hlf_st', rfl,
                    ⟨vals, body, callee, rs, rfl, hl_orig, by rw [hrun]⟩, hr⟩
                · simp [shapeOfHOLExact, shapeEqHOL] at hsh_one
                · simp [shapeOfHOLExact, shapeEqHOL] at hsh_one
              · simp at hr
            | _ => simp at hr
  have h10 : ¬ ((1#64 : BitVec 64) = 0) := by decide
  have h00 : (0#64 : BitVec 64) = 0 := rfl
  rw [hbody] at hret
  obtain ⟨zw, s1, hs1_c, hs1_lf, hs1_loc, _, hr1⟩ :=
    step_ro_call (by decide) hcode (LocFrame.refl s) hret
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hr1
  have hs1_z : s1.locals.lookup (ofString "z") = some (.val (.word zw)) := by
    rw [hs1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hcmp_z : @evalHOLExact 64 F _ s1.toExact (fun x => Classical.propDecidable (s1.memaddrs x))
      (.cmp .notEqual (.var .local (ofString "z")) (.const 0#64)) =
      some (.val (.word (if zw ≠ 0#64 then (1#64 : BitVec 64) else 0#64))) := by
    simp [evalHOLExact, hs1_z, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  rw [hcmp_z] at hr1; dsimp only at hr1
  by_cases hzw : zw ≠ 0#64
  · rw [if_pos hzw] at hr1; rw [if_neg h10] at hr1; rw [hret_rstruct s1 0#64 0#64] at hr1
    injection hr1 with h1; injection h1 with hv
    exact ⟨0#64, 0#64, hv.symm, Or.inl rfl⟩
  · rw [if_neg hzw] at hr1; rw [if_pos h00] at hr1; rw [evaluateHOLFiniteState_skip] at hr1; dsimp only at hr1
    obtain ⟨sw, s2, hs2_c, hs2_lf, hs2_loc, _, hr2⟩ :=
      step_ro_call (by decide) hs1_c hs1_lf hr1
    obtain ⟨nw, s3, hs3_c, hs3_lf, hs3_loc, _, hr3⟩ :=
      step_ro_call (by decide) hs2_c hs2_lf hr2
    obtain ⟨endpw, s4, hs4_c, hs4_lf, hs4_loc, _, hr4⟩ :=
      step_ro_call (by decide) hs3_c hs3_lf hr3
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hr4
    have hs4_endp : s4.locals.lookup (ofString "endp") = some (.val (.word endpw)) := by
      rw [hs4_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
    have hcmp_endp : @evalHOLExact 64 F _ s4.toExact (fun x => Classical.propDecidable (s4.memaddrs x))
        (.cmp .equal (.var .local (ofString "endp")) (.const 18446744073709551615#64)) =
        some (.val (.word (if endpw = 18446744073709551615#64 then (1#64 : BitVec 64) else 0#64))) := by
      simp [evalHOLExact, hs4_endp, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    rw [hcmp_endp] at hr4; dsimp only at hr4
    by_cases hendp : endpw = 18446744073709551615#64
    · rw [if_pos hendp] at hr4; rw [if_neg h10] at hr4; rw [hret_rstruct s4 18446744073709551615#64 0#64] at hr4
      injection hr4 with h1; injection h1 with hv
      exact ⟨18446744073709551615#64, 0#64, hv.symm, Or.inl rfl⟩
    · rw [if_neg hendp] at hr4; rw [if_pos h00] at hr4; rw [evaluateHOLFiniteState_skip] at hr4; dsimp only at hr4
      rw [evaluateHOLFiniteState_dec_total] at hr4; dsimp only at hr4
      rcases hld_cur : @evalHOLExact 64 F _ s4.toExact (fun x => Classical.propDecidable (s4.memaddrs x))
          (.load .one (.op .add [.var .global (ofString "ev"), .const 32#64])) with _ | curv
      · rw [hld_cur] at hr4; simp at hr4
      · obtain ⟨curw, rfl, hcurw_nat⟩ := evalAt_loadG_word s4 "ev" 32#64 curv hld_cur
        rw [hld_cur] at hr4; dsimp only at hr4
        have hsh_cur : shapeEqHOL .one (shapeOfHOLExact (.val (.word curw))) = true := by
          simp [shapeEqHOL, shapeOfHOLExact]
        rw [if_pos hsh_cur] at hr4; dsimp only at hr4
        have hs4_mem : s4.memory = s.memory := by unfold LocFrame at hs4_lf; conv_lhs => rw [hs4_lf]
        have hs4_glob : s4.globals = s.globals := by unfold LocFrame at hs4_lf; conv_lhs => rw [hs4_lf]
        have hcur_eq : curw.toNat = memW s (globN s "ev" + 32) := by
          have h32 : (32#64 : BitVec 64).toNat = 32 := rfl
          rw [hcurw_nat, h32]
          simp [memW, globN, hs4_mem, hs4_glob]
        set s5 := setVarHOLFinite (ofString "cur") (.val (.word curw)) s4 with hs5_def
        have hs5_c : s5.code = originalRuntimeCode := hs4_c
        have hs5_lf : LocFrame s s5 := hs4_lf.with_locals_clock _ s4.clock
        have hs5_cur : s5.locals.lookup (ofString "cur") = some (.val (.word curw)) := by
          simp [hs5_def, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        obtain ⟨befw, s6, hs6_c, hs6_lf, hs6_loc, ⟨vals6, body6, cal6, rs6, hargs6, hl6, hrun6⟩, hr6⟩ :=
          step_ro_call (by decide) hs5_c hs5_lf hr4
        have hvals6 : vals6 = [.val (.word curw)] := by
          simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hs5_cur] at hargs6
          exact hargs6.symm
        subst hvals6
        obtain ⟨rfl, rfl, curw', hcur_inj, hcal6_v⟩ := one_word_arg_lookup lookup_ceil32 hl6
        injection hcur_inj with hcur_inj'; injection hcur_inj' with hcur_inj''; subst hcur_inj''
        have hbef_ex := ceil32_body_exact (callEntryStateHOLFinite s5 cal6) hs5_c hcal6_v
          (.val (.word befw)) hrun6
        obtain ⟨befw', hbef_inj, hbef_lo, hbef_hi⟩ := hbef_ex
        injection hbef_inj with hbef_inj'; injection hbef_inj' with hbef_inj''; subst hbef_inj''
        have hs6_endp : s6.locals.lookup (ofString "endp") = some (.val (.word endpw)) := by
          rw [hs6_loc]; simp [hs5_def, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs4_endp,
            show ofString "before" ≠ ofString "endp" by decide,
            show ofString "cur" ≠ ofString "endp" by decide]
        obtain ⟨aftw, s7, hs7_c, hs7_lf, hs7_loc, ⟨vals7, body7, cal7, rs7, hargs7, hl7, hrun7⟩, hr7⟩ :=
          step_ro_call (by decide) hs6_c hs6_lf hr6
        have hvals7 : vals7 = [.val (.word endpw)] := by
          simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hs6_endp] at hargs7
          exact hargs7.symm
        subst hvals7
        obtain ⟨rfl, rfl, endpw', hendp_inj, hcal7_v⟩ := one_word_arg_lookup lookup_ceil32 hl7
        injection hendp_inj with hendp_inj'; injection hendp_inj' with hendp_inj''; subst hendp_inj''
        obtain ⟨aftw', haft_inj, haft_lo, haft_hi⟩ := ceil32_body_exact (callEntryStateHOLFinite s6 cal7) hs6_c
          hcal7_v (.val (.word aftw)) hrun7
        injection haft_inj with haft_inj'; injection haft_inj' with haft_inj''; subst haft_inj''
        have hs7_bef : s7.locals.lookup (ofString "before") = some (.val (.word befw)) := by
          rw [hs7_loc, hs6_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "after" ≠ ofString "before" by decide]
        have hs7_aft : s7.locals.lookup (ofString "after") = some (.val (.word aftw)) := by
          rw [hs7_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hr7
        have hcmp_ba : @evalHOLExact 64 F _ s7.toExact (fun x => Classical.propDecidable (s7.memaddrs x))
            (.cmp .notLower (.var .local (ofString "before")) (.var .local (ofString "after"))) =
            some (.val (.word (if ¬ (befw < aftw) then (1#64 : BitVec 64) else 0#64))) := by
          simp [evalHOLExact, hs7_bef, hs7_aft, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
        rw [hcmp_ba] at hr7; dsimp only at hr7
        by_cases hba : ¬ (befw < aftw)
        · rw [if_pos hba] at hr7; rw [if_neg h10] at hr7; rw [hret_rstruct s7 0#64 0#64] at hr7
          injection hr7 with h1; injection h1 with hv
          exact ⟨0#64, 0#64, hv.symm, Or.inl rfl⟩
        · rw [if_neg hba] at hr7; rw [if_pos h00] at hr7; rw [evaluateHOLFiniteState_skip] at hr7; dsimp only at hr7
          have hba_lt : befw.toNat < aftw.toNat := BitVec.lt_def.1 (Classical.not_not.1 hba)
          obtain ⟨caw, s8, hs8_c, hs8_lf, hs8_loc, ⟨vals8, body8, cal8, rs8, hargs8, hl8, hrun8⟩, hr8⟩ :=
            step_ro_call (by decide) hs7_c hs7_lf hr7
          have hvals8 : vals8 = [.val (.word aftw)] := by
            simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hs7_aft] at hargs8
            exact hargs8.symm
          subst hvals8
          obtain ⟨rfl, rfl, aftw_arg, haft_arg_inj, hcal8_sz⟩ := one_word_arg_lookup lookup_memory_gas_cost hl8
          injection haft_arg_inj with h1; injection h1 with h2; subst h2
          obtain ⟨cbw, s9, hs9_c, hs9_lf, hs9_loc, _, hr9⟩ :=
            step_ro_call (by decide) hs8_c hs8_lf hr8
          have hs9_ca : s9.locals.lookup (ofString "ca") = some (.val (.word caw)) := by
            rw [hs9_loc, hs8_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "cb" ≠ ofString "ca" by decide]
          have hs9_cb : s9.locals.lookup (ofString "cb") = some (.val (.word cbw)) := by
            rw [hs9_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
          have hs9_bef : s9.locals.lookup (ofString "before") = some (.val (.word befw)) := by
            rw [hs9_loc, hs8_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs7_bef,
              show ofString "cb" ≠ ofString "before" by decide,
              show ofString "ca" ≠ ofString "before" by decide]
          have hs9_aft : s9.locals.lookup (ofString "after") = some (.val (.word aftw)) := by
            rw [hs9_loc, hs8_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs7_aft,
              show ofString "cb" ≠ ofString "after" by decide,
              show ofString "ca" ≠ ofString "after" by decide]
          rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hr9
          have hcmp_ca : @evalHOLExact 64 F _ s9.toExact (fun x => Classical.propDecidable (s9.memaddrs x))
              (.cmp .equal (.var .local (ofString "ca")) (.const 18446744073709551615#64)) =
              some (.val (.word (if caw = 18446744073709551615#64 then (1#64 : BitVec 64) else 0#64))) := by
            simp [evalHOLExact, hs9_ca, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
          rw [hcmp_ca] at hr9; dsimp only at hr9
          by_cases hca_max : caw = 18446744073709551615#64
          · rw [if_pos hca_max] at hr9; rw [if_neg h10] at hr9; rw [hret_rstruct s9 18446744073709551615#64 0#64] at hr9
            injection hr9 with h1; injection h1 with hv
            exact ⟨18446744073709551615#64, 0#64, hv.symm, Or.inl rfl⟩
          · rw [if_neg hca_max] at hr9; rw [if_pos h00] at hr9; rw [evaluateHOLFiniteState_skip] at hr9; dsimp only at hr9
            rw [evaluateHOLFiniteState_return] at hr9
            have hev_ret : @evalHOLExact 64 F _ s9.toExact (fun x => Classical.propDecidable (s9.memaddrs x))
                (.rstruct
                  [.op .sub [.var .local (ofString "ca"), .var .local (ofString "cb")],
                   .op .sub [.var .local (ofString "after"), .var .local (ofString "before")]]) =
                some (.rStruct [.val (.word (caw - cbw)), .val (.word (aftw - befw))]) := by
              simp [evalHOLExact, evalListHOLExact, hs9_ca, hs9_cb, hs9_aft, hs9_bef,
                wordOpHOL, wordOp, valueIsWord, valueWord]
            rw [hev_ret] at hr9; dsimp only at hr9
            have hsz : sizeOfShapeWithContextHOL s9.structs
                (shapeOfHOLExact (.rStruct [.val (.word (caw - cbw)), .val (.word (aftw - befw))] : ValueHOL 64)) ≤ 32 := by
              simp [shapeOfHOLExact, sizeOfShapeWithContextHOL, sizeOfShapesWithContextHOL]
            rw [if_pos hsz] at hr9; dsimp only at hr9
            injection hr9 with h1; injection h1 with hv
            have haft_lt37 : aftw.toNat < 2 ^ 37 := by
              by_contra hge
              have hca_eq := memory_gas_cost_ge_twoPow37 (callEntryStateHOLFinite s7 cal8)
                (Nat.le_of_not_lt hge) hs7_c hcal8_sz (.val (.word caw)) hrun8
              injection hca_eq with h1; injection h1 with h2
              exact hca_max h2
            have hendp_le : endpw.toNat ≤ 2 ^ 64 - 32 := by
              by_contra hgt
              have haft_max_nat := haft_hi (by omega)
              omega
            have haft_eq := haft_lo hendp_le
            have haft_mod : aftw.toNat % 32 = 0 := by omega
            have hcur_le : curw.toNat ≤ 2 ^ 64 - 32 := by
              by_contra hgt
              have := hbef_hi (by omega)
              omega
            have hbef_eq := hbef_lo hcur_le
            have hsub_nat : (aftw - befw).toNat = aftw.toNat - befw.toNat :=
              BitVec.toNat_sub_of_le (BitVec.le_def.2 (Nat.le_of_lt hba_lt))
            refine ⟨caw - cbw, aftw - befw, hv.symm, Or.inr ⟨befw.toNat, aftw.toNat, haft_lt37, haft_mod, hba_lt, hsub_nat, ?_⟩⟩
            intro hcur_al
            rw [← hcur_eq] at hcur_al ⊢
            omega

theorem eps_extend_memory_cost1_bounds :
    EvmPreservingSpec (fun _ => True)
      (fun s v post =>
        LocFrame s post ∧
        ∃ cw ebw : BitVec 64,
          v = .rStruct [.val (.word cw), .val (.word ebw)] ∧
          (ebw = 0#64 ∨
            ∃ before after : Nat,
              after < 2 ^ 37 ∧
              after % 32 = 0 ∧
              before < after ∧
              ebw.toNat = after - before ∧
              (memW s (globN s "ev" + 32) % 32 = 0 → before = memW s (globN s "ev" + 32))))
      (ofString "extend_memory_cost1") := by
  obtain ⟨params, body, retShape, hlk, hro⟩ := eps_extend_memory_cost1
  have hlk_eq := lookup_extend_memory_cost1.symm.trans hlk
  injection hlk_eq with hprod
  rcases Prod.mk.inj hprod with ⟨rfl, hprod2⟩
  rcases Prod.mk.inj hprod2 with ⟨hbody_eq, rfl⟩
  subst hbody_eq
  refine ⟨_, _, _, lookup_extend_memory_cost1, ?_⟩
  intro F s hcode hInv hP hlookup hnt
  have hs := hro s hcode hInv hP hlookup hnt
  dsimp only at hs ⊢
  refine ⟨fun v hv => ?_, hs.2⟩
  obtain ⟨h1, h2, h3, hlf⟩ := hs.1 v hv
  exact ⟨h1, h2, h3, hlf, extend_memory_cost1_body_bounds s hcode v hv⟩

theorem extend_memory_cost1_aligned_growth {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hcode : s.code = originalRuntimeCode)
    (hal : memW s (globN s "ev" + 32) % 32 = 0)
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_extend_memory_cost1)).1 =
      some (.returned v)) :
    ∃ cw ebw : BitVec 64,
      v = .rStruct [.val (.word cw), .val (.word ebw)] ∧
      (ebw = 0#64 ∨
        (memW s (globN s "ev" + 32) + ebw.toNat < 2 ^ 37 ∧
          (memW s (globN s "ev" + 32) + ebw.toNat) % 32 = 0)) := by
  obtain ⟨cw, ebw, hv, hz | ⟨before, after, hb, ha, hlt, he, hbefore⟩⟩ :=
    extend_memory_cost1_body_bounds s hcode v hret
  · exact ⟨cw, ebw, hv, Or.inl hz⟩
  · have hbefore_eq := hbefore hal
    have hsum : memW s (globN s "ev" + 32) + ebw.toNat = after := by omega
    exact ⟨cw, ebw, hv, Or.inr ⟨hsum ▸ hb, hsum ▸ ha⟩⟩

end Group10

theorem lookup_is_valid_delegation :
    originalRuntimeCode.lookup (ofString "is_valid_delegation") =
      some ([(ofString "code", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_is_valid_delegation, .one) :=
  lookup_of_guestAst_getElem 446 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_is_valid_delegation) rfl

theorem eps_is_valid_delegation :
    EvmPreservingSpec (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "is_valid_delegation") :=
  eps_of_readOnly 446 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_is_valid_delegation rfl
    opRoCallees opRoCallees_good (by decide)

theorem lookup_calculate_message_call_gas :
    originalRuntimeCode.lookup (ofString "calculate_message_call_gas") =
      some ([(ofString "value", .comb [.one, .one, .one, .one]),
        (ofString "gas", .one), (ofString "gas_left", .one),
        (ofString "memory_cost", .one), (ofString "extra_gas", .one)],
        sourceFnBody Guest.Software.guestFn_calculate_message_call_gas, .comb [.one, .one]) :=
  lookup_of_guestAst_getElem 602 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_calculate_message_call_gas) rfl

theorem eps_calculate_message_call_gas :
    EvmPreservingSpec (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "calculate_message_call_gas") :=
  eps_of_readOnly 602 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_calculate_message_call_gas rfl
    opRoCallees opRoCallees_good (by decide)

theorem lookup_extend_memory_cost2 :
    originalRuntimeCode.lookup (ofString "extend_memory_cost2") =
      some ([(ofString "s1", .comb [.one, .one, .one, .one]),
             (ofString "n1", .comb [.one, .one, .one, .one]),
             (ofString "s2", .comb [.one, .one, .one, .one]),
             (ofString "n2", .comb [.one, .one, .one, .one])],
        sourceFnBody Guest.Software.guestFn_extend_memory_cost2, .comb [.one, .one]) :=
  lookup_of_guestAst_getElem 459 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_extend_memory_cost2) rfl

theorem extend_memory_cost1_locFrame_of_resumes {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode)
    (hres : Resumes (evaluateHOLFiniteState s
      (sourceFnBody Guest.Software.guestFn_extend_memory_cost1)).1) :
    LocFrame s (evaluateHOLFiniteState s
      (sourceFnBody Guest.Software.guestFn_extend_memory_cost1)).2 := by
  exact (evaluate_readOnlyProg opRoCallees opRoCallees_good
    (sourceFnBody Guest.Software.guestFn_extend_memory_cost1) (by decide) s hcode).to_resumes hres

theorem lookup_set_retdata :
    originalRuntimeCode.lookup (ofString "set_retdata") =
      some ([(ofString "p", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_set_retdata, .one) :=
  lookup_of_guestAst_getElem 595 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_set_retdata) rfl

theorem lookup_compute_contract_address :
    originalRuntimeCode.lookup (ofString "compute_contract_address") =
      some ([(ofString "addr", .one), (ofString "nonce", .one), (ofString "out", .one)],
        sourceFnBody Guest.Software.guestFn_compute_contract_address, .one) :=
  lookup_of_guestAst_getElem 596 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_compute_contract_address) rfl

theorem lookup_compute_create2_contract_address :
    originalRuntimeCode.lookup (ofString "compute_create2_contract_address") =
      some ([(ofString "addr", .one), (ofString "salt", .one),
        (ofString "code", .one), (ofString "n", .one), (ofString "out", .one)],
        sourceFnBody Guest.Software.guestFn_compute_create2_contract_address, .one) :=
  lookup_of_guestAst_getElem 597 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_compute_create2_contract_address) rfl

def HeadSafeAddr (e0 c0 a : Nat) : Prop :=
  (∃ k, a = e0 + k ∧ k < 280 ∧ k ≠ 24 ∧ k ≠ 32 ∧ k ≠ 40) ∨
  (∃ k, a = c0 + k ∧ k < 104 ∧ k ≠ 56)

theorem headMemChainWF_of_headSafe {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hE : EvmInv s) (hs : Group10.HeadMemChainWF s)
    (hchain : evmChain post = evmChain s)
    (hev : globN post "ev" = globN s "ev")
    (hfmp : globN post "frame_mem_ptr" = globN s "frame_mem_ptr")
    (hmem_out : ∀ x : BitVec 64,
      ¬ HeadSafeAddr (globN s "ev") (globN s "cur_cont") x.toNat →
      post.memory x = s.memory x) :
    Group10.HeadMemChainWF post := by
  obtain ⟨_, S, _, hrest⟩ := hE
  dsimp only at hrest
  obtain ⟨_, _, _, hFWF, _, _, hPair, _⟩ := hrest
  obtain ⟨tl, hcs⟩ : ∃ tl, evmChain s = (globN s "ev", globN s "cur_cont") :: tl :=
    ⟨_, rfl⟩
  have hSE : scratchEnd = 2965299200 := rfl
  have hhead : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by
    rw [hcs]; exact List.mem_cons_self
  have hFW0 := hFWF _ hhead
  have he_in := (hFW0.1 (globN s "ev", 280) (by simp)).1.2
  have hc_in := (hFW0.1 (globN s "cur_cont", 104) (by simp)).1.2
  dsimp only at he_in hc_in
  rw [hcs, List.map_cons, List.flatten_cons, List.pairwise_append] at hPair
  obtain ⟨hP0, _, hcross⟩ := hPair
  have hdec : Disj (globN s "ev", 280) (globN s "cur_cont", 104) := by
    unfold frameObjects at hP0
    exact (List.pairwise_cons.mp (List.pairwise_append.mp hP0).1).1 _ (by simp)
  have hsafe : ∀ a : Nat, a < 2 ^ 64 →
      ¬ HeadSafeAddr (globN s "ev") (globN s "cur_cont") a → memW post a = memW s a := by
    intro a hlt hne
    unfold memW
    rw [hmem_out (BitVec.ofNat 64 a)]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    exact hne
  refine Group10.headMemChainWF_of_agree hs hchain ?_ hev hfmp
  intro ec hec
  rw [hcs] at hec
  rcases List.mem_cons.mp hec with rfl | htl
  · unfold Disj at hdec; dsimp only at hdec
    rw [hSE] at he_in hc_in
    refine ⟨?_, ?_, ?_, ?_⟩ <;> apply hsafe <;> (try dsimp only) <;> (try omega) <;>
      (rintro (⟨k, hk, _⟩ | ⟨k, hk, _⟩) <;> omega)
  · have hFec := hFWF ec (by rw [hcs]; exact List.mem_cons_of_mem _ htl)
    have hr_in := (hFec.1 (ec.1, 280) (by simp)).1.2
    have hk_in := (hFec.1 (ec.2, 104) (by simp)).1.2
    dsimp only at hr_in hk_in
    have hmemb : ∀ o ∈ [(ec.1, 280), (ec.2, 104)],
        o ∈ ((tl.map (frameObjects s)).flatten) := by
      intro o ho
      exact List.mem_flatten.2 ⟨frameObjects s ec, List.mem_map_of_mem htl,
        by unfold frameObjects; simp only [List.mem_cons, List.mem_append] at ho ⊢; tauto⟩
    have hA : (globN s "ev", 280) ∈ frameObjects s (globN s "ev", globN s "cur_cont") := by
      unfold frameObjects; simp
    have hB : (globN s "cur_cont", 104) ∈ frameObjects s (globN s "ev", globN s "cur_cont") := by
      unfold frameObjects; simp
    have d1 := hcross _ hA _ (hmemb (ec.1, 280) (by simp))
    have d2 := hcross _ hB _ (hmemb (ec.1, 280) (by simp))
    have d3 := hcross _ hA _ (hmemb (ec.2, 104) (by simp))
    have d4 := hcross _ hB _ (hmemb (ec.2, 104) (by simp))
    unfold Disj at d1 d2 d3 d4; dsimp only at d1 d2 d3 d4
    rw [hSE] at he_in hc_in hr_in hk_in
    refine ⟨?_, ?_, ?_, ?_⟩ <;> apply hsafe <;> (try omega) <;>
      (rintro (⟨k, hk, _⟩ | ⟨k, hk, _⟩) <;> omega)

theorem headMemChainWF_of_disj_bre {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl}
    (hE : EvmInv s) (hs : Group10.HeadMemChainWF s)
    (hchain : evmChain post = evmChain s)
    (hev : globN post "ev" = globN s "ev")
    (hfmp : globN post "frame_mem_ptr" = globN s "frame_mem_ptr")
    (hRl8 : ∀ i ∈ Rl, i.1 % 8 = 0)
    (hcell : ∀ a : BitVec 64, (∀ i ∈ Rl, ¬ CellHits a.toNat i) → post.memory a = s.memory a)
    (hdj : ∀ ec ∈ evmChain s, ∀ i ∈ Rl,
      (i.2 = 0 ∨ Disj (ec.1, 280) i) ∧ (i.2 = 0 ∨ Disj (ec.2, 104) i)) :
    Group10.HeadMemChainWF post := by
  obtain ⟨hAs, S, _, _, _, _, hFWF, _⟩ := hE
  refine Group10.headMemChainWF_of_agree hs hchain ?_ hev hfmp
  intro ec hec
  have hFW := hFWF ec hec
  obtain ⟨hb1, hb2, _, _⟩ := frameWF_bounds hAs.2 hFW
  have he8 : ec.1 % 8 = 0 := (hFW.1 (ec.1, 280) (by simp)).2.1
  have hc8 : ec.2 % 8 = 0 := (hFW.1 (ec.2, 104) (by simp)).2.1
  have hword1 : ∀ k, k + 8 ≤ 280 → k % 8 = 0 → memW post (ec.1 + k) = memW s (ec.1 + k) := by
    intro k hk hk8
    have hlt : ec.1 + k < 2 ^ 64 := by omega
    unfold memW
    rw [hcell (BitVec.ofNat 64 (ec.1 + k))]
    intro i hi
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    rcases (hdj ec hec i hi).1 with hi0 | hd
    · have hi8 := hRl8 i hi
      intro ⟨h1, h2⟩; omega
    · exact not_cellHits_of_disj_aligned (i := (ec.1, 280)) (by omega) (hRl8 i hi)
        (Nat.le_add_right _ k) (Nat.add_le_add_left hk _) hd
  have hword2 : ∀ k, k + 8 ≤ 104 → k % 8 = 0 → memW post (ec.2 + k) = memW s (ec.2 + k) := by
    intro k hk hk8
    have hlt : ec.2 + k < 2 ^ 64 := by omega
    unfold memW
    rw [hcell (BitVec.ofNat 64 (ec.2 + k))]
    intro i hi
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    rcases (hdj ec hec i hi).2 with hi0 | hd
    · have hi8 := hRl8 i hi
      intro ⟨h1, h2⟩; omega
    · exact not_cellHits_of_disj_aligned (i := (ec.2, 104)) (by omega) (hRl8 i hi)
        (Nat.le_add_right _ k) (Nat.add_le_add_left hk _) hd
  exact ⟨hword1 24 (by omega) (by omega),
    hword1 32 (by omega) (by omega),
    hword1 40 (by omega) (by omega),
    hword2 56 (by omega) (by omega)⟩

theorem headMemChainWF_store_headSafe {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hE : EvmInv s) (hs : Group10.HeadMemChainWF s) {x : BitVec 64}
    (hx : HeadSafeAddr (globN s "ev") (globN s "cur_cont") x.toNat)
    (hglob : post.globals = s.globals)
    (hchain : evmChain post = evmChain s)
    (hmem : ∀ a : BitVec 64, a ≠ x → post.memory a = s.memory a) :
    Group10.HeadMemChainWF post :=
  headMemChainWF_of_headSafe hE hs hchain
    (congrFun (globN_congr hglob) "ev") (congrFun (globN_congr hglob) "frame_mem_ptr")
    (fun a ha => hmem a (fun h => ha (h ▸ hx)))

theorem headMemChainWF_of_locFrame {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hs : Group10.HeadMemChainWF s) (h : LocFrame s post) :
    Group10.HeadMemChainWF post :=
  (Group10.headMemChainWF_congr (by unfold LocFrame at h; rw [h])
    (by unfold LocFrame at h; rw [h])).2 hs

theorem headMemChainWF_of_byteRegionEffect {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl}
    (hE : EvmInv s) (hs : Group10.HeadMemChainWF s)
    (hchain : evmChain post = evmChain s)
    (heff : ByteRegionEffect s post Rl)
    (hRl8 : ∀ i ∈ Rl, i.1 % 8 = 0)
    (hdj : ∀ ec ∈ evmChain s, ∀ i ∈ Rl,
      (i.2 = 0 ∨ Disj (ec.1, 280) i) ∧ (i.2 = 0 ∨ Disj (ec.2, 104) i)) :
    Group10.HeadMemChainWF post :=
  headMemChainWF_of_disj_bre hE hs hchain
    (congrFun (globN_congr heff.globals) "ev")
    (congrFun (globN_congr heff.globals) "frame_mem_ptr")
    hRl8 heff.cell_frame hdj

theorem headMemChainWF_of_scratchByteEff {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl}
    (hE : EvmInv s) (hs : Group10.HeadMemChainWF s)
    (hchain : evmChain post = evmChain s)
    (heff : ScratchByteEff s post Rl)
    (hRl8 : ∀ i ∈ Rl, i.1 % 8 = 0)
    (hdj : ∀ ec ∈ evmChain s, ∀ i ∈ Rl,
      (i.2 = 0 ∨ Disj (ec.1, 280) i) ∧ (i.2 = 0 ∨ Disj (ec.2, 104) i)) :
    Group10.HeadMemChainWF post :=
  headMemChainWF_of_disj_bre hE hs hchain
    (OpHandlers.globN_eq_of_lookup_eq (heff.glob_other "ev" (by decide)))
    (OpHandlers.globN_eq_of_lookup_eq (heff.glob_other "frame_mem_ptr" (by decide)))
    hRl8 heff.cell_frame hdj

local notation "evmR" => R11Shards.OpDispatchSpec.evmR

def EvmPreservingSpecA
    (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (Qret : ∀ {F : Type}, PanSemStateFiniteExact 64 F → ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop)
    (fname : MlS) : Prop :=
  ∃ (params : List (MlS × ShapeHOL)) (body : ProgHOL 64) (retShape : ShapeHOL),
    originalRuntimeCode.lookup fname = some (params, body, retShape) ∧
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode →
      EvmInv s → Group10.HeadMemChainWF s → P s →
      (∃ values, lookupCodeHOLFinite originalRuntimeCode.lookup fname values =
        some (body, s.locals, retShape)) →
      (evaluateHOLFiniteState s body).1 ≠ some .timeOut →
      let r := (evaluateHOLFiniteState s body).1
      let post := (evaluateHOLFiniteState s body).2
      (∀ v, r = some (.returned v) →
        (EvmInv post ∧ Group10.HeadMemChainWF post) ∧
          evmChain post = evmChain s ∧ evmR post ≤ evmR s ∧ Qret s v post) ∧
      (IsEvmErr r → (EvmInv post ∧ Group10.HeadMemChainWF post) ∧
        evmChain post = evmChain s ∧ evmR post ≤ evmR s)

def OpDispatchPostA {F : Type} (s : PanSemStateFiniteExact 64 F)
    (r : Option (PanSemResultExact 64)) (post : PanSemStateFiniteExact 64 F) : Prop :=
  ((∃ v, r = some (.returned v)) →
    (EvmInv post ∧ Group10.HeadMemChainWF post) ∧ evmPot post < evmPot s) ∧
  (IsEvmErr r → (EvmInv post ∧ Group10.HeadMemChainWF post) ∧
    (evmChain post).length = (evmChain s).length ∧ evmR post ≤ evmR s)

def OpHandlerSpecA (fname : MlS) : Prop :=
  FunSpec (fun s => EvmInv s ∧ Group10.HeadMemChainWF s ∧ ¬ EvmDone s)
    OpDispatchPostA fname

def HandlerRunA {F : Type} (s0 : PanSemStateFiniteExact 64 F)
    (P : PanSemStateFiniteExact 64 F → Prop) (charged : Bool)
    (prog : ProgHOL 64) : Prop :=
  ∀ (t : PanSemStateFiniteExact 64 F), t.code = originalRuntimeCode →
    EvmInv t → Group10.HeadMemChainWF t →
    (evmChain t).length = (evmChain s0).length →
    (if charged then evmR t < evmR s0 else evmR t ≤ evmR s0) → P t →
    (evaluateHOLFiniteState t prog).1 ≠ some .timeOut →
    OpDispatchPostA s0 (evaluateHOLFiniteState t prog).1 (evaluateHOLFiniteState t prog).2

theorem opDispatchPostA_to_standard {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {r : Option (PanSemResultExact 64)} (h : OpDispatchPostA s r post) :
    OpDispatchPost s r post :=
  ⟨fun hr => ⟨(h.1 hr).1.1, (h.1 hr).2⟩,
    fun he => ⟨(h.2 he).1.1, (h.2 he).2⟩⟩

theorem epsA_of_readOnly (i : Nat) (hi : i < Guest.Software.guestAst.length)
    (d : Decl (BitVec 64)) (hd : Guest.Software.guestAst[i] = .function (extractFn d))
    (good : MlS → Bool)
    (hgood : ∀ function, good function = true → ∀ values body callee rs,
      PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup function values =
        some (body, callee, rs) → readOnlyProg good body = true)
    (hbody : readOnlyProg good
      (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural (extractFn d).body) = true) :
    EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString (extractFn d).name) := by
  refine ⟨_, _, _, lookup_of_guestAst_getElem i hi (extractFn d) hd, ?_⟩
  intro F s hcode hInv hWF _ _ _
  have hsafe := evaluate_readOnlyProg good hgood _ hbody s hcode
  have hres (hr : Resumes (evaluateHOLFiniteState s
      (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural (extractFn d).body)).1) :
      let post := (evaluateHOLFiniteState s
        (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural (extractFn d).body)).2
      (EvmInv post ∧ Group10.HeadMemChainWF post) ∧
        evmChain post = evmChain s ∧ evmR post ≤ evmR s ∧ LocFrame s post := by
    have hlf := hsafe.to_resumes hr
    dsimp only
    let post := (evaluateHOLFiniteState s
      (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural (extractFn d).body)).2
    have hInv_p : EvmInv post := by
      have h := localsFree_evmInv s post.locals post.clock hInv
      rwa [← hlf] at h
    have hm : post.memory = s.memory := by
      change (evaluateHOLFiniteState s
        (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural (extractFn d).body)).2.memory = s.memory
      conv_lhs => rw [hlf]
    have hg : post.globals = s.globals := by
      change (evaluateHOLFiniteState s
        (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural (extractFn d).body)).2.globals = s.globals
      conv_lhs => rw [hlf]
    have hc := evm_congr hm hg
    exact ⟨⟨hInv_p, headMemChainWF_of_locFrame hWF hlf⟩,
      evmChain_congr hm hg, le_of_eq hc.2.1, hlf⟩
  refine ⟨fun v hv => hres (Or.inl ⟨v, hv⟩), fun ⟨v, hv⟩ => ?_⟩
  obtain ⟨h1, h2, h3, _⟩ := hres (Or.inr ⟨_, v, hv, by decide⟩)
  exact ⟨h1, h2, h3⟩

theorem epsA_is_valid_delegation :
    EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "is_valid_delegation") :=
  epsA_of_readOnly 446 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_is_valid_delegation rfl
    opRoCallees opRoCallees_good rfl

theorem epsA_calculate_message_call_gas :
    EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "calculate_message_call_gas") :=
  epsA_of_readOnly 602 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_calculate_message_call_gas rfl
    opRoCallees opRoCallees_good rfl

theorem epsA_is_warm_address :
    EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "is_warm_address") :=
  epsA_of_readOnly 471 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_is_warm_address rfl
    opRoCallees opRoCallees_good rfl

theorem epsA_access_gas_cost :
    EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "access_gas_cost") :=
  epsA_of_readOnly 473 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_access_gas_cost rfl
    opRoCallees opRoCallees_good rfl

theorem epsA_words_of :
    EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "words_of") :=
  epsA_of_readOnly 443 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_words_of rfl
    opRoCallees opRoCallees_good rfl

theorem epsA_sat_word :
    EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "sat_word") :=
  epsA_of_readOnly 440 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_sat_word rfl
    opRoCallees opRoCallees_good rfl

theorem epsA_add_sat :
    EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "add_sat") :=
  epsA_of_readOnly 441 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_add_sat rfl
    opRoCallees opRoCallees_good rfl

theorem epsA_u256_is_zero :
    EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "u256_is_zero") :=
  epsA_of_readOnly 42 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_is_zero rfl
    opRoCallees opRoCallees_good rfl

theorem epsA_u256_lt :
    EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "u256_lt") :=
  epsA_of_readOnly 46 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_lt rfl
    opRoCallees opRoCallees_good rfl

theorem epsA_u256_fits_word :
    EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "u256_fits_word") :=
  epsA_of_readOnly 41 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_fits_word rfl
    opRoCallees opRoCallees_good rfl

theorem epsA_u256_low :
    EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "u256_low") :=
  epsA_of_readOnly 40 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_low rfl
    opRoCallees opRoCallees_good rfl

theorem epsA_u256_from_word :
    EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "u256_from_word") :=
  epsA_of_readOnly 39 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_u256_from_word rfl
    opRoCallees opRoCallees_good rfl

theorem epsA_address_to_u256 :
    EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "address_to_u256") :=
  epsA_of_readOnly 445 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_address_to_u256 rfl
    opRoCallees opRoCallees_good rfl

theorem epsA_extend_memory_cost1 :
    EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "extend_memory_cost1") :=
  epsA_of_readOnly 458 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_extend_memory_cost1 rfl
    opRoCallees opRoCallees_good rfl

theorem opDispatchPostA_error {F : Type} (s post : PanSemStateFiniteExact 64 F) :
    OpDispatchPostA s (some .error) post := by
  constructor
  · rintro ⟨_, h⟩; cases h
  · rintro ⟨_, h⟩; cases h

theorem opDispatchPostA_congr_lc {F : Type}
    {s post post' : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    (hlc : post' = { post with locals := post'.locals, clock := post'.clock })
    (h : OpDispatchPostA s r post) : OpDispatchPostA s r post' := by
  have hm : post'.memory = post.memory := by rw [hlc]
  have hg : post'.globals = post.globals := by rw [hlc]
  have hc := evm_congr hm hg
  have hInv (hi : EvmInv post) : EvmInv post' := by
    rw [hlc]; exact localsFree_evmInv post _ _ hi
  constructor
  · intro hr
    obtain ⟨⟨hi, hw⟩, hp⟩ := h.1 hr
    refine ⟨⟨hInv hi, (Group10.headMemChainWF_congr hm hg).2 hw⟩, ?_⟩
    rw [hc.1]; exact hp
  · intro he
    obtain ⟨⟨hi, hw⟩, hl, hR⟩ := h.2 he
    refine ⟨⟨hInv hi, (Group10.headMemChainWF_congr hm hg).2 hw⟩,
      hc.2.2.1.trans hl, ?_⟩
    rw [hc.2.1]; exact hR

theorem HandlerRunA.weaken {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {P Q : PanSemStateFiniteExact 64 F → Prop} {charged : Bool} {prog : ProgHOL 64}
    (himp : ∀ t, EvmInv t → P t → Q t) (h : HandlerRunA s0 Q charged prog) :
    HandlerRunA s0 P charged prog :=
  fun t hc hi hw hl hR hp hn => h t hc hi hw hl hR (himp t hi hp) hn

theorem HandlerRunA.ret {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {P : PanSemStateFiniteExact 64 F → Prop} (e : ExpHOL 64) :
    HandlerRunA s0 P true (.return e) := by
  intro t _ hi hw _ hR _ _
  simp only [↓reduceIte] at hR
  rw [evaluateHOLFiniteState_return]
  split
  · exact opDispatchPostA_error s0 t
  · split
    · have hi' := localsFree_evmInv t (emptyLocalsHOLFinite t).locals t.clock hi
      have hw' := Group10.headMemChainWF_locals t (emptyLocalsHOLFinite t).locals t.clock hw
      have hc := evm_congr (s := t) (t := emptyLocalsHOLFinite t) rfl rfl
      refine ⟨fun _ => ⟨⟨hi', hw'⟩, evmPot_lt_of_evmR_lt hi' ?_⟩, ?_⟩
      · rw [hc.2.1]; exact hR
      · rintro ⟨_, h⟩; cases h
    · exact opDispatchPostA_error s0 t

theorem HandlerRunA.ite {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {P : PanSemStateFiniteExact 64 F → Prop} {charged : Bool}
    {cond : ExpHOL 64} {yes no : ProgHOL 64}
    (hyes : HandlerRunA s0 (fun t => P t ∧
      ∃ w : BitVec 64, @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) cond = some (.val (.word w)) ∧ w ≠ 0) charged yes)
    (hno : HandlerRunA s0 (fun t => P t ∧
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) cond = some (.val (.word 0))) charged no) :
    HandlerRunA s0 P charged (.ite cond yes no) := by
  intro t hc hi hw hl hR hp hn
  rw [evaluateHOLFiniteState_ite] at hn ⊢
  revert hn
  split
  · rename_i w he
    by_cases hz : w = 0
    · subst hz; simp only [↓reduceIte]
      intro hn; exact hno t hc hi hw hl hR ⟨hp, he⟩ hn
    · simp only [hz, ↓reduceIte]
      intro hn; exact hyes t hc hi hw hl hR ⟨hp, w, he, hz⟩ hn
  · intro _; exact opDispatchPostA_error s0 t

theorem HandlerRunA.seq_skip {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {P : PanSemStateFiniteExact 64 F → Prop} {charged : Bool} {cont : ProgHOL 64}
    (hcont : HandlerRunA s0 P charged cont) :
    HandlerRunA s0 P charged (.seq .skip cont) := by
  intro t hc hi hw hl hR hp hn
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_skip] at hn ⊢
  exact hcont t hc hi hw hl hR hp hn

theorem opDispatchPostA_other {F : Type} {s t : PanSemStateFiniteExact 64 F}
    {r : Option (PanSemResultExact 64)}
    (hnret : ∀ v, r ≠ some (.returned v)) (hnerr : ¬ IsEvmErr r) :
    OpDispatchPostA s r t :=
  ⟨fun ⟨v, hv⟩ => (hnret v hv).elim, fun he => (hnerr he).elim⟩

private theorem rboundA_step {charged : Bool} {r1 r2 r0 : Nat}
    (h1 : r2 ≤ r1) (h2 : if charged then r1 < r0 else r1 ≤ r0) :
    if charged then r2 < r0 else r2 ≤ r0 := by
  cases charged <;> simp only [↓reduceIte, Bool.false_eq_true] at h2 ⊢ <;> omega

private theorem rboundA_to_le {charged : Bool} {r1 r0 : Nat}
    (h : if charged then r1 < r0 else r1 ≤ r0) : r1 ≤ r0 := by
  cases charged <;> simp only [↓reduceIte, Bool.false_eq_true] at h <;> omega

theorem opHandlerSpecA_of_run (idx : Nat) (hidx : idx < Guest.Software.guestAst.length)
    (d : Decl (BitVec 64)) (hd : Guest.Software.guestAst[idx] = .function (extractFn d))
    (hrun : ∀ {F : Type} (s0 : PanSemStateFiniteExact 64 F),
      EvmInv s0 → Group10.HeadMemChainWF s0 → ¬ EvmDone s0 →
      HandlerRunA s0 (fun _ => True) false
        (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural (extractFn d).body)) :
    OpHandlerSpecA (ofString (extractFn d).name) := by
  refine ⟨_, _, _, lookup_of_guestAst_getElem idx hidx (extractFn d) hd, ?_⟩
  intro F s0 hcode ⟨hInv, hWF, hnd⟩ _ hnt
  exact hrun s0 hInv hWF hnd s0 hcode hInv hWF rfl (le_refl _) trivial hnt

theorem HandlerRunA.raise_evmErr {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {P : PanSemStateFiniteExact 64 F → Prop} {charged : Bool} (e : ExpHOL 64) :
    HandlerRunA s0 P charged (.raise (ofString "EvmErr") e) := by
  intro t _ hi hw hlen hR _ _
  have hR_le : evmR t ≤ evmR s0 := rboundA_to_le hR
  rw [evaluateHOLFiniteState_raise]
  split
  · dsimp only
    split
    · have hi' := localsFree_evmInv t (emptyLocalsHOLFinite t).locals t.clock hi
      have hw' := Group10.headMemChainWF_locals t (emptyLocalsHOLFinite t).locals t.clock hw
      have hc := evm_congr (s := t) (t := emptyLocalsHOLFinite t) rfl rfl
      refine ⟨?_, fun _ => ⟨⟨hi', hw'⟩, by rw [hc.2.2.1]; exact hlen, by rw [hc.2.1]; exact hR_le⟩⟩
      rintro ⟨_, h⟩; cases h
    · exact opDispatchPostA_error s0 t
  · exact opDispatchPostA_error s0 t

theorem HandlerRunA.dec {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {P Q : PanSemStateFiniteExact 64 F → Prop} {charged : Bool}
    {nm : MlS} {sh : ShapeHOL} {init : ExpHOL 64} {body : ProgHOL 64}
    (hinit : ∀ t v,
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) init = some v →
      EvmInv t → P t → Q (setVarHOLFinite nm v t))
    (hbody : HandlerRunA s0 Q charged body) :
    HandlerRunA s0 P charged (.dec nm sh init body) := by
  intro t hc hi hw hlen hR hp hn
  rw [evaluateHOLFiniteState_dec_total] at hn ⊢
  dsimp only at hn ⊢
  revert hn
  split
  · intro _; exact opDispatchPostA_error s0 t
  · rename_i v hv
    split
    · intro hn
      let t1 := setVarHOLFinite nm v t
      have hi1 : EvmInv t1 := localsFree_evmInv t t1.locals t.clock hi
      have hw1 : Group10.HeadMemChainWF t1 := Group10.headMemChainWF_locals t t1.locals t.clock hw
      have hc1 := evm_congr (s := t) (t := t1) rfl rfl
      have hR1 : if charged then evmR t1 < evmR s0 else evmR t1 ≤ evmR s0 := by
        rw [hc1.2.1]; exact hR
      have hb := hbody t1 hc hi1 hw1 (hc1.2.2.1.trans hlen) hR1 (hinit t v hv hi hp) hn
      exact opDispatchPostA_congr_lc rfl hb
    · intro _; exact opDispatchPostA_error s0 t

theorem HandlerRunA.seq_assign_local {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {P Q : PanSemStateFiniteExact 64 F → Prop} {charged : Bool}
    {nm : MlS} {exp : ExpHOL 64} {cont : ProgHOL 64}
    (hasgn : ∀ t v,
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) exp = some v →
      EvmInv t → P t → Q (setKvarHOLFinite .local nm v t))
    (hcont : HandlerRunA s0 Q charged cont) :
    HandlerRunA s0 P charged (.seq (.assign .local nm exp) cont) := by
  intro t hc hi hw hlen hR hp hn
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign] at hn ⊢
  revert hn
  split
  · intro _; exact opDispatchPostA_error s0 t
  · rename_i v hv
    split
    · dsimp only; intro hn
      let t1 := setKvarHOLFinite .local nm v t
      have hi1 : EvmInv t1 := localsFree_evmInv t t1.locals t.clock hi
      have hw1 : Group10.HeadMemChainWF t1 := Group10.headMemChainWF_locals t t1.locals t.clock hw
      have hc1 := evm_congr (s := t) (t := t1) rfl rfl
      have hR1 : if charged then evmR t1 < evmR s0 else evmR t1 ≤ evmR s0 := by
        rw [hc1.2.1]; exact hR
      exact hcont t1 hc hi1 hw1 (hc1.2.2.1.trans hlen) hR1 (hasgn t v hv hi hp) hn
    · intro _; exact opDispatchPostA_error s0 t

theorem HandlerRunA.seq_ite_raise_skip {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {P Q : PanSemStateFiniteExact 64 F → Prop} {charged : Bool}
    {cond : ExpHOL 64} {errExp : ExpHOL 64} {cont : ProgHOL 64}
    (hfalse : ∀ t,
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) cond = some (.val (.word 0)) →
      EvmInv t → P t → Q t)
    (hcont : HandlerRunA s0 Q charged cont) :
    HandlerRunA s0 P charged (.seq (.ite cond (.raise (ofString "EvmErr") errExp) .skip) cont) := by
  intro t hc hi hw hlen hR hp hn
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hn ⊢
  revert hn
  split
  · rename_i w he
    by_cases hz : w = 0
    · subst hz; simp only [↓reduceIte, evaluateHOLFiniteState_skip]
      intro hn; exact hcont t hc hi hw hlen hR (hfalse t he hi hp) hn
    · simp only [hz, ↓reduceIte]
      rcases hraise : evaluateHOLFiniteState t (.raise (ofString "EvmErr") errExp) with ⟨rr, sr⟩
      cases rr with
      | none => exact absurd hraise (fun h => raise_ne_none t _ errExp (by rw [h]))
      | some _ =>
        dsimp only; intro hn
        have hr := (HandlerRunA.raise_evmErr (P := P) (charged := charged) errExp) t hc hi hw hlen hR hp
          (by rw [hraise]; exact hn)
        rw [hraise] at hr; exact hr
  · intro _; exact opDispatchPostA_error s0 t

theorem HandlerRunA.decCall {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {P Q : PanSemStateFiniteExact 64 F → Prop}
    {Pc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {Qc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    {charged : Bool}
    {nm : MlS} {sh : ShapeHOL} {fname : MlS} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (hf : EvmPreservingSpecA Pc Qc fname)
    (hentry : ∀ t values body' callee ret',
      t.code = originalRuntimeCode → EvmInv t → Group10.HeadMemChainWF t → P t →
      evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) args = some values →
      lookupCodeHOLFinite t.code.lookup fname values = some (body', callee, ret') →
      Pc (callEntryStateHOLFinite t callee))
    (hstep : ∀ t values body callee retShape v cpost,
      EvmInv t → Group10.HeadMemChainWF t → P t →
      evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) args = some values →
      lookupCodeHOLFinite originalRuntimeCode.lookup fname values = some (body, callee, retShape) →
      EvmInv cpost → Group10.HeadMemChainWF cpost →
      evmChain cpost = evmChain (callEntryStateHOLFinite t callee) →
      Qc (callEntryStateHOLFinite t callee) v cpost →
      Q (setVarHOLFinite nm v { cpost with locals := t.locals }))
    (hcont : HandlerRunA s0 Q charged cont) :
    HandlerRunA s0 P charged (.decCall nm sh fname args cont) := by
  intro t hc hi hw hlen hR hp hn
  obtain ⟨params, body, retShape, hlook, hspec⟩ := hf
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hn ⊢
  rcases hargs : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) args with _ | values
  · exact opDispatchPostA_error s0 t
  · simp only [hargs] at hn ⊢
    rcases hl : lookupCodeHOLFinite t.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · exact opDispatchPostA_error s0 t
    · simp only [hl] at hn ⊢
      by_cases hz : t.clock = 0
      · simp [hz] at hn
      · simp only [hz, ↓reduceIte] at hn ⊢
        have hbody_eq : body' = body :=
          lookupCodeHOLFinite_installed_body t.code.lookup fname params body body'
            retShape ret' values callee (by rw [hc]; exact hlook) hl
        subst body'
        have hret_eq : ret' = retShape := by
          have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
            t.code.lookup fname values body callee ret' hl
          rw [hc] at hx; simp only [Flapjack.lookupCodeHOLExact, hlook] at hx
          split at hx
          · exact (congrArg (fun x => x.2.2) (Option.some.inj hx)).symm
          · cases hx
        subst ret'
        have hi_ce : EvmInv (callEntryStateHOLFinite t callee) := localsFree_evmInv t callee (t.clock - 1) hi
        have hw_ce : Group10.HeadMemChainWF (callEntryStateHOLFinite t callee) :=
          Group10.headMemChainWF_locals t callee (t.clock - 1) hw
        have hPc : Pc (callEntryStateHOLFinite t callee) := hentry t values body callee retShape hc hi hw hp hargs hl
        have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup fname values =
            some (body, callee, retShape) := by rwa [← hc]
        have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite t callee) body).1
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite t callee) body with ⟨res, cpost⟩
        simp only [hrun] at hn hmeta ⊢
        change cpost.code = t.code at hmeta
        have hc_ce := evm_congr (s := t) (t := callEntryStateHOLFinite t callee) rfl rfl
        have hQ (hsafe : res ≠ some .timeOut) :
            (∀ v, res = some (.returned v) →
              (EvmInv cpost ∧ Group10.HeadMemChainWF cpost) ∧
              evmChain cpost = evmChain (callEntryStateHOLFinite t callee) ∧
              evmR cpost ≤ evmR (callEntryStateHOLFinite t callee) ∧
              Qc (callEntryStateHOLFinite t callee) v cpost) ∧
            (IsEvmErr res →
              (EvmInv cpost ∧ Group10.HeadMemChainWF cpost) ∧
              evmChain cpost = evmChain (callEntryStateHOLFinite t callee) ∧
              evmR cpost ≤ evmR (callEntryStateHOLFinite t callee)) := by
          have hs := hspec (callEntryStateHOLFinite t callee) hc hi_ce hw_ce hPc ⟨values, hl_orig⟩
            (by rw [hrun]; exact hsafe)
          dsimp only at hs; rw [hrun] at hs; exact hs
        cases res with
        | none => exact opDispatchPostA_error s0 cpost
        | some r0 =>
          cases r0 with
          | timeOut => simp at hn
          | returned v =>
            dsimp only at hn ⊢
            split
            · rename_i hsh_ok
              rw [if_pos hsh_ok] at hn
              obtain ⟨⟨hi_cp, hw_cp⟩, hch_cp, hR_cp, hQc_cp⟩ := (hQ (by simp)).1 v rfl
              let resumed := setVarHOLFinite nm v { cpost with locals := t.locals }
              have hcode_res : resumed.code = originalRuntimeCode := hmeta.trans hc
              have hi_res : EvmInv resumed := localsFree_evmInv cpost resumed.locals cpost.clock hi_cp
              have hw_res : Group10.HeadMemChainWF resumed :=
                Group10.headMemChainWF_locals cpost resumed.locals cpost.clock hw_cp
              have hc_res := evm_congr (s := cpost) (t := resumed) rfl rfl
              have hlen_res : (evmChain resumed).length = (evmChain s0).length := by
                rw [hc_res.2.2.1, hch_cp, hc_ce.2.2.1]; exact hlen
              have hR_res : if charged then evmR resumed < evmR s0 else evmR resumed ≤ evmR s0 :=
                rboundA_step (by rw [hc_res.2.1]; rw [hc_ce.2.1] at hR_cp; exact hR_cp) hR
              have hQ_res : Q resumed :=
                hstep t values body callee retShape v cpost hi hw hp hargs hl_orig hi_cp hw_cp hch_cp hQc_cp
              have hb := hcont resumed hcode_res hi_res hw_res hlen_res hR_res hQ_res (by simpa [resumed] using hn)
              exact opDispatchPostA_congr_lc rfl hb
            · exact opDispatchPostA_error s0 cpost
          | exception eid ev =>
            by_cases heid : eid = ofString "EvmErr"
            · subst heid
              obtain ⟨⟨hi_cp, hw_cp⟩, hch_cp, hR_cp⟩ := (hQ (by simp)).2 ⟨ev, rfl⟩
              have hi_el : EvmInv cpost.emptyLocalsHOLFinite :=
                localsFree_evmInv cpost _ cpost.clock hi_cp
              have hw_el : Group10.HeadMemChainWF cpost.emptyLocalsHOLFinite :=
                Group10.headMemChainWF_locals cpost _ cpost.clock hw_cp
              have hc_el := evm_congr (s := cpost) (t := cpost.emptyLocalsHOLFinite) rfl rfl
              refine ⟨?_, fun _ => ⟨⟨hi_el, hw_el⟩, ?_, ?_⟩⟩
              · rintro ⟨_, h⟩; cases h
              · rw [hc_el.2.2.1, hch_cp, hc_ce.2.2.1]; exact hlen
              · have := rboundA_to_le hR; rw [hc_el.2.1]; rw [hc_ce.2.1] at hR_cp; omega
            · refine opDispatchPostA_other (fun _ h => by cases h) ?_
              rintro ⟨_, h⟩; injection h with h'; injection h' with h1 _; exact heid h1
          | «break» => exact opDispatchPostA_error s0 cpost
          | «continue» => exact opDispatchPostA_error s0 cpost
          | finalFfi _ =>
            refine opDispatchPostA_other (fun _ h => by cases h) ?_
            rintro ⟨_, h⟩; cases h
          | error => exact opDispatchPostA_error s0 cpost.emptyLocalsHOLFinite

theorem HandlerRunA.seq_call {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {P Q : PanSemStateFiniteExact 64 F → Prop}
    {Pc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {Qc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    {charged : Bool}
    {fname : MlS} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (hf : EvmPreservingSpecA Pc Qc fname)
    (hentry : ∀ t values body' callee ret',
      t.code = originalRuntimeCode → EvmInv t → Group10.HeadMemChainWF t → P t →
      evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) args = some values →
      lookupCodeHOLFinite t.code.lookup fname values = some (body', callee, ret') →
      Pc (callEntryStateHOLFinite t callee))
    (hstep : ∀ t values body callee retShape v cpost,
      EvmInv t → Group10.HeadMemChainWF t → P t →
      evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) args = some values →
      lookupCodeHOLFinite originalRuntimeCode.lookup fname values = some (body, callee, retShape) →
      EvmInv cpost → Group10.HeadMemChainWF cpost →
      evmChain cpost = evmChain (callEntryStateHOLFinite t callee) →
      Qc (callEntryStateHOLFinite t callee) v cpost →
      Q { cpost with locals := t.locals })
    (hcont : HandlerRunA s0 Q charged cont) :
    HandlerRunA s0 P charged (.seq (.call (some (none, none)) fname args) cont) := by
  intro t hc hi hw hlen hR hp hn
  obtain ⟨params, body, retShape, hlook, hspec⟩ := hf
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_call] at hn ⊢
  rcases hargs : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) args with _ | values
  · exact opDispatchPostA_error s0 t
  · simp only [hargs] at hn ⊢
    rcases hl : lookupCodeHOLFinite t.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · exact opDispatchPostA_error s0 t
    · simp only [hl] at hn ⊢
      by_cases hz : t.clock = 0
      · simp [hz] at hn
      · simp only [hz, ↓reduceIte] at hn ⊢
        have hbody_eq : body' = body :=
          lookupCodeHOLFinite_installed_body t.code.lookup fname params body body'
            retShape ret' values callee (by rw [hc]; exact hlook) hl
        subst body'
        have hret_eq : ret' = retShape := by
          have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
            t.code.lookup fname values body callee ret' hl
          rw [hc] at hx; simp only [Flapjack.lookupCodeHOLExact, hlook] at hx
          split at hx
          · exact (congrArg (fun x => x.2.2) (Option.some.inj hx)).symm
          · cases hx
        subst ret'
        have hi_ce : EvmInv (callEntryStateHOLFinite t callee) := localsFree_evmInv t callee (t.clock - 1) hi
        have hw_ce : Group10.HeadMemChainWF (callEntryStateHOLFinite t callee) :=
          Group10.headMemChainWF_locals t callee (t.clock - 1) hw
        have hPc : Pc (callEntryStateHOLFinite t callee) := hentry t values body callee retShape hc hi hw hp hargs hl
        have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup fname values =
            some (body, callee, retShape) := by rwa [← hc]
        have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite t callee) body).1
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite t callee) body with ⟨res, cpost⟩
        simp only [hrun] at hn hmeta ⊢
        change cpost.code = t.code at hmeta
        have hc_ce := evm_congr (s := t) (t := callEntryStateHOLFinite t callee) rfl rfl
        have hQ (hsafe : res ≠ some .timeOut) :
            (∀ v, res = some (.returned v) →
              (EvmInv cpost ∧ Group10.HeadMemChainWF cpost) ∧
              evmChain cpost = evmChain (callEntryStateHOLFinite t callee) ∧
              evmR cpost ≤ evmR (callEntryStateHOLFinite t callee) ∧
              Qc (callEntryStateHOLFinite t callee) v cpost) ∧
            (IsEvmErr res →
              (EvmInv cpost ∧ Group10.HeadMemChainWF cpost) ∧
              evmChain cpost = evmChain (callEntryStateHOLFinite t callee) ∧
              evmR cpost ≤ evmR (callEntryStateHOLFinite t callee)) := by
          have hs := hspec (callEntryStateHOLFinite t callee) hc hi_ce hw_ce hPc ⟨values, hl_orig⟩
            (by rw [hrun]; exact hsafe)
          dsimp only at hs; rw [hrun] at hs; exact hs
        cases res with
        | none => exact opDispatchPostA_error s0 cpost
        | some r0 =>
          cases r0 with
          | timeOut => simp at hn
          | returned v =>
            by_cases hsh_ok : shapeEqHOL (shapeOfHOLExact v) retShape = true
            · simp only [hsh_ok, ↓reduceIte] at hn ⊢
              obtain ⟨⟨hi_cp, hw_cp⟩, hch_cp, hR_cp, hQc_cp⟩ := (hQ (by simp)).1 v rfl
              let resumed : PanSemStateFiniteExact 64 F := { cpost with locals := t.locals }
              have hcode_res : resumed.code = originalRuntimeCode := hmeta.trans hc
              have hi_res : EvmInv resumed := localsFree_evmInv cpost t.locals cpost.clock hi_cp
              have hw_res : Group10.HeadMemChainWF resumed :=
                Group10.headMemChainWF_locals cpost t.locals cpost.clock hw_cp
              have hc_res := evm_congr (s := cpost) (t := resumed) rfl rfl
              have hlen_res : (evmChain resumed).length = (evmChain s0).length := by
                rw [hc_res.2.2.1, hch_cp, hc_ce.2.2.1]; exact hlen
              have hR_res : if charged then evmR resumed < evmR s0 else evmR resumed ≤ evmR s0 :=
                rboundA_step (by rw [hc_res.2.1]; rw [hc_ce.2.1] at hR_cp; exact hR_cp) hR
              have hQ_res : Q resumed :=
                hstep t values body callee retShape v cpost hi hw hp hargs hl_orig hi_cp hw_cp hch_cp hQc_cp
              exact hcont resumed hcode_res hi_res hw_res hlen_res hR_res hQ_res (by simpa [resumed] using hn)
            · simp only [hsh_ok, Bool.false_eq_true, ↓reduceIte]
              exact opDispatchPostA_error s0 cpost
          | exception eid ev =>
            by_cases heid : eid = ofString "EvmErr"
            · subst heid
              obtain ⟨⟨hi_cp, hw_cp⟩, hch_cp, hR_cp⟩ := (hQ (by simp)).2 ⟨ev, rfl⟩
              have hi_el : EvmInv cpost.emptyLocalsHOLFinite :=
                localsFree_evmInv cpost _ cpost.clock hi_cp
              have hw_el : Group10.HeadMemChainWF cpost.emptyLocalsHOLFinite :=
                Group10.headMemChainWF_locals cpost _ cpost.clock hw_cp
              have hc_el := evm_congr (s := cpost) (t := cpost.emptyLocalsHOLFinite) rfl rfl
              refine ⟨?_, fun _ => ⟨⟨hi_el, hw_el⟩, ?_, ?_⟩⟩
              · rintro ⟨_, h⟩; cases h
              · rw [hc_el.2.2.1, hch_cp, hc_ce.2.2.1]; exact hlen
              · have := rboundA_to_le hR; rw [hc_el.2.1]; rw [hc_ce.2.1] at hR_cp; omega
            · refine opDispatchPostA_other (fun _ h => by cases h) ?_
              rintro ⟨_, h⟩; injection h with h'; injection h' with h1 _; exact heid h1
          | «break» => exact opDispatchPostA_error s0 cpost
          | «continue» => exact opDispatchPostA_error s0 cpost
          | finalFfi _ =>
            refine opDispatchPostA_other (fun _ h => by cases h) ?_
            rintro ⟨_, h⟩; cases h
          | error => exact opDispatchPostA_error s0 cpost.emptyLocalsHOLFinite

theorem HandlerRunA.dec_simple {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {charged : Bool} {nm : MlS} {sh : ShapeHOL} {init : ExpHOL 64} {body : ProgHOL 64}
    (hbody : HandlerRunA s0 (fun _ => True) charged body) :
    HandlerRunA s0 (fun _ => True) charged (.dec nm sh init body) :=
  HandlerRunA.dec (fun _ _ _ _ _ => trivial) hbody

theorem HandlerRunA.decCall_simple {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {Qc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    {charged : Bool}
    {nm : MlS} {sh : ShapeHOL} {fname : MlS} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (hf : EvmPreservingSpecA (fun _ => True) Qc fname)
    (hcont : HandlerRunA s0 (fun _ => True) charged cont) :
    HandlerRunA s0 (fun _ => True) charged (.decCall nm sh fname args cont) :=
  HandlerRunA.decCall hf (by intros; trivial) (by intros; trivial) hcont

theorem HandlerRunA.seq_call_simple {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {Qc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    {charged : Bool} {fname : MlS} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (hf : EvmPreservingSpecA (fun _ => True) Qc fname)
    (hcont : HandlerRunA s0 (fun _ => True) charged cont) :
    HandlerRunA s0 (fun _ => True) charged (.seq (.call (some (none, none)) fname args) cont) :=
  HandlerRunA.seq_call hf (by intros; trivial) (by intros; trivial) hcont

theorem epsA_require_not_static :
    EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "require_not_static") :=
  epsA_of_readOnly 470 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_require_not_static rfl
    opRoCallees opRoCallees_good (by decide)

private theorem store_some_eq_error_g10 {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {dst val : ExpHOL 64} {res : PanSemResultExact 64}
    (h : evaluateHOLFiniteState s (.store dst val) = (some res, post)) :
    res = .error := by
  rw [evaluateHOLFiniteState_store] at h
  revert h
  rcases @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dst with _ | dv
  · intro h; injection h with h1; injection h1 with h2; exact h2.symm
  · rcases dv with ⟨⟨addr⟩⟩ | _ | _
    · rcases @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) val with _ | v
      · intro h; injection h with h1; injection h1 with h2; exact h2.symm
      · dsimp only
        split
        · intro h; injection h with h1; cases h1
        · intro h; injection h with h1; injection h1 with h2; exact h2.symm
    · intro h; injection h with h1; injection h1 with h2; exact h2.symm
    · intro h; injection h with h1; injection h1 with h2; exact h2.symm

private theorem evmInv_head_ev_bounds_g10 {F : Type} {s : PanSemStateFiniteExact 64 F} (hInv : EvmInv s) :
    0 < globN s "ev" ∧ globN s "ev" + 280 ≤ heapEnd ∧ globN s "ev" + 280 ≤ 2 ^ 64 := by
  obtain ⟨hAs, S, _, _, _, _, hFW_all, _⟩ := hInv
  have hhead : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by
    unfold evmChain
    have hpos : ∃ m, Wave8GuestInv.maxChain + 1 = m + 1 := ⟨Wave8GuestInv.maxChain, rfl⟩
    obtain ⟨m, hm⟩ := hpos; rw [hm, evmChainFrom]; exact List.mem_cons_self
  have hFW0 := hFW_all _ hhead
  have hin1 := (hFW0.1 (globN s "ev", 280) (by simp)).1.1
  have hin2 := (hFW0.1 (globN s "ev", 280) (by simp)).1.2
  dsimp only at hin1 hin2
  have hfm1 := hAs.2.2.2.1
  have hfm2 := hAs.2.2.2.2.1
  rw [R11Shards.scratchStart_val] at hfm1
  rw [R11Shards.scratchEnd_val] at hin2
  rw [R11Shards.heapEnd_val]
  have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := by norm_num
  rw [h264]
  exact ⟨by omega, by omega, by omega⟩

theorem epsA_pc_add :
    EvmPreservingSpecA (fun _ => True) (fun s _ post => post.globals = s.globals)
      (ofString "pc_add") := by
  refine ⟨_, _, _, lookup_pc_add, ?_⟩
  intro F s _ hInv hWF _ _ _
  have hbody : sourceFnBody Guest.Software.guestFn_pc_add =
      .seq
        (.store (.op .add [.var .global (ofString "ev"), .const 0])
          (.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 0]), .var .local (ofString "n")]))
        (.return (.const 0)) := rfl
  have hhead_mem : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by simp [evmChain, evmChainFrom]
  have hFW0 := hInv.2.choose_spec.2.2.2.2.1 _ hhead_mem
  have hb_ev := (frameWF_bounds hInv.1.2 hFW0).1
  dsimp only at hb_ev
  have hev_pos : 0 < globN s "ev" := by
    have hin := (hFW0.1 (globN s "ev", 280) (by simp)).1.1
    have h1 := hInv.1.2.2.2.1
    have h2 := hInv.1.2.2.2.2.1
    rw [R11Shards.scratchStart_val] at h1
    dsimp only at hin
    omega
  obtain ⟨evw, hevw, hevw_nat⟩ := global_word_of_pos s "ev" hev_pos
  dsimp only
  rw [hbody, evaluateHOLFiniteState_seq_line780]
  rcases hst : evaluateHOLFiniteState s
      (.store (.op .add [.var .global (ofString "ev"), .const 0])
        (.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 0]), .var .local (ofString "n")])) with ⟨r1, s1⟩
  cases r1 with
  | some res1 =>
    have herr := store_some_eq_error_g10 hst
    subst herr
    dsimp only
    constructor
    · intro _ h; cases h
    · rintro ⟨_, h⟩; cases h
  | none =>
    dsimp only
    obtain ⟨w1, _, hs1_eq⟩ := R14Shards.OpHandlersA.store_global_off_word (t := s) (post := s1)
      (gname := "ev") (gbase := globN s "ev") (off := 0) hevw hevw_nat (by omega)
      (fun v hv => by
        simp only [evalHOLExact, wordOpHOL] at hv
        revert hv
        rcases @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) _ with _ | vs
        · simp
        · dsimp only
          split
          · simp only [Option.map]
            rcases wordOp .add (vs.map valueWord) with _ | w
            · simp
            · intro hv; injection hv with hv'; exact ⟨w, hv'.symm⟩
          · simp) hst
    rw [evaluateHOLFiniteState_return]
    dsimp only [evalHOLExact]
    have hsz0 : sizeOfShapeWithContextHOL s1.structs
        (shapeOfHOLExact (.val (.word (0 : BitVec 64)))) ≤ 32 := by
      simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
    rw [if_pos hsz0]
    dsimp only
    let post := emptyLocalsHOLFinite s1
    have hGp : GuestInv post := guestInv_congr (s := s)
      (by simp [post, emptyLocalsHOLFinite, hs1_eq])
      (by simp [post, emptyLocalsHOLFinite, hs1_eq])
      (by simp [post, emptyLocalsHOLFinite, hs1_eq])
      (by simp [post, emptyLocalsHOLFinite, hs1_eq]) hInv.1.1
    have hglob_p : post.globals = s.globals := by simp [post, emptyLocalsHOLFinite, hs1_eq]
    have hbe_p : post.be = s.be := by simp [post, emptyLocalsHOLFinite, hs1_eq]
    have hmem_ne : ∀ x : BitVec 64, x ≠ BitVec.ofNat 64 (globN s "ev" + 0) →
        post.memory x = s.memory x := by
      intro x hx
      change s1.memory x = s.memory x
      rw [hs1_eq]
      dsimp only [R14Shards.OpHandlersA.updW]
      rw [if_neg hx]
    have hmem_out : ∀ x : BitVec 64,
        (∀ off ∈ nonStructFrameOffs, x ≠ BitVec.ofNat 64 (globN s "ev" + off)) →
        post.memory x = s.memory x := by
      intro x hx
      exact hmem_ne x (hx 0 (by simp [nonStructFrameOffs]))
    obtain ⟨hInv_p, hch_p, hR_p⟩ := evmInv_of_head_nonstruct hInv hGp hglob_p hbe_p hmem_out
    have hWF_p : Group10.HeadMemChainWF post :=
      headMemChainWF_store_headSafe hInv hWF
        (x := BitVec.ofNat 64 (globN s "ev" + 0))
        (by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          exact Or.inl ⟨0, rfl, by omega, by omega, by omega, by omega⟩)
        hglob_p hch_p hmem_ne
    exact ⟨fun _ _ => ⟨⟨hInv_p, hWF_p⟩, hch_p, le_of_eq hR_p, hglob_p⟩,
      by rintro ⟨_, h⟩; cases h⟩

theorem charge_gas_body_exactA {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hInv : EvmInv s) (hWF : Group10.HeadMemChainWF s) {amtw : BitVec 64}
    (hamt : s.locals.lookup (ofString "amount") = some (.val (.word amtw))) :
    let out := evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_charge_gas)
    (∀ v, out.1 = some (.returned v) →
      (EvmInv out.2 ∧ Group10.HeadMemChainWF out.2) ∧ out.2.globals = s.globals ∧
      evmChain out.2 = evmChain s ∧ evmR out.2 + amtw.toNat = evmR s) ∧
    (IsEvmErr out.1 →
      (EvmInv out.2 ∧ Group10.HeadMemChainWF out.2) ∧ out.2.globals = s.globals ∧
      evmChain out.2 = evmChain s ∧ evmR out.2 = evmR s) := by
  have hcg := charge_gas_body_exact s hInv hamt
  dsimp only at hcg ⊢
  have hhead_mem : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by simp [evmChain, evmChainFrom]
  have hFW0 := hInv.2.choose_spec.2.2.2.2.1 _ hhead_mem
  have hb_ev := (frameWF_bounds hInv.1.2 hFW0).1
  dsimp only at hb_ev
  have hev_pos : 0 < globN s "ev" := by
    have hin := (hFW0.1 (globN s "ev", 280) (by simp)).1.1
    have h1 := hInv.1.2.2.2.1
    have h2 := hInv.1.2.2.2.2.1
    rw [R11Shards.scratchStart_val] at h1
    dsimp only at hin
    omega
  obtain ⟨evw, hevw, hevw_nat⟩ := global_word_of_pos s "ev" hev_pos
  have hmem_res (hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_charge_gas)).1) :
      let post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_charge_gas)).2
      ∀ x : BitVec 64,
        x ≠ BitVec.ofNat 64 (globN s "ev" + 64) →
        x ≠ BitVec.ofNat 64 (globN s "ev" + 184) →
        post.memory x = s.memory x := by
    dsimp only
    have hnot_err : ¬ Resumes (some (.error : PanSemResultExact 64)) := by
      rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> cases h
    have hbody : sourceFnBody Guest.Software.guestFn_charge_gas =
        .dec (ofString "gl") .one (.load .one (.op .add [.var .global (ofString "ev"), .const 64]))
          (.seq
            (.ite (.cmp .lower (.var .local (ofString "gl")) (.var .local (ofString "amount")))
              (.raise (ofString "EvmErr") (.const 4))
              .skip)
            (.seq
              (.store (.op .add [.var .global (ofString "ev"), .const 64])
                (.op .sub [.var .local (ofString "gl"), .var .local (ofString "amount")]))
              (.seq
                (.store (.op .add [.var .global (ofString "ev"), .const 184])
                  (.op .add
                    [.load .one (.op .add [.var .global (ofString "ev"), .const 184]),
                     .var .local (ofString "amount")]))
                (.return (.const 0))))) := rfl
    revert hres
    rw [hbody, evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · intro hres; exact absurd hres hnot_err
    · rename_i glv _
      split
      · dsimp only
        set s1 := setVarHOLFinite (ofString "gl") glv s
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
        split
        · split
          · simp only [evaluateHOLFiniteState_skip]
            rw [evaluateHOLFiniteState_seq_line780]
            rcases hst1 : evaluateHOLFiniteState s1
                (.store (.op .add [.var .global (ofString "ev"), .const 64])
                  (.op .sub [.var .local (ofString "gl"), .var .local (ofString "amount")])) with ⟨r1, s2⟩
            cases r1 with
            | some res1 =>
              have herr1 := store_some_eq_error_g10 hst1; subst herr1; dsimp only
              intro hres; exact absurd hres hnot_err
            | none =>
              dsimp only
              obtain ⟨w1, _, hs2_eq⟩ := R14Shards.OpHandlersA.store_global_off_word (t := s1) (post := s2)
                (gname := "ev") (gbase := globN s "ev") (off := 64) hevw hevw_nat (by omega)
                (fun v hv => by
                  simp only [evalHOLExact, wordOpHOL] at hv; revert hv
                  rcases @evalListHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a)) _ with _ | vs
                  · simp
                  · dsimp only; split
                    · simp only [Option.map]
                      rcases wordOp .sub (vs.map valueWord) with _ | w
                      · simp
                      · intro hv; injection hv with hv'; exact ⟨w, hv'.symm⟩
                    · simp) hst1
              rw [evaluateHOLFiniteState_seq_line780]
              rcases hst2 : evaluateHOLFiniteState s2
                  (.store (.op .add [.var .global (ofString "ev"), .const 184])
                    (.op .add
                      [.load .one (.op .add [.var .global (ofString "ev"), .const 184]),
                       .var .local (ofString "amount")])) with ⟨r2, s3⟩
              cases r2 with
              | some res2 =>
                have herr2 := store_some_eq_error_g10 hst2; subst herr2; dsimp only
                intro hres; exact absurd hres hnot_err
              | none =>
                dsimp only
                obtain ⟨w2, _, hs3_eq⟩ := R14Shards.OpHandlersA.store_global_off_word (t := s2) (post := s3)
                  (gname := "ev") (gbase := globN s "ev") (off := 184)
                  (by rw [hs2_eq]; exact hevw) hevw_nat (by omega)
                  (fun v hv => by
                    simp only [evalHOLExact, wordOpHOL] at hv; revert hv
                    rcases @evalListHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a)) _ with _ | vs
                    · simp
                    · dsimp only; split
                      · simp only [Option.map]
                        rcases wordOp .add (vs.map valueWord) with _ | w
                        · simp
                        · intro hv; injection hv with hv'; exact ⟨w, hv'.symm⟩
                      · simp) hst2
                intro _ x hx64 hx184
                rw [evaluateHOLFiniteState_return]
                split
                · dsimp only; rw [hs3_eq]; dsimp only [R14Shards.OpHandlersA.updW]; rw [if_neg hx184, hs2_eq]; dsimp only [R14Shards.OpHandlersA.updW]; rw [if_neg hx64]; rfl
                · split
                  · dsimp only [emptyLocalsHOLFinite]; rw [hs3_eq]; dsimp only [R14Shards.OpHandlersA.updW]; rw [if_neg hx184, hs2_eq]; dsimp only [R14Shards.OpHandlersA.updW]; rw [if_neg hx64]; rfl
                  · dsimp only; rw [hs3_eq]; dsimp only [R14Shards.OpHandlersA.updW]; rw [if_neg hx184, hs2_eq]; dsimp only [R14Shards.OpHandlersA.updW]; rw [if_neg hx64]; rfl
          · rcases hraise : evaluateHOLFiniteState s1 (.raise (ofString "EvmErr") (.const 4)) with ⟨rr, sr⟩
            have hr_nn : rr ≠ none ∧ sr.memory = s.memory := by
              rw [evaluateHOLFiniteState_raise] at hraise; dsimp only [evalHOLExact] at hraise
              split at hraise
              · split at hraise <;> (injection hraise with h1 h2; subst h1 h2; exact ⟨by simp, rfl⟩)
              · injection hraise with h1 h2; subst h1 h2; exact ⟨by simp, rfl⟩
            cases rr with
            | none => exact absurd rfl hr_nn.1
            | some _ =>
              dsimp only; intro _ x _ _; exact congrFun hr_nn.2 x
        · intro hres; exact absurd hres hnot_err
      · intro hres; exact absurd hres hnot_err
  have hwf_mk {post : PanSemStateFiniteExact 64 F}
      (hg : post.globals = s.globals) (hch : evmChain post = evmChain s)
      (hm : ∀ x : BitVec 64, x ≠ BitVec.ofNat 64 (globN s "ev" + 64) →
        x ≠ BitVec.ofNat 64 (globN s "ev" + 184) → post.memory x = s.memory x) :
      Group10.HeadMemChainWF post :=
    headMemChainWF_of_headSafe hInv hWF hch
      (congrFun (globN_congr hg) "ev") (congrFun (globN_congr hg) "frame_mem_ptr")
      (fun x hx => hm x
        (fun h => hx (by subst h; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact Or.inl ⟨64, rfl, by omega, by omega, by omega, by omega⟩))
        (fun h => hx (by subst h; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact Or.inl ⟨184, rfl, by omega, by omega, by omega, by omega⟩)))
  refine ⟨fun v hv => ?_, fun ⟨ev, hev⟩ => ?_⟩
  · obtain ⟨hI, hg, hch, hR⟩ := hcg.1 v hv
    exact ⟨⟨hI, hwf_mk hg hch (hmem_res (Or.inl ⟨v, hv⟩))⟩, hg, hch, hR⟩
  · obtain ⟨hI, hg, hch, hR⟩ := hcg.2 ⟨ev, hev⟩
    exact ⟨⟨hI, hwf_mk hg hch (hmem_res (Or.inr ⟨_, ev, hev, by decide⟩))⟩, hg, hch, hR⟩

theorem epsA_charge_gas_any :
    EvmPreservingSpecA (fun _ => True)
      (fun s _ post => post.globals = s.globals)
      (ofString "charge_gas") := by
  refine ⟨_, _, _, M21.lookup_charge_gas, ?_⟩
  intro F s _ hInv hWF _ ⟨vals, hl⟩ _
  have hlen1 : ∃ v0, vals = [v0] := by
    have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
      originalRuntimeCode.lookup (ofString "charge_gas") vals _ _ _ hl
    simp only [Flapjack.lookupCodeHOLExact, M21.lookup_charge_gas] at hx
    rcases vals with _ | ⟨v0, _ | _⟩ <;> simp at hx
    exact ⟨v0, rfl⟩
  obtain ⟨v0, rfl⟩ := hlen1
  obtain ⟨_, _, amtw, rfl, hamt⟩ := one_word_arg_lookup M21.lookup_charge_gas hl
  have hcg := charge_gas_body_exactA s hInv hWF hamt
  dsimp only at hcg ⊢
  refine ⟨fun v hv => ?_, fun herr => ?_⟩
  · obtain ⟨hIW, hg, hch, hR⟩ := hcg.1 v hv
    exact ⟨hIW, hch, by change _ + _ = _ at hR; omega, hg⟩
  · obtain ⟨hIW, _, hch, hR⟩ := hcg.2 herr
    exact ⟨hIW, hch, le_of_eq hR⟩

theorem HandlerRunA.seq_charge_gas {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {P Q : PanSemStateFiniteExact 64 F → Prop} {charged : Bool}
    {amtExp : ExpHOL 64} {cont : ProgHOL 64}
    (hpos : ∀ t (w : BitVec 64),
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) amtExp =
        some (.val (.word w)) →
      EvmInv t → Group10.HeadMemChainWF t → P t → 0 < w.toNat)
    (hstep : ∀ t cpost,
      EvmInv t → Group10.HeadMemChainWF t → P t →
      EvmInv cpost → Group10.HeadMemChainWF cpost →
      cpost.globals = t.globals → evmChain cpost = evmChain t →
      Q { cpost with locals := t.locals })
    (hcont : HandlerRunA s0 Q true cont) :
    HandlerRunA s0 P charged (.seq (.call (some (none, none)) (ofString "charge_gas") [amtExp]) cont) := by
  intro t hc hi hw hlen hR hp hn
  have hR_le : evmR t ≤ evmR s0 := rboundA_to_le hR
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_call] at hn ⊢
  rcases hargs : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) [amtExp] with _ | values
  · exact opDispatchPostA_error s0 t
  · simp only [hargs] at hn ⊢
    rcases hl : lookupCodeHOLFinite t.code.lookup (ofString "charge_gas") values with _ | ⟨body', callee, ret'⟩
    · exact opDispatchPostA_error s0 t
    · simp only [hl] at hn ⊢
      by_cases hz : t.clock = 0
      · simp [hz] at hn
      · simp only [hz, ↓reduceIte] at hn ⊢
        have hv_list : ∃ v0, @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) amtExp = some v0 ∧ values = [v0] := by
          rw [evalListHOLFinite_eq_toExact] at hargs
          simp only [evalListHOLExact] at hargs
          rcases he : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) amtExp with _ | v0
          · simp [he] at hargs
          · simp only [he, Option.some.injEq] at hargs; exact ⟨v0, rfl, hargs.symm⟩
        obtain ⟨v0, hv0_ev, rfl⟩ := hv_list
        have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "charge_gas") [v0] =
            some (body', callee, ret') := by rwa [← hc]
        obtain ⟨rfl, rfl, amtw, rfl, hamt_cal⟩ := one_word_arg_lookup M21.lookup_charge_gas hl_orig
        have hamt_pos : 0 < amtw.toNat := hpos t amtw hv0_ev hi hw hp
        have hi_ce : EvmInv (callEntryStateHOLFinite t callee) := localsFree_evmInv t callee (t.clock - 1) hi
        have hw_ce : Group10.HeadMemChainWF (callEntryStateHOLFinite t callee) :=
          Group10.headMemChainWF_locals t callee (t.clock - 1) hw
        have hc_ce := evm_congr (s := t) (t := callEntryStateHOLFinite t callee) rfl rfl
        have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata
          (callEntryStateHOLFinite t callee) (sourceFnBody Guest.Software.guestFn_charge_gas)).1
        have hcg := charge_gas_body_exactA (callEntryStateHOLFinite t callee) hi_ce hw_ce hamt_cal
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite t callee)
            (sourceFnBody Guest.Software.guestFn_charge_gas) with ⟨res, cpost⟩
        simp only [hrun] at hn hmeta hcg ⊢
        change cpost.code = t.code at hmeta
        cases res with
        | none => exact opDispatchPostA_error s0 cpost
        | some r0 =>
          cases r0 with
          | timeOut => simp at hn
          | returned v =>
            by_cases hsh_ok : shapeEqHOL (shapeOfHOLExact v) .one = true
            · simp only [hsh_ok, ↓reduceIte] at hn ⊢
              obtain ⟨⟨hi_cp, hw_cp⟩, hglob_cp, hch_cp, hR_cp⟩ := hcg.1 v rfl
              let resumed : PanSemStateFiniteExact 64 F := { cpost with locals := t.locals }
              have hi_res : EvmInv resumed := localsFree_evmInv cpost t.locals cpost.clock hi_cp
              have hw_res : Group10.HeadMemChainWF resumed :=
                Group10.headMemChainWF_locals cpost t.locals cpost.clock hw_cp
              have hc_res := evm_congr (s := cpost) (t := resumed) rfl rfl
              have hlen_res : (evmChain resumed).length = (evmChain s0).length := by
                rw [hc_res.2.2.1, hch_cp, hc_ce.2.2.1]; exact hlen
              have hR_lt : evmR resumed < evmR s0 := by
                rw [hc_res.2.1]; rw [hc_ce.2.1] at hR_cp; omega
              exact hcont resumed (hmeta.trans hc) hi_res hw_res hlen_res (by simp [hR_lt])
                (hstep t cpost hi hw hp hi_cp hw_cp hglob_cp (hch_cp.trans (evmChain_congr rfl rfl)))
                (by simpa [resumed] using hn)
            · simp only [hsh_ok, Bool.false_eq_true, ↓reduceIte]
              exact opDispatchPostA_error s0 cpost
          | exception eid ev =>
            by_cases heid : eid = ofString "EvmErr"
            · subst heid
              obtain ⟨⟨hi_cp, hw_cp⟩, _, hch_cp, hR_cp⟩ := hcg.2 ⟨ev, rfl⟩
              have hi_el : EvmInv cpost.emptyLocalsHOLFinite := localsFree_evmInv cpost _ cpost.clock hi_cp
              have hw_el : Group10.HeadMemChainWF cpost.emptyLocalsHOLFinite :=
                Group10.headMemChainWF_locals cpost _ cpost.clock hw_cp
              have hc_el := evm_congr (s := cpost) (t := cpost.emptyLocalsHOLFinite) rfl rfl
              refine ⟨?_, fun _ => ⟨⟨hi_el, hw_el⟩, ?_, ?_⟩⟩
              · rintro ⟨_, h⟩; cases h
              · rw [hc_el.2.2.1, hch_cp, hc_ce.2.2.1]; exact hlen
              · rw [hc_el.2.1, hR_cp, hc_ce.2.1]; exact hR_le
            · refine opDispatchPostA_other (fun _ h => by cases h) ?_
              rintro ⟨_, h⟩; injection h with h'; injection h' with h1 _; exact heid h1
          | «break» => exact opDispatchPostA_error s0 cpost
          | «continue» => exact opDispatchPostA_error s0 cpost
          | finalFfi _ =>
            refine opDispatchPostA_other (fun _ h => by cases h) ?_
            rintro ⟨_, h⟩; cases h
          | error => exact opDispatchPostA_error s0 cpost.emptyLocalsHOLFinite

theorem HandlerRunA.seq_charge_gas_const {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {charged : Bool} {k : BitVec 64} (hk : 0 < k.toNat) {cont : ProgHOL 64}
    (hcont : HandlerRunA s0 (fun _ => True) true cont) :
    HandlerRunA s0 (fun _ => True) charged (.seq (.call (some (none, none)) (ofString "charge_gas") [.const k]) cont) :=
  HandlerRunA.seq_charge_gas
    (fun _ w hw _ _ _ => by simp only [evalHOLExact] at hw; injection hw with h1; injection h1 with h2; injection h2 with h3; subst h3; exact hk)
    (by intros; trivial)
    hcont

theorem epsA_stack_pop :
    EvmPreservingSpecA (fun _ => True) (fun s _ post => post.globals = s.globals)
      (ofString "stack_pop") := by
  refine ⟨_, _, _, lookup_stack_pop_pub, ?_⟩
  intro F s hcode hInv hWF _ hlookup hnt
  obtain ⟨params_sp, body_sp, ret_sp, hlk_sp, hspec_sp⟩ := eps_stack_pop
  have hlk_eq : some ([], sourceFnBody Guest.Software.guestFn_stack_pop, ShapeHOL.comb [.one, .one, .one, .one]) =
      some (params_sp, body_sp, ret_sp) := lookup_stack_pop_pub.symm.trans hlk_sp
  injection hlk_eq with hprod
  rcases Prod.mk.inj hprod with ⟨rfl, hprod2⟩
  rcases Prod.mk.inj hprod2 with ⟨hbody_sp, rfl⟩
  subst hbody_sp
  have hsp := hspec_sp s hcode hInv trivial hlookup hnt
  dsimp only at hsp ⊢
  let retExp : ExpHOL 64 :=
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural
      (Exp.load (Shape.comb [Shape.one, Shape.one, Shape.one, Shape.one])
        (Exp.op BinOp.add [(Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.global "ev"), (Exp.const (BitVec.ofNat 64 8))])),
          (Exp.panOp PanOp.mul [(Exp.var VarKind.local "sp"), (Exp.const (BitVec.ofNat 64 32))])]))
  have hb : sourceFnBody Guest.Software.guestFn_stack_pop =
      .dec (ofString "sp") .one (.load .one (.op .add [.var .global (ofString "ev"), .const 16]))
        (.seq
          (.ite (.cmp .equal (.var .local (ofString "sp")) (.const 0))
            (.raise (ofString "EvmErr") (.const 2))
            .skip)
          (.seq
            (.assign .local (ofString "sp") (.op .sub [.var .local (ofString "sp"), .const 1]))
            (.seq
              (.store (.op .add [.var .global (ofString "ev"), .const 16]) (.var .local (ofString "sp")))
              (.return retExp)))) := rfl
  have hhead_mem : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by simp [evmChain, evmChainFrom]
  have hFW0 := hInv.2.choose_spec.2.2.2.2.1 _ hhead_mem
  have hb_ev := (frameWF_bounds hInv.1.2 hFW0).1
  dsimp only at hb_ev
  have hev_pos : 0 < globN s "ev" := by
    have hin := (hFW0.1 (globN s "ev", 280) (by simp)).1.1
    have h1 := hInv.1.2.2.2.1; have h2 := hInv.1.2.2.2.2.1
    rw [R11Shards.scratchStart_val] at h1; dsimp only at hin; omega
  obtain ⟨evw, hevw, hevw_nat⟩ := global_word_of_pos s "ev" hev_pos
  have hmem_glob (hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_stack_pop)).1) :
      let post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_stack_pop)).2
      post.globals = s.globals ∧ ∀ x : BitVec 64, x ≠ BitVec.ofNat 64 (globN s "ev" + 16) → post.memory x = s.memory x := by
    dsimp only
    have hnot_err : ¬ Resumes (some (.error : PanSemResultExact 64)) := by
      rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> cases h
    revert hres
    rw [hb, evaluateHOLFiniteState_dec_total]; dsimp only
    split
    · intro hres; exact absurd hres hnot_err
    · rename_i vsp _
      split
      · dsimp only
        set s1 := setVarHOLFinite (ofString "sp") vsp s
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
        split
        · split
          · simp only [evaluateHOLFiniteState_skip]
            rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
            split
            · intro hres; exact absurd hres hnot_err
            · rename_i sp1 hsp1
              have hsp1_w : ∃ w : BitVec 64, sp1 = .val (.word w) := by
                simp only [evalHOLExact, wordOpHOL] at hsp1; revert hsp1
                rcases @evalListHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a)) _ with _ | vs
                · simp
                · dsimp only; split
                  · simp only [Option.map]
                    rcases wordOp .sub (vs.map valueWord) with _ | w
                    · simp
                    · intro hv; injection hv with hv'; exact ⟨w, hv'.symm⟩
                  · simp
              obtain ⟨spw, rfl⟩ := hsp1_w
              split
              · dsimp only
                set s2 := setKvarHOLFinite .local (ofString "sp") (.val (.word spw)) s1
                rw [evaluateHOLFiniteState_seq_line780]
                rcases hst : evaluateHOLFiniteState s2
                    (.store (.op .add [.var .global (ofString "ev"), .const 16]) (.var .local (ofString "sp"))) with ⟨r2, s3⟩
                cases r2 with
                | some res2 =>
                  have herr := store_some_eq_error_g10 hst; subst herr; dsimp only
                  intro hres; exact absurd hres hnot_err
                | none =>
                  dsimp only
                  obtain ⟨w2, _, hs3_eq⟩ := R14Shards.OpHandlersA.store_global_off_word (t := s2) (post := s3)
                    (gname := "ev") (gbase := globN s "ev") (off := 16) hevw hevw_nat (by omega)
                    (fun v hv => by
                      have hsp2 : s2.locals.lookup (ofString "sp") = some (.val (.word spw)) := by
                        simp [s2, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                      change s2.locals.lookup (ofString "sp") = some v at hv
                      rw [hsp2] at hv; injection hv with hv'; exact ⟨spw, hv'.symm⟩) hst
                  intro _
                  rw [evaluateHOLFiniteState_return]
                  split
                  · refine ⟨by simp [hs3_eq, s2, s1, setKvarHOLFinite, setVarHOLFinite], fun x hx => ?_⟩
                    dsimp only; rw [hs3_eq]; dsimp only [R14Shards.OpHandlersA.updW]; rw [if_neg hx]; rfl
                  · split
                    · refine ⟨by simp [emptyLocalsHOLFinite, hs3_eq, s2, s1, setKvarHOLFinite, setVarHOLFinite], fun x hx => ?_⟩
                      dsimp only [emptyLocalsHOLFinite]; rw [hs3_eq]; dsimp only [R14Shards.OpHandlersA.updW]; rw [if_neg hx]; rfl
                    · refine ⟨by simp [hs3_eq, s2, s1, setKvarHOLFinite, setVarHOLFinite], fun x hx => ?_⟩
                      dsimp only; rw [hs3_eq]; dsimp only [R14Shards.OpHandlersA.updW]; rw [if_neg hx]; rfl
              · intro hres; exact absurd hres hnot_err
          · rcases hraise : evaluateHOLFiniteState s1 (.raise (ofString "EvmErr") (.const 2)) with ⟨rr, sr⟩
            have hr_nn : rr ≠ none ∧ sr.globals = s.globals ∧ sr.memory = s.memory := by
              rw [evaluateHOLFiniteState_raise] at hraise; dsimp only [evalHOLExact] at hraise
              split at hraise
              · split at hraise <;> (injection hraise with h1 h2; subst h1 h2; exact ⟨by simp, rfl, rfl⟩)
              · injection hraise with h1 h2; subst h1 h2; exact ⟨by simp, rfl, rfl⟩
            cases rr with
            | none => exact absurd rfl hr_nn.1
            | some _ =>
              dsimp only; intro _
              exact ⟨hr_nn.2.1, fun x _ => congrFun hr_nn.2.2 x⟩
        · intro hres; exact absurd hres hnot_err
      · intro hres; exact absurd hres hnot_err
  have hwf_mk {post : PanSemStateFiniteExact 64 F}
      (hg : post.globals = s.globals) (hch : evmChain post = evmChain s)
      (hm : ∀ x : BitVec 64, x ≠ BitVec.ofNat 64 (globN s "ev" + 16) → post.memory x = s.memory x) :
      Group10.HeadMemChainWF post :=
    headMemChainWF_store_headSafe hInv hWF
      (x := BitVec.ofNat 64 (globN s "ev" + 16))
      (by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        exact Or.inl ⟨16, rfl, by omega, by omega, by omega, by omega⟩)
      hg hch hm
  refine ⟨fun v hv => ?_, fun ⟨ev, hev⟩ => ?_⟩
  · obtain ⟨hI, hch, hR, hg⟩ := hsp.1 v hv
    obtain ⟨_, hm⟩ := hmem_glob (Or.inl ⟨v, hv⟩)
    exact ⟨⟨hI, hwf_mk hg hch hm⟩, hch, hR, hg⟩
  · obtain ⟨hI, hch, hR⟩ := hsp.2 ⟨ev, hev⟩
    obtain ⟨hg, hm⟩ := hmem_glob (Or.inr ⟨_, ev, hev, by decide⟩)
    exact ⟨⟨hI, hwf_mk hg hch hm⟩, hch, hR⟩

private theorem bv_add_off_nat_g10 (base : BitVec 64) (off : Nat)
    (hbase : base.toNat < heapEnd) (hoff : off ≤ 32) :
    (base + BitVec.ofNat 64 off).toNat = base.toNat + off := by
  rw [R11Shards.heapEnd_val] at hbase
  have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := by norm_num
  have ho_lt : off < 18446744073709551616 := by omega
  have hsum_lt : base.toNat + off < 18446744073709551616 := by omega
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, h264, Nat.mod_eq_of_lt ho_lt, Nat.mod_eq_of_lt hsum_lt]

private theorem eval_var_local_zero_g10 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (nm : String) (base : BitVec 64)
    (hloc : s.locals.lookup (ofString nm) = some (.val (.word base))) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.var .local (ofString nm)) =
      some (.val (.word (base + BitVec.ofNat 64 0))) := by
  have hz : base + BitVec.ofNat 64 0 = base := BitVec.add_zero base
  rw [hz]; exact hloc

private theorem eval_add_local_const_g10 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (nm : String) (base : BitVec 64) (off : Nat)
    (hloc : s.locals.lookup (ofString nm) = some (.val (.word base))) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .local (ofString nm), .const (BitVec.ofNat 64 off)]) =
      some (.val (.word (base + BitVec.ofNat 64 off))) := by
  simp only [evalHOLExact, evalListHOLExact, hloc, wordOpHOL, wordOp, valueIsWord, valueWord,
    List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr]
  have hz : BitVec.ofNat 64 off + (0 : BitVec 64) = BitVec.ofNat 64 off := BitVec.add_zero _
  exact congrArg (fun w => some (ValueHOL.val (HolWordLab.word (base + w)))) hz

private theorem eval_align8_eq0_g10 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (nm : String) (base : BitVec 64)
    (hloc : s.locals.lookup (ofString nm) = some (.val (.word base))) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .equal (.op .and [.var .local (ofString nm), .const 7#64]) (.const 0#64)) =
      some (.val (.word (if (base &&& 7#64) = 0#64 then 1 else 0))) := by
  simp only [evalHOLExact, evalListHOLExact, hloc, wordOpHOL, wordOp, valueIsWord, valueWord,
    List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
    Compiler.Encoders.Asm.wordCmpHOL]
  have h7 : (7#64 : BitVec 64) &&& 18446744073709551615#64 = 7#64 := by decide
  change some (ValueHOL.val (HolWordLab.word (if decide ((base &&& (7#64 &&& 18446744073709551615#64)) = 0#64) = true then 1 else 0))) = _
  rw [h7]
  by_cases hc : (base &&& 7#64) = 0#64 <;> simp [hc]

private theorem return_eff_g10 {F : Type} (s : PanSemStateFiniteExact 64 F) (ex : ExpHOL 64) (Rl : List Ivl) :
    ByteRegionEffect s (evaluateHOLFiniteState s (.return ex)).2 Rl := by
  have hret : (evaluateHOLFiniteState s (.return ex)).2 =
      { s with locals := (evaluateHOLFiniteState s (.return ex)).2.locals } := by
    rw [evaluateHOLFiniteState_return]
    split
    · rfl
    · split <;> rfl
  conv => arg 2; rw [hret]
  exact (ByteRegionEffect.refl s Rl).with_locals_clock _ s.clock

private theorem bswap64_body_ro_g10 {F : Type} (s : PanSemStateFiniteExact 64 F) (Rl : List Ivl) :
    ByteRegionEffect s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_bswap64)).2 Rl := by
  have hb : sourceFnBody Guest.Software.guestFn_bswap64 =
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_bswap64).body := rfl
  rw [hb]
  dsimp only [extractFn, Guest.Software.guestFn_bswap64,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural]
  have hasgn : ∀ (st : PanSemStateFiniteExact 64 F) (nm : MlS) (ex : ExpHOL 64),
      (evaluateHOLFiniteState st (.assign .local nm ex)).2 =
        { st with locals := (evaluateHOLFiniteState st (.assign .local nm ex)).2.locals } := by
    intro st nm ex; rw [evaluateHOLFiniteState_assign]; split <;> [rfl; (split <;> rfl)]
  have hseq_ro : ∀ (st : PanSemStateFiniteExact 64 F) (a b : ProgHOL 64),
      ByteRegionEffect st (evaluateHOLFiniteState st a).2 Rl →
      (∀ m, ByteRegionEffect st m Rl → ByteRegionEffect st (evaluateHOLFiniteState m b).2 Rl) →
      ByteRegionEffect st (evaluateHOLFiniteState st (.seq a b)).2 Rl := by
    intro st a b ha hb'
    rw [evaluateHOLFiniteState_seq_line780]
    rcases h1 : evaluateHOLFiniteState st a with ⟨r1, s1⟩
    rw [h1] at ha
    cases r1 with
    | none => exact hb' s1 ha
    | some _ => exact ha
  have hasgn_eff : ∀ (st : PanSemStateFiniteExact 64 F) (nm : MlS) (ex : ExpHOL 64),
      ByteRegionEffect st (evaluateHOLFiniteState st (.assign .local nm ex)).2 Rl := by
    intro st nm ex
    conv => arg 2; rw [hasgn st nm ex]
    exact (ByteRegionEffect.refl st Rl).with_locals_clock _ st.clock
  refine hseq_ro s _ _ (hasgn_eff s _ _) fun s1 hs1 => ?_
  exact hs1.trans (hseq_ro s1 _ _ (hasgn_eff s1 _ _) (fun s2 hs2 => hs2.trans (return_eff_g10 s2 _ Rl)))

private theorem seq_storeByte_known_eff_g10 {F : Type} {s : PanSemStateFiniteExact 64 F}
    {dstExp valExp : ExpHOL 64} {base : BitVec 64} {off len : Nat} {cont : ProgHOL 64}
    (hbase_lt : base.toNat < heapEnd) (hlen : len ≤ 32) (hoff : off < len)
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
      some (.val (.word (base + BitVec.ofNat 64 off))))
    (hcont : ∀ s1 : PanSemStateFiniteExact 64 F,
      s1.code = s.code → s1.memaddrs = s.memaddrs → s1.locals = s.locals →
      ByteRegionEffect s1 (evaluateHOLFiniteState s1 cont).2 [(base.toNat, len)]) :
    ByteRegionEffect s (evaluateHOLFiniteState s (.seq (.storeByte dstExp valExp) cont)).2 [(base.toNat, len)] := by
  rw [evaluateHOLFiniteState_seq_line780]
  rcases h1 : evaluateHOLFiniteState s (.storeByte dstExp valExp) with ⟨r1, s1⟩
  cases r1 with
  | some _ =>
    have h1' := h1
    rw [evaluateHOLFiniteState_storeByte, hdst] at h1'
    rcases hv : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) valExp with _ | vv
    · rw [hv] at h1'; dsimp only at h1'; injection h1' with _ hs1; subst hs1; exact ByteRegionEffect.refl s _
    · rw [hv] at h1'
      rcases vv with ⟨⟨v⟩⟩ | _ | _
      · dsimp only at h1'; split at h1'
        · cases h1'
        · injection h1' with _ hs1; subst hs1; exact ByteRegionEffect.refl s _
      · dsimp only at h1'; injection h1' with _ hs1; subst hs1; exact ByteRegionEffect.refl s _
      · dsimp only at h1'; injection h1' with _ hs1; subst hs1; exact ByteRegionEffect.refl s _
  | none =>
    have heff1 := ByteRegionEffect.of_storeByte (Rl := [(base.toNat, len)]) h1
      (fun addr ha _ => by
        rw [hdst] at ha
        injection ha with e1; injection e1 with e2; injection e2 with e3; subst e3
        have hnat := bv_add_off_nat_g10 base off hbase_lt (by omega)
        exact ⟨(base.toNat, len), List.mem_singleton.2 rfl, by rw [hnat]; omega, by rw [hnat]; omega⟩)
    exact heff1.1.trans (hcont s1 heff1.1.code heff1.1.memaddrs heff1.2)

private theorem st_be32_known_eff_g10 {F : Type} (s : PanSemStateFiniteExact 64 F) (p : BitVec 64)
    (hp_lt : p.toNat < heapEnd)
    (hp : s.locals.lookup (ofString "p") = some (.val (.word p))) :
    ByteRegionEffect s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_st_be32)).2 [(p.toNat, 4)] := by
  have hb : sourceFnBody Guest.Software.guestFn_st_be32 =
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_st_be32).body := rfl
  rw [hb]
  dsimp only [extractFn, Guest.Software.guestFn_st_be32,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    List.map]
  refine seq_storeByte_known_eff_g10 hp_lt (by omega) (by omega)
    (eval_var_local_zero_g10 s "p" p hp) fun s1 _ _ hl1 => ?_
  have hp1 : s1.locals.lookup (ofString "p") = some (.val (.word p)) := by rw [hl1]; exact hp
  refine seq_storeByte_known_eff_g10 (s := s1) hp_lt (by omega) (by omega)
    (eval_add_local_const_g10 s1 "p" p 1 hp1) fun s2 _ _ hl2 => ?_
  have hp2 : s2.locals.lookup (ofString "p") = some (.val (.word p)) := by rw [hl2]; exact hp1
  refine seq_storeByte_known_eff_g10 (s := s2) hp_lt (by omega) (by omega)
    (eval_add_local_const_g10 s2 "p" p 2 hp2) fun s3 _ _ hl3 => ?_
  have hp3 : s3.locals.lookup (ofString "p") = some (.val (.word p)) := by rw [hl3]; exact hp2
  refine seq_storeByte_known_eff_g10 (s := s3) hp_lt (by omega) (by omega)
    (eval_add_local_const_g10 s3 "p" p 3 hp3) fun s4 _ _ _ => return_eff_g10 s4 _ _

private theorem lookup_two_words_reject_nonword_g10 {width : Nat} [NeZero width]
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (fname p1 p2 : MlS) (body : ProgHOL width) (w1 : BitVec width) (v2 : ValueHOL width)
    (hlook : code fname = some ([(p1, .one), (p2, .one)], body, .one))
    (hnot : ∀ w2 : BitVec width, v2 ≠ .val (.word w2)) :
    lookupCodeHOLFinite code fname [.val (.word w1), v2] = none := by
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite
  split
  · rfl
  · rename_i eb el es hraw
    unfold lookupCodeHOLExact at hraw; rw [hlook] at hraw
    rcases v2 with ⟨⟨w2⟩⟩ | _ | _ <;>
      [exact absurd rfl (hnot w2); simp [shapeOfHOLExact, shapeEqHOL] at hraw; simp [shapeOfHOLExact, shapeEqHOL] at hraw]

private theorem seq_call_st_be32_known_g10 {F : Type} {s : PanSemStateFiniteExact 64 F}
    {pExp vExp : ExpHOL 64} {base : BitVec 64} {off len : Nat} {cont : ProgHOL 64}
    (hcode : s.code = originalRuntimeCode) (hbase_lt : base.toNat + len ≤ heapEnd)
    (hlen : len ≤ 32) (hoff : off + 4 ≤ len)
    (hp_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) pExp =
      some (.val (.word (base + BitVec.ofNat 64 off))))
    (hcont : ∀ s1 : PanSemStateFiniteExact 64 F,
      s1.code = originalRuntimeCode → s1.memaddrs = s.memaddrs → s1.locals = s.locals →
      ByteRegionEffect s1 (evaluateHOLFiniteState s1 cont).2 [(base.toNat, len)]) :
    ByteRegionEffect s
      (evaluateHOLFiniteState s (.seq (.call (some (none, none)) (ofString "st_be32") [pExp, vExp]) cont)).2
      [(base.toNat, len)] := by
  let pArg := base + BitVec.ofNat 64 off
  have hbase_lt0 : base.toNat < heapEnd := by omega
  have hpArg_nat : pArg.toNat = base.toNat + off := bv_add_off_nat_g10 base off hbase_lt0 (by omega)
  have hpArg_lt : pArg.toNat < heapEnd := by rw [hpArg_nat]; omega
  rw [evaluateHOLFiniteState_seq_line780]
  rcases hc : evaluateHOLFiniteState s (.call (some (none, none)) (ofString "st_be32") [pExp, vExp]) with ⟨rc, sc⟩
  rw [evaluateHOLFiniteState_call] at hc
  rcases hv_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) vExp with _ | vv
  · have hnone : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [pExp, vExp] = none := by
      simp [evalListHOLFinite, evalListHOLExact, hp_ev, hv_ev]
    rw [hnone] at hc; injection hc with hr hsc; subst hr hsc; exact ByteRegionEffect.refl s _
  · have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [pExp, vExp] =
        some [.val (.word pArg), vv] := by
      simp [evalListHOLFinite, evalListHOLExact, hp_ev, hv_ev, pArg]
    rw [hargs] at hc; dsimp only at hc
    by_cases hvw : ∃ vW : BitVec 64, vv = .val (.word vW)
    · obtain ⟨vW, rfl⟩ := hvw
      have hl := pan_two_word_lookup s.code.lookup (ofString "st_be32") (ofString "p") (ofString "v")
        (sourceFnBody Guest.Software.guestFn_st_be32) pArg vW (by decide) (by rw [hcode]; exact lookup_st_be32_b)
      rw [hl] at hc; dsimp only at hc
      split at hc
      · injection hc with hr hsc; subst hr hsc; exact (ByteRegionEffect.refl s _).with_locals_clock _ _
      · let entry := callEntryStateHOLFinite s
          ((HolFiniteMapExact.empty.update (ofString "p", .val (.word pArg))).update (ofString "v", .val (.word vW)))
        have hp_in : entry.locals.lookup (ofString "p") = some (.val (.word pArg)) := by
          simp [entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "v" ≠ ofString "p" by decide]
        have heff_b := st_be32_known_eff_g10 entry pArg hpArg_lt hp_in
        rcases hb : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_st_be32) with ⟨rb, sb⟩
        have hb_entry : evaluateHOLFiniteState
            (callEntryStateHOLFinite s
              ((HolFiniteMapExact.empty.update (ofString "p", .val (.word pArg))).update (ofString "v", .val (.word vW))))
            (sourceFnBody Guest.Software.guestFn_st_be32) = (rb, sb) := hb
        rw [hb_entry] at hc; rw [hb] at heff_b; dsimp only at heff_b
        have heff_entry : ByteRegionEffect s entry [(base.toNat, len)] :=
          (ByteRegionEffect.refl s _).with_locals_clock _ _
        have heff_sb : ByteRegionEffect s sb [(base.toNat, len)] :=
          heff_entry.trans (heff_b.mono fun i hi => by
            simp only [List.mem_singleton] at hi; subst hi
            exact ⟨(base.toNat, len), List.mem_singleton.2 rfl, by rw [hpArg_nat]; omega, by rw [hpArg_nat]; omega⟩)
        cases rb with
        | none => injection hc with hr hsc; subst hr hsc; exact heff_sb
        | some r =>
          cases r with
          | returned rv =>
            dsimp only at hc; split at hc
            · injection hc with hr hsc; subst hr hsc; dsimp only
              let s1 : PanSemStateFiniteExact 64 F := { sb with locals := s.locals }
              have heff_s1 : ByteRegionEffect s s1 [(base.toNat, len)] := heff_sb.with_locals_clock _ _
              exact heff_s1.trans (hcont s1 (heff_s1.code.trans hcode) heff_s1.memaddrs rfl)
            · injection hc with hr hsc; subst hr hsc; exact heff_sb
          | timeOut | error | exception _ _ | finalFfi _ =>
            injection hc with hr hsc; subst hr hsc; exact heff_sb.with_locals_clock _ _
          | «break» | «continue» =>
            injection hc with hr hsc; subst hr hsc; exact heff_sb
    · have hln := lookup_two_words_reject_nonword_g10 s.code.lookup (ofString "st_be32") (ofString "p") (ofString "v")
        _ pArg vv (by rw [hcode]; exact lookup_st_be32_b) (fun w hw => hvw ⟨w, hw⟩)
      rw [hln] at hc; injection hc with hr hsc; subst hr hsc; exact ByteRegionEffect.refl s _

private theorem st_be64_known_eff_g10 {F : Type} (s : PanSemStateFiniteExact 64 F) (p : BitVec 64)
    (hcode : s.code = originalRuntimeCode) (hma : s.memaddrs = ordinaryDomain)
    (hp_lt : p.toNat + 8 ≤ heapEnd)
    (hp : s.locals.lookup (ofString "p") = some (.val (.word p))) :
    ByteRegionEffect s (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_st_be64)).2 [(p.toNat, 8)] := by
  have hb : sourceFnBody Guest.Software.guestFn_st_be64 =
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_st_be64).body := rfl
  rw [hb]
  dsimp only [extractFn, Guest.Software.guestFn_st_be64,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    List.map, Option.map]
  have hcond := eval_align8_eq0_g10 s "p" p hp
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite, hcond]
  by_cases hal : (p &&& 7#64) = 0#64
  · simp only [hal, ↓reduceIte]
    have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
    rw [if_neg h10]
    let yesProg : ProgHOL 64 :=
      .decCall (ofString "w") .one (ofString "bswap64") [.var .local (ofString "v")]
        (.seq (.store (.var .local (ofString "p")) (.var .local (ofString "w")))
          (.return (.const 0#64)))
    have hnn_eff : (evaluateHOLFiniteState s yesProg).1 ≠ none ∧
        ByteRegionEffect s (evaluateHOLFiniteState s yesProg).2 [(p.toNat, 8)] := by
      dsimp only [yesProg]
      rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
      rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [.var .local (ofString "v")] with _ | vals
      · exact ⟨by simp, ByteRegionEffect.refl s _⟩
      · dsimp only
        rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "bswap64") vals with _ | ⟨b', cal', rs'⟩
        · exact ⟨by simp, ByteRegionEffect.refl s _⟩
        · dsimp only
          have hinst := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "bswap64")
            _ _ b' _ rs' vals cal' (by rw [hcode]; exact lookup_bswap64_b) hl
          subst hinst
          have hrs_eq : rs' = .one := by
            unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hl
            split at hl
            · cases hl
            · rename_i eb el es hraw
              have hinj := Option.some.inj hl
              rcases Prod.mk.inj hinj with ⟨_, hr2⟩; rcases Prod.mk.inj hr2 with ⟨_, rfl⟩
              unfold lookupCodeHOLExact at hraw; rw [hcode, lookup_bswap64_b] at hraw; dsimp only at hraw
              split at hraw <;> [ (injection hraw with h'; exact (Prod.mk.inj (Prod.mk.inj h').2).2.symm); cases hraw ]
          subst hrs_eq
          split
          · exact ⟨by simp, (ByteRegionEffect.refl s _).with_locals_clock _ _⟩
          · have heff_ent : ByteRegionEffect s (callEntryStateHOLFinite s cal') [(p.toNat, 8)] :=
              (ByteRegionEffect.refl s _).with_locals_clock _ _
            have heff_b := bswap64_body_ro_g10 (callEntryStateHOLFinite s cal') [(p.toNat, 8)]
            rcases hb_run : evaluateHOLFiniteState (callEntryStateHOLFinite s cal')
                (sourceFnBody Guest.Software.guestFn_bswap64) with ⟨rb, sb⟩
            rw [hb_run] at heff_b; dsimp only at heff_b ⊢
            have heff_sb := heff_ent.trans heff_b
            cases rb with
            | none => exact ⟨by simp, heff_sb⟩
            | some r =>
              cases r with
              | returned v =>
                dsimp only; split
                · rename_i hsh_v
                  have hvw : ∃ wv : BitVec 64, v = .val (.word wv) := by
                    rcases v with ⟨⟨wv⟩⟩ | _ | _ <;>
                      [exact ⟨wv, rfl⟩; simp [shapeOfHOLExact, shapeEqHOL] at hsh_v; simp [shapeOfHOLExact, shapeEqHOL] at hsh_v]
                  obtain ⟨wv, rfl⟩ := hvw
                  let mid := setVarHOLFinite (ofString "w") (.val (.word wv)) { sb with locals := s.locals }
                  have heff_mid : ByteRegionEffect s mid [(p.toNat, 8)] := heff_sb.with_locals_clock _ _
                  have hp_mid : @evalHOLExact 64 F _ mid.toExact (fun a => Classical.propDecidable (mid.memaddrs a))
                      (.var .local (ofString "p")) = some (.val (.word p)) := by
                    simp [evalHOLExact, mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hp,
                      show ofString "w" ≠ ofString "p" by decide]
                  have hw_mid : @evalHOLExact 64 F _ mid.toExact (fun a => Classical.propDecidable (mid.memaddrs a))
                      (.var .local (ofString "w")) = some (.val (.word wv)) := by
                    simp [evalHOLExact, mid, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                  rw [evaluateHOLFiniteState_seq_line780]
                  rcases hst_pair : evaluateHOLFiniteState mid
                      (.store (.var .local (ofString "p")) (.var .local (ofString "w"))) with ⟨rst, sst⟩
                  cases rst with
                  | some _ =>
                    have hst' := hst_pair
                    rw [evaluateHOLFiniteState_store, hp_mid, hw_mid] at hst'; dsimp only at hst'
                    split at hst'
                    · cases hst'
                    · injection hst' with _ hsst; subst hsst; exact ⟨by simp, heff_mid.with_locals_clock _ _⟩
                  | none =>
                    have heff_st := ByteRegionEffect.of_store_word (Rl := [(p.toNat, 8)])
                      (heff_mid.memaddrs.trans hma) hst_pair
                      (fun v hv => by rw [hw_mid] at hv; injection hv with h; exact ⟨wv, h.symm⟩)
                      (fun addr ha _ => by
                        rw [hp_mid] at ha
                        injection ha with e1; injection e1 with e2; injection e2 with e3; subst e3
                        exact ⟨(p.toNat, 8), List.mem_singleton.2 rfl, le_refl _, le_refl _⟩)
                    dsimp only
                    have hret0 : (evaluateHOLFiniteState sst (.return (.const 0#64))).1 = some (.returned (.val (.word 0))) := by
                      rw [evaluateHOLFiniteState_return]
                      have he : @evalHOLExact 64 F _ sst.toExact (fun a => Classical.propDecidable (sst.memaddrs a))
                          (.const 0#64) = some (.val (.word 0)) := rfl
                      rw [he]
                      have hsz : sizeOfShapeWithContextHOL sst.structs (shapeOfHOLExact (.val (.word (0 : BitVec 64)))) ≤ 32 := by
                        simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
                      dsimp only; rw [if_pos hsz]
                    rw [hret0]
                    exact ⟨by simp, (heff_mid.trans (heff_st.1.trans (return_eff_g10 sst _ _))).with_locals_clock _ _⟩
                · exact ⟨by simp, heff_sb.with_locals_clock _ _⟩
              | timeOut | error | exception _ _ | finalFfi _ | «break» | «continue» =>
                exact ⟨by simp, heff_sb.with_locals_clock _ _⟩
    rcases hy : evaluateHOLFiniteState s yesProg with ⟨ry, sy⟩
    rw [hy] at hnn_eff
    cases ry with
    | none => exact absurd rfl hnn_eff.1
    | some _ => exact hnn_eff.2
  · simp only [hal, ↓reduceIte, evaluateHOLFiniteState_skip]
    refine seq_call_st_be32_known_g10 hcode hp_lt (by omega) (by omega)
      (eval_var_local_zero_g10 s "p" p hp) fun s1 hc1 _ hl1 => ?_
    have hp1 : s1.locals.lookup (ofString "p") = some (.val (.word p)) := by rw [hl1]; exact hp
    refine seq_call_st_be32_known_g10 (s := s1) hc1 hp_lt (by omega) (by omega)
      (eval_add_local_const_g10 s1 "p" p 4 hp1) fun s2 _ _ _ => return_eff_g10 s2 _ _

private theorem seq_call_st_be64_known_g10 {F : Type} {s : PanSemStateFiniteExact 64 F}
    {pExp vExp : ExpHOL 64} {base : BitVec 64} {off len : Nat} {cont : ProgHOL 64}
    (hcode : s.code = originalRuntimeCode) (hma : s.memaddrs = ordinaryDomain)
    (hbase_lt : base.toNat + len ≤ heapEnd) (hlen : len ≤ 32) (hoff : off + 8 ≤ len)
    (hp_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) pExp =
      some (.val (.word (base + BitVec.ofNat 64 off))))
    (hcont : ∀ s1 : PanSemStateFiniteExact 64 F,
      s1.code = originalRuntimeCode → s1.memaddrs = ordinaryDomain → s1.locals = s.locals →
      ByteRegionEffect s1 (evaluateHOLFiniteState s1 cont).2 [(base.toNat, len)]) :
    ByteRegionEffect s
      (evaluateHOLFiniteState s (.seq (.call (some (none, none)) (ofString "st_be64") [pExp, vExp]) cont)).2
      [(base.toNat, len)] := by
  let pArg := base + BitVec.ofNat 64 off
  have hbase_lt0 : base.toNat < heapEnd := by omega
  have hpArg_nat : pArg.toNat = base.toNat + off := bv_add_off_nat_g10 base off hbase_lt0 (by omega)
  have hpArg_lt : pArg.toNat + 8 ≤ heapEnd := by rw [hpArg_nat]; omega
  rw [evaluateHOLFiniteState_seq_line780]
  rcases hc : evaluateHOLFiniteState s (.call (some (none, none)) (ofString "st_be64") [pExp, vExp]) with ⟨rc, sc⟩
  rw [evaluateHOLFiniteState_call] at hc
  rcases hv_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) vExp with _ | vv
  · have hnone : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [pExp, vExp] = none := by
      simp [evalListHOLFinite, evalListHOLExact, hp_ev, hv_ev]
    rw [hnone] at hc; injection hc with hr hsc; subst hr hsc; exact ByteRegionEffect.refl s _
  · have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [pExp, vExp] =
        some [.val (.word pArg), vv] := by
      simp [evalListHOLFinite, evalListHOLExact, hp_ev, hv_ev, pArg]
    rw [hargs] at hc; dsimp only at hc
    by_cases hvw : ∃ vW : BitVec 64, vv = .val (.word vW)
    · obtain ⟨vW, rfl⟩ := hvw
      have hl := pan_two_word_lookup s.code.lookup (ofString "st_be64") (ofString "p") (ofString "v")
        (sourceFnBody Guest.Software.guestFn_st_be64) pArg vW (by decide) (by rw [hcode]; exact lookup_st_be64_b)
      rw [hl] at hc; dsimp only at hc
      split at hc
      · injection hc with hr hsc; subst hr hsc; exact (ByteRegionEffect.refl s _).with_locals_clock _ _
      · let entry := callEntryStateHOLFinite s
          ((HolFiniteMapExact.empty.update (ofString "p", .val (.word pArg))).update (ofString "v", .val (.word vW)))
        have hp_in : entry.locals.lookup (ofString "p") = some (.val (.word pArg)) := by
          simp [entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "v" ≠ ofString "p" by decide]
        have heff_b := st_be64_known_eff_g10 entry pArg hcode hma hpArg_lt hp_in
        rcases hb : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_st_be64) with ⟨rb, sb⟩
        have hb_entry : evaluateHOLFiniteState
            (callEntryStateHOLFinite s
              ((HolFiniteMapExact.empty.update (ofString "p", .val (.word pArg))).update (ofString "v", .val (.word vW))))
            (sourceFnBody Guest.Software.guestFn_st_be64) = (rb, sb) := hb
        rw [hb_entry] at hc; rw [hb] at heff_b; dsimp only at heff_b
        have heff_entry : ByteRegionEffect s entry [(base.toNat, len)] :=
          (ByteRegionEffect.refl s _).with_locals_clock _ _
        have heff_sb : ByteRegionEffect s sb [(base.toNat, len)] :=
          heff_entry.trans (heff_b.mono fun i hi => by
            simp only [List.mem_singleton] at hi; subst hi
            exact ⟨(base.toNat, len), List.mem_singleton.2 rfl, by rw [hpArg_nat]; omega, by rw [hpArg_nat]; omega⟩)
        cases rb with
        | none => injection hc with hr hsc; subst hr hsc; exact heff_sb
        | some r =>
          cases r with
          | returned rv =>
            dsimp only at hc; split at hc
            · injection hc with hr hsc; subst hr hsc; dsimp only
              let s1 : PanSemStateFiniteExact 64 F := { sb with locals := s.locals }
              have heff_s1 : ByteRegionEffect s s1 [(base.toNat, len)] := heff_sb.with_locals_clock _ _
              exact heff_s1.trans (hcont s1 (heff_s1.code.trans hcode) (heff_s1.memaddrs.trans hma) rfl)
            · injection hc with hr hsc; subst hr hsc; exact heff_sb
          | timeOut | error | exception _ _ | finalFfi _ =>
            injection hc with hr hsc; subst hr hsc; exact heff_sb.with_locals_clock _ _
          | «break» | «continue» =>
            injection hc with hr hsc; subst hr hsc; exact heff_sb
    · have hln := lookup_two_words_reject_nonword_g10 s.code.lookup (ofString "st_be64") (ofString "p") (ofString "v")
        _ pArg vv (by rw [hcode]; exact lookup_st_be64_b) (fun w hw => hvw ⟨w, hw⟩)
      rw [hln] at hc; injection hc with hr hsc; subst hr hsc; exact ByteRegionEffect.refl s _

theorem epsA_to_address_masked :
    EvmPreservingSpecA (fun _ => True)
      (fun s _ post => post.globals = s.globals ∧ evmR post = evmR s)
      (ofString "to_address_masked") := by
  refine ⟨_, _, _, lookup_to_address_masked, ?_⟩
  intro F s hcode hInv hWF _ hlookup hnt
  obtain ⟨params_t, body_t, ret_t, hlk_t, hspec_t⟩ := eps_to_address_masked
  have hlk_eq : some ([(ofString "v", .comb [.one, .one, .one, .one])],
      sourceFnBody Guest.Software.guestFn_to_address_masked, ShapeHOL.one) =
      some (params_t, body_t, ret_t) := lookup_to_address_masked.symm.trans hlk_t
  injection hlk_eq with hprod
  rcases Prod.mk.inj hprod with ⟨rfl, hprod2⟩
  rcases Prod.mk.inj hprod2 with ⟨hbody_t, rfl⟩
  subst hbody_t
  have htm := hspec_t s hcode hInv trivial hlookup hnt
  dsimp only at htm ⊢
  refine ⟨?_, fun ⟨ev, hev⟩ => ?_⟩
  · intro v hv
    obtain ⟨hInv_p, hch_p, hR_le, hg_p, hR_eq⟩ := htm.1 v hv
    have hma : s.memaddrs = ordinaryDomain := hInv.1.1.memaddrs
    obtain ⟨hev_pos, hev_he, hb_ev⟩ := evmInv_head_ev_bounds_g10 hInv
    obtain ⟨evw, hevw_lk, hevw_nat⟩ := global_word_of_pos s "ev" hev_pos
    let aW : BitVec 64 := evw + BitVec.ofNat 64 240
    have haW_nat : aW.toNat = globN s "ev" + 240 := by
      have hev_lt : evw.toNat < heapEnd := by rw [hevw_nat]; omega
      rw [R11Shards.heapEnd_val] at hev_lt
      have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := by norm_num
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, hevw_nat, h264,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    have haW_he : aW.toNat + 20 ≤ heapEnd := by rw [haW_nat]; omega
    have hev_init : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 240)]) =
        some (.val (.word aW)) := by
      simp only [evalHOLExact, evalListHOLExact, hevw_lk, wordOpHOL, wordOp, valueIsWord, valueWord,
        List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr]
      have hz : (240#64 : BitVec 64) + 0 = 240#64 := BitVec.add_zero _
      exact congrArg (fun w => some (ValueHOL.val (HolWordLab.word (evw + w)))) hz
    have heff : ByteRegionEffect s
        (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_to_address_masked)).2
        [(globN s "ev" + 240, 20)] := by
      have hb : sourceFnBody Guest.Software.guestFn_to_address_masked =
          InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
            (extractFn Guest.Software.guestFn_to_address_masked).body := rfl
      rw [hb]
      dsimp only [extractFn, Guest.Software.guestFn_to_address_masked,
        InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
        List.map, Option.map]
      rw [evaluateHOLFiniteState_dec_total]
      dsimp only
      rw [hev_init]
      dsimp only
      have hsh_ok : shapeEqHOL .one (shapeOfHOLExact (.val (.word aW) : ValueHOL 64)) = true := by
        simp [shapeEqHOL, shapeOfHOLExact]
      rw [if_pos hsh_ok]
      dsimp only
      let s0 := setVarHOLFinite (ofString "a") (.val (.word aW)) s
      have hs0_eff : ByteRegionEffect s s0 [(aW.toNat, 20)] :=
        (ByteRegionEffect.refl s _).with_locals_clock _ _
      have ha_s0 : s0.locals.lookup (ofString "a") = some (.val (.word aW)) := by
        simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hbody_eff : ByteRegionEffect s0
          (evaluateHOLFiniteState s0
            (.seq
              (.call (some (none, none)) (ofString "st_be32")
                [.var .local (ofString "a"), .rfield 2 (.var .local (ofString "v"))])
              (.seq
                (.call (some (none, none)) (ofString "st_be64")
                  [.op .add [.var .local (ofString "a"), .const 4#64],
                   .rfield 1 (.var .local (ofString "v"))])
                (.seq
                  (.call (some (none, none)) (ofString "st_be64")
                    [.op .add [.var .local (ofString "a"), .const 12#64],
                     .rfield 0 (.var .local (ofString "v"))])
                  (.return (.var .local (ofString "a"))))))).2
          [(aW.toNat, 20)] := by
        refine seq_call_st_be32_known_g10 hcode haW_he (by omega) (by omega)
          (eval_var_local_zero_g10 s0 "a" aW ha_s0) fun s1 hc1 hm1 hl1 => ?_
        have ha1 : s1.locals.lookup (ofString "a") = some (.val (.word aW)) := by rw [hl1]; exact ha_s0
        refine seq_call_st_be64_known_g10 (s := s1) hc1 (hm1.trans hma) haW_he (by omega) (by omega)
          (eval_add_local_const_g10 s1 "a" aW 4 ha1) fun s2 hc2 hm2 hl2 => ?_
        have ha2 : s2.locals.lookup (ofString "a") = some (.val (.word aW)) := by rw [hl2]; exact ha1
        refine seq_call_st_be64_known_g10 (s := s2) hc2 hm2 haW_he (by omega) (by omega)
          (eval_add_local_const_g10 s2 "a" aW 12 ha2) fun s3 _ _ _ => return_eff_g10 s3 _ _
      rw [← haW_nat]
      exact (hs0_eff.trans hbody_eff).with_locals_clock _ _
    have hWF_p : Group10.HeadMemChainWF
        (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_to_address_masked)).2 := by
      refine headMemChainWF_of_headSafe hInv hWF hch_p
        (congrFun (globN_congr hg_p) "ev") (congrFun (globN_congr hg_p) "frame_mem_ptr") ?_
      intro x hx
      by_cases hx_dom : s.memaddrs x
      · have hx8 : x.toNat % 8 = 0 := by
          rw [hma, ordinaryDomain_iff] at hx_dom; exact hx_dom.2.2
        have hev8 : globN s "ev" % 8 = 0 := by
          obtain ⟨_, _, _, _, _, _, hFW_all, _⟩ := hInv
          exact ((hFW_all (globN s "ev", globN s "cur_cont")
            (by simp [evmChain, evmChainFrom])).1 (globN s "ev", 280) (by simp)).2.1
        refine heff.cell_frame x fun r hr => ?_
        simp only [List.mem_singleton] at hr; subst hr
        intro ⟨hc1, hc2⟩
        dsimp only at hc1 hc2
        have hx_in : ∃ k, x.toNat = globN s "ev" + k ∧ 240 ≤ k ∧ k < 280 := by
          exact ⟨x.toNat - globN s "ev", by omega, by omega, by omega⟩
        obtain ⟨k, hxk, hk1, hk2⟩ := hx_in
        exact hx (Or.inl ⟨k, hxk, hk2, by omega, by omega, by omega⟩)
      · exact heff.out_dom x hx_dom
    exact ⟨⟨hInv_p, hWF_p⟩, hch_p, hR_le, hg_p, hR_eq⟩
  · have hnc := evaluate_noCatchableRaise warmAccessNcrCallees warmAccessNcrCallees_good
      (sourceFnBody Guest.Software.guestFn_to_address_masked) (by decide) s hcode
    exact False.elim (hnc (ofString "EvmErr") ev (by decide) hev)

private def HeadSafeValProg : ExpHOL 64 → Bool
  | .const _ | .op _ _ | .shift _ _ _ | .cmp _ _ _ => true
  | _ => false

private def HeadSafeStoreProg (dst val : ExpHOL 64) : Bool :=
  match dst with
  | .op .add [.var .global g, .const k] =>
    (g == ofString "ev") &&
    decide (k.toNat + 8 ≤ 280 ∧ k.toNat % 8 = 0 ∧ k.toNat ≠ 24 ∧ k.toNat ≠ 32 ∧ k.toNat ≠ 40) &&
    HeadSafeValProg val
  | _ => false

private def headSafeProg' (good : MlS → Bool) : ProgHOL 64 → Bool
  | .dec _ _ _ body => headSafeProg' good body
  | .seq first second => headSafeProg' good first && headSafeProg' good second
  | .ite _ yes no => headSafeProg' good yes && headSafeProg' good no
  | .decCall _ _ fname _ cont => good fname && headSafeProg' good cont
  | .store dst val => HeadSafeStoreProg dst val
  | .assign .local _ _ => true
  | .primitive _ _ _ => true
  | .skip | .break | .continue | .annot _ _ | .raise _ _ | .return _ => true
  | _ => false

private def HeadSafeStep {F : Type} (s post : PanSemStateFiniteExact 64 F) : Prop :=
  post.code = s.code ∧ post.globals = s.globals ∧
    ∀ a : BitVec 64, ¬ HeadSafeAddr (globN s "ev") (globN s "cur_cont") a.toNat → post.memory a = s.memory a

private theorem HeadSafeStep.of_locFrame {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (h : LocFrame s post) : HeadSafeStep s post := by
  refine ⟨by unfold LocFrame at h; rw [h], by unfold LocFrame at h; rw [h], fun a _ => ?_⟩
  unfold LocFrame at h; rw [h]

private theorem HeadSafeStep.trans {F : Type} {s m post : PanSemStateFiniteExact 64 F}
    (h1 : HeadSafeStep s m) (h2 : HeadSafeStep m post) : HeadSafeStep s post := by
  refine ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, fun a ha => ?_⟩
  have hev : globN m "ev" = globN s "ev" := congrFun (globN_congr h1.2.1) "ev"
  have hcc : globN m "cur_cont" = globN s "cur_cont" := congrFun (globN_congr h1.2.1) "cur_cont"
  exact (h2.2.2 a (by rw [hev, hcc]; exact ha)).trans (h1.2.2 a ha)

private theorem HeadSafeStep.with_locals_clock {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (h : HeadSafeStep s post) (L : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    HeadSafeStep s { post with locals := L, clock := k } := h

private def HeadSafeOrTrapped {F : Type} (s : PanSemStateFiniteExact 64 F)
    (out : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 F) : Prop :=
  HeadSafeStep s out.2 ∨
    (out.1 ≠ none ∧ out.1 ≠ some .continue ∧ out.1 ≠ some .break ∧ ¬ Resumes out.1)

private theorem HeadSafeOrTrapped.to_resumes {F : Type} {s : PanSemStateFiniteExact 64 F}
    {out : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 F}
    (h : HeadSafeOrTrapped s out) (hr : Resumes out.1) : HeadSafeStep s out.2 :=
  h.elim id (fun ⟨_, _, _, hnr⟩ => (hnr hr).elim)

private theorem headSafeValProg_word {F : Type} (s : PanSemStateFiniteExact 64 F)
    (val : ExpHOL 64) (hshape : HeadSafeValProg val = true)
    (vv : ValueHOL 64)
    (hv : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) val = some vv) :
    ∃ w : BitVec 64, vv = .val (.word w) := by
  cases val with
  | const w =>
    simp [evalHOLExact] at hv; exact ⟨w, hv.symm⟩
  | op op es =>
    simp [evalHOLExact] at hv
    rcases hes : @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) es with _ | vs
    · rw [hes] at hv; simp at hv
    · rw [hes] at hv; dsimp only at hv
      split at hv
      · rcases hw : wordOpHOL op (List.map valueWord vs) with _ | w
        · rw [hw] at hv; simp at hv
        · rw [hw] at hv; simp at hv; exact ⟨w, hv.symm⟩
      · simp at hv
  | shift sh e n =>
    simp [evalHOLExact] at hv
    rcases he : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e with _ | ev
    · rw [he] at hv; simp at hv
    · rw [he] at hv
      rcases hn : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) n with _ | nv
      · rw [hn] at hv; rcases ev with ⟨⟨_⟩⟩ | _ | _ <;> simp at hv
      · rw [hn] at hv
        rcases ev with ⟨⟨w1⟩⟩ | _ | _ <;> rcases nv with ⟨⟨w2⟩⟩ | _ | _ <;> try simp at hv
        rcases hs_w : wordShiftHOL sh w1 w2.toNat with _ | w
        · rw [hs_w] at hv; simp at hv
        · rw [hs_w] at hv; simp at hv; exact ⟨w, hv.symm⟩
  | cmp c e1 e2 =>
    simp [evalHOLExact] at hv
    rcases he1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e1 with _ | v1
    · rw [he1] at hv; simp at hv
    · rw [he1] at hv
      rcases he2 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e2 with _ | v2
      · rw [he2] at hv; simp at hv
      · rw [he2] at hv
        rcases v1 with ⟨⟨w1⟩⟩ | _ | _ <;> rcases v2 with ⟨⟨w2⟩⟩ | _ | _ <;> simp at hv
        exact ⟨_, hv.symm⟩
  | _ => simp [HeadSafeValProg] at hshape

private theorem readOnlyProg_mono_g10 {g1 g2 : MlS → Bool}
    (himp : ∀ f, g1 f = true → g2 f = true) :
    ∀ (p : ProgHOL 64), readOnlyProg g1 p = true → readOnlyProg g2 p = true := by
  intro p hp
  cases shape : p with
  | dec _ _ _ body =>
    have hb : readOnlyProg g1 body = true := by simpa [shape, readOnlyProg] using hp
    exact readOnlyProg_mono_g10 himp body hb
  | seq a b =>
    have hab : readOnlyProg g1 a = true ∧ readOnlyProg g1 b = true := by
      simpa [shape, readOnlyProg, Bool.and_eq_true] using hp
    simp [readOnlyProg, readOnlyProg_mono_g10 himp a hab.1, readOnlyProg_mono_g10 himp b hab.2]
  | ite _ a b =>
    have hab : readOnlyProg g1 a = true ∧ readOnlyProg g1 b = true := by
      simpa [shape, readOnlyProg, Bool.and_eq_true] using hp
    simp [readOnlyProg, readOnlyProg_mono_g10 himp a hab.1, readOnlyProg_mono_g10 himp b hab.2]
  | «while» _ body =>
    have hb : readOnlyProg g1 body = true := by simpa [shape, readOnlyProg] using hp
    exact readOnlyProg_mono_g10 himp body hb
  | decCall _ _ fn _ cont =>
    have hc : g1 fn = true ∧ readOnlyProg g1 cont = true := by
      simpa [shape, readOnlyProg, Bool.and_eq_true] using hp
    simp [readOnlyProg, himp fn hc.1, readOnlyProg_mono_g10 himp cont hc.2]
  | call ret fn _ =>
    rcases ret with _ | ⟨dest, hdl⟩
    · have hfn : g1 fn = true := by simpa [shape, readOnlyProg] using hp
      simp [readOnlyProg, himp fn hfn]
    · rcases hdl with _ | _
      · rcases dest with _ | ⟨vk, _⟩
        · have hor : (fn == ofString "trap_with") = true ∨ g1 fn = true := by
            simpa [shape, readOnlyProg, Bool.or_eq_true] using hp
          rcases hor with htr | hfn
          · simp [readOnlyProg, htr]
          · simp [readOnlyProg, himp fn hfn]
        · cases vk with
          | global => simp [shape, readOnlyProg] at hp
          | «local» =>
            have hfn : g1 fn = true := by simpa [shape, readOnlyProg] using hp
            simp [readOnlyProg, himp fn hfn]
      · simp [shape, readOnlyProg] at hp
  | assign vk _ _ =>
    cases vk <;> simp [shape, readOnlyProg] at hp ⊢
  | primitive _ _ _ | skip | «break» | «continue» | annot _ _ | raise _ _ | «return» _ =>
    simp [readOnlyProg]
  | _ => simp [shape, readOnlyProg] at hp
termination_by p => sizeOf p
decreasing_by
  all_goals
    simp_wf
    subst shape
    simp +arith [ProgHOL.seq.sizeOf_spec, ProgHOL.ite.sizeOf_spec, ProgHOL.dec.sizeOf_spec,
      ProgHOL.while.sizeOf_spec, ProgHOL.decCall.sizeOf_spec]

private theorem evaluate_headSafeProg {F : Type} (good : MlS → Bool)
    (hgood : ∀ function, good function = true → ∀ values body callee rs,
      PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup function values =
        some (body, callee, rs) →
      readOnlyProg good body = true)
    (program : ProgHOL 64) (supported : headSafeProg' good program = true)
    (state : PanSemStateFiniteExact 64 F) (code : state.code = originalRuntimeCode)
    (hev_pos : 0 < globN state "ev") (hev_bnd : globN state "ev" + 280 ≤ 2 ^ 64) :
    HeadSafeOrTrapped state (evaluateHOLFiniteState state program) := by
  cases shape : program with
  | skip =>
    rw [evaluateHOLFiniteState_skip]; exact Or.inl ⟨rfl, rfl, fun _ _ => rfl⟩
  | «break» =>
    rw [evaluateHOLFiniteState_break]; exact Or.inl ⟨rfl, rfl, fun _ _ => rfl⟩
  | «continue» =>
    rw [evaluateHOLFiniteState_continue]; exact Or.inl ⟨rfl, rfl, fun _ _ => rfl⟩
  | annot _ _ =>
    rw [evaluateHOLFiniteState_annot]; exact Or.inl ⟨rfl, rfl, fun _ _ => rfl⟩
  | raise _ _ =>
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only; split <;> exact Or.inl ⟨rfl, rfl, fun _ _ => rfl⟩
    · exact Or.inl ⟨rfl, rfl, fun _ _ => rfl⟩
  | «return» _ =>
    rw [evaluateHOLFiniteState_return]
    split
    · exact Or.inl ⟨rfl, rfl, fun _ _ => rfl⟩
    · split <;> exact Or.inl ⟨rfl, rfl, fun _ _ => rfl⟩
  | assign kind _ _ =>
    cases kind with
    | global => simp [shape, headSafeProg'] at supported
    | «local» =>
      rw [evaluateHOLFiniteState_assign]
      split
      · exact Or.inl ⟨rfl, rfl, fun _ _ => rfl⟩
      · split <;> exact Or.inl ⟨rfl, rfl, fun _ _ => rfl⟩
  | primitive _ _ _ =>
    rw [evaluateHOLFiniteState_primitive]
    split
    · exact Or.inl ⟨rfl, rfl, fun _ _ => rfl⟩
    · split
      · exact Or.inl ⟨rfl, rfl, fun _ _ => rfl⟩
      · split <;> exact Or.inl ⟨rfl, rfl, fun _ _ => rfl⟩
  | dec name _ expr body =>
    have child : headSafeProg' good body = true := by simpa [shape, headSafeProg'] using supported
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · exact Or.inl ⟨rfl, rfl, fun _ _ => rfl⟩
    · rename_i v _
      split
      · have ih := evaluate_headSafeProg good hgood body child (setVarHOLFinite name v state) code hev_pos hev_bnd
        rcases hrun : evaluateHOLFiniteState (setVarHOLFinite name v state) body with ⟨r, st⟩
        rw [hrun] at ih; dsimp only at ih ⊢
        rcases ih with hstep | htrap
        · exact Or.inl ⟨hstep.1, hstep.2.1, hstep.2.2⟩
        · exact Or.inr htrap
      · exact Or.inl ⟨rfl, rfl, fun _ _ => rfl⟩
  | seq first second =>
    have children : headSafeProg' good first = true ∧ headSafeProg' good second = true := by
      simpa only [shape, headSafeProg', Bool.and_eq_true] using supported
    have ih1 := evaluate_headSafeProg good hgood first children.1 state code hev_pos hev_bnd
    have remaining := evaluateHOLFiniteState_clock_le state first
    rw [evaluateHOLFiniteState_seq_line780]
    rcases firstRun : evaluateHOLFiniteState state first with ⟨result, middle⟩
    rw [firstRun] at ih1 remaining; dsimp only at ih1 remaining ⊢
    cases result with
    | none =>
      rcases ih1 with hstep1 | ⟨hnn, _⟩
      · dsimp only at hstep1
        have mclock : middle.clock ≤ state.clock := remaining
        have hev_m : globN middle "ev" = globN state "ev" := congrFun (globN_congr hstep1.2.1) "ev"
        have ih2 := evaluate_headSafeProg good hgood second children.2 middle
          (hstep1.1.trans code) (by rw [hev_m]; exact hev_pos) (by rw [hev_m]; exact hev_bnd)
        rcases ih2 with hstep2 | htrap2
        · exact Or.inl (hstep1.trans hstep2)
        · exact Or.inr htrap2
      · exact absurd rfl hnn
    | some r =>
      rcases ih1 with hstep1 | ⟨_, hnc, hnb, hnr⟩
      · exact Or.inl hstep1
      · exact Or.inr ⟨by simp, hnc, hnb, hnr⟩
  | ite condition yes no =>
    have children : headSafeProg' good yes = true ∧ headSafeProg' good no = true := by
      simpa only [shape, headSafeProg', Bool.and_eq_true] using supported
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_headSafeProg good hgood no children.2 state code hev_pos hev_bnd
      · exact evaluate_headSafeProg good hgood yes children.1 state code hev_pos hev_bnd
    · exact Or.inl ⟨rfl, rfl, fun _ _ => rfl⟩
  | decCall name _ function arguments continuation =>
    have children : good function = true ∧ headSafeProg' good continuation = true := by
      simpa only [shape, headSafeProg', Bool.and_eq_true] using supported
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
    rcases hargs : evalListHOLFinite state
        (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments with _ | values
    · exact Or.inl ⟨rfl, rfl, fun _ _ => rfl⟩
    · dsimp only
      rcases found : PanSemStateFiniteExact.lookupCodeHOLFinite state.code.lookup function values with _ | ⟨body, callee, rs⟩
      · exact Or.inl ⟨rfl, rfl, fun _ _ => rfl⟩
      · dsimp only
        have found' : PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup function values =
            some (body, callee, rs) := by rwa [← code]
        have bodyOk := hgood function children.1 values body callee rs found'
        split
        · exact Or.inl ⟨rfl, rfl, fun _ _ => rfl⟩
        · have ih := evaluate_readOnlyProg good hgood body bodyOk
            (callEntryStateHOLFinite state callee) code
          have cl := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite state callee) body
          rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with ⟨res, st⟩
          rw [hrun] at ih cl; dsimp only at ih cl ⊢
          change st.clock ≤ state.clock - 1 at cl
          have small : st.clock < state.clock := by omega
          cases res with
          | none =>
            rcases ih with hloc | ⟨hnn, _⟩
            · dsimp only at hloc
              have ih' : LocFrame state st := by unfold LocFrame at hloc ⊢; rw [hloc]; rfl
              exact Or.inl (HeadSafeStep.of_locFrame ih')
            · exact absurd rfl hnn
          | some r =>
            cases r with
            | returned v =>
              have hloc : LocFrame (callEntryStateHOLFinite state callee) st :=
                ih.to_resumes (Or.inl ⟨v, rfl⟩)
              have ih' : LocFrame state st := by unfold LocFrame at hloc ⊢; rw [hloc]; rfl
              dsimp only
              split
              · set resumed := setVarHOLFinite name v { st with locals := state.locals }
                have smallR : resumed.clock < state.clock := small
                have ihR : HeadSafeStep state resumed :=
                  (HeadSafeStep.of_locFrame ih').with_locals_clock _ _
                have hev_r : globN resumed "ev" = globN state "ev" :=
                  congrFun (globN_congr ihR.2.1) "ev"
                have ih2 := evaluate_headSafeProg good hgood continuation children.2 resumed
                  (ihR.1.trans code) (by rw [hev_r]; exact hev_pos) (by rw [hev_r]; exact hev_bnd)
                rcases hcont : evaluateHOLFiniteState resumed continuation with ⟨res2, st2⟩
                rw [hcont] at ih2
                rcases ih2 with hstep2 | ⟨hnn2, hnc2, hnb2, hnr2⟩
                · exact Or.inl ((ihR.trans hstep2).with_locals_clock _ _)
                · exact Or.inr ⟨hnn2, hnc2, hnb2, hnr2⟩
              · exact Or.inl (HeadSafeStep.of_locFrame ih')
            | timeOut | error | exception _ _ | finalFfi _ =>
              rcases ih with hloc | ⟨_, _, _, hnr⟩
              · dsimp only at hloc
                have ih' : LocFrame state st := by unfold LocFrame at hloc ⊢; rw [hloc]; rfl
                exact Or.inl ((HeadSafeStep.of_locFrame ih').with_locals_clock _ _)
              · exact Or.inr ⟨by simp, by simp, by simp, hnr⟩
            | «break» | «continue» =>
              rcases ih with hloc | _
              · dsimp only at hloc
                have ih' : LocFrame state st := by unfold LocFrame at hloc ⊢; rw [hloc]; rfl
                exact Or.inl (HeadSafeStep.of_locFrame ih')
              · exact Or.inr ⟨by simp, by simp, by simp,
                  by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h⟩
  | store dst val =>
    have hdst : HeadSafeStoreProg dst val = true := by simpa [shape, headSafeProg'] using supported
    cases dst with
    | op op es =>
      cases op <;> try simp [HeadSafeStoreProg] at hdst
      rcases es with _ | ⟨e1, _ | ⟨e2, _ | _⟩⟩ <;> try simp [HeadSafeStoreProg] at hdst
      cases e1 with
      | var vk g =>
        cases vk <;> try simp [HeadSafeStoreProg] at hdst
        cases e2 with
        | const k =>
          simp only [HeadSafeStoreProg, beq_iff_eq, decide_eq_true_eq, Bool.and_eq_true] at hdst
          obtain ⟨⟨rfl, hk_le, hk8, hk24, hk32, hk40⟩, hval_sh⟩ := hdst
          obtain ⟨evw, hevw, hevw_nat⟩ := global_word_of_pos state "ev" hev_pos
          rcases hst : evaluateHOLFiniteState state (.store (.op .add [.var .global (ofString "ev"), .const k]) val) with ⟨r, post⟩
          cases r with
          | some res =>
            have herr := store_some_eq_error_g10 hst; subst herr
            exact Or.inr ⟨by simp, by simp, by simp, by rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h⟩
          | none =>
            rw [evaluateHOLFiniteState_store] at hst
            have had_ev : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a))
                (.op .add [.var .global (ofString "ev"), .const k]) = some (.val (.word (evw + k))) := by
              simp [evalHOLExact, evalListHOLExact, hevw, wordOpHOL, wordOp, valueIsWord, valueWord]
            rw [had_ev] at hst; dsimp only at hst
            rcases hv : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a)) val with _ | vv
            · rw [hv] at hst; simp at hst
            · obtain ⟨vw, rfl⟩ := headSafeValProg_word state val hval_sh vv hv
              rw [hv] at hst; dsimp only at hst
              have hfl_vw : flattenHOL (.val (.word vw) : ValueHOL 64) = [.word vw] := by
                simp [flattenHOL]
              rw [hfl_vw] at hst
              simp only [panMemStoresHOL, panMemStoreHOL] at hst
              by_cases hdom : state.memaddrs (evw + k)
              · simp only [hdom, ↓reduceIte] at hst
                injection hst with _ hp_eq; subst hp_eq
                refine Or.inl ⟨rfl, rfl, fun a ha => ?_⟩
                have hk_nat : (evw + k).toNat = globN state "ev" + k.toNat := by
                  rw [BitVec.toNat_add, hevw_nat, Nat.mod_eq_of_lt (by omega)]
                have hk24' : k.toNat ≠ 24 := by simpa using hk24
                have hk32' : k.toNat ≠ 32 := by simpa using hk32
                have hk40' : k.toNat ≠ 40 := by simpa using hk40
                have hne : a ≠ evw + k := by
                  rintro rfl
                  exact ha (Or.inl ⟨k.toNat, hk_nat, by omega, hk24', hk32', hk40'⟩)
                dsimp only; rw [if_neg hne]
              · simp only [hdom, ↓reduceIte] at hst; simp at hst
        | _ => simp [HeadSafeStoreProg] at hdst
      | _ => simp [HeadSafeStoreProg] at hdst
    | _ => simp [HeadSafeStoreProg] at hdst
  | _ => simp [shape, headSafeProg'] at supported
termination_by (state.clock, sizeOf program)
decreasing_by
  all_goals
    simp_wf
    apply GuestGlobalKeep.lex_of
    try subst shape
    try simp only [setVarHOLFinite, decClockHOLFinite, callEntryStateHOLFinite,
      ProgHOL.seq.sizeOf_spec, ProgHOL.ite.sizeOf_spec, ProgHOL.dec.sizeOf_spec,
      ProgHOL.decCall.sizeOf_spec, true_and]
    first
      | exact Or.inl smallR
      | exact Or.inl small
      | (rcases Nat.lt_or_eq_of_le mclock with h | h
         · exact Or.inl h
         · exact Or.inr (And.intro h (by simp +arith)))
      | exact Or.inr (by simp +arith)

private def stateGasRoCallees (f : MlS) : Bool :=
  f == ofString "min" || opRoCallees f

private theorem stateGasRoCallees_good :
    ∀ function, stateGasRoCallees function = true → ∀ values body callee rs,
      PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup function values =
        some (body, callee, rs) →
      readOnlyProg stateGasRoCallees body = true := by
  intro function hfn values body callee rs hfound
  simp only [stateGasRoCallees, Bool.or_eq_true, beq_iff_eq] at hfn
  rcases hfn with rfl | hop
  · exact installed_body_readOnly 31 (by rw [guestAst_len]; decide)
      Guest.Software.guestFn_min rfl stateGasRoCallees (by decide) hfound
  · exact readOnlyProg_mono_g10 (fun f hf => by simp [stateGasRoCallees, hf]) body
      (opRoCallees_good function hop values body callee rs hfound)

theorem epsA_charge_state_gas :
    EvmPreservingSpecA (fun _ => True)
      (fun s _ post => post.globals = s.globals)
      (ofString "charge_state_gas") := by
  obtain ⟨params, body, retShape, hlk, hspec⟩ := eps_charge_state_gas
  have hlk_eq := lookup_charge_state_gas_b.symm.trans hlk
  injection hlk_eq with hprod
  rcases Prod.mk.inj hprod with ⟨rfl, hprod2⟩
  rcases Prod.mk.inj hprod2 with ⟨hbody_eq, rfl⟩
  subst hbody_eq
  refine ⟨_, _, _, lookup_charge_state_gas_b, ?_⟩
  intro F s hcode hInv hHMWF hP hlookup hnt
  have hs := hspec s hcode hInv hP hlookup hnt
  obtain ⟨hev_pos, _, hev_bnd⟩ := evmInv_head_ev_bounds_g10 hInv
  have hhs := evaluate_headSafeProg stateGasRoCallees stateGasRoCallees_good
    (sourceFnBody Guest.Software.guestFn_charge_state_gas) (by decide) s hcode hev_pos hev_bnd
  rcases hrun : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_charge_state_gas) with ⟨r, post⟩
  rw [hrun] at hs hhs; dsimp only at hs hhs ⊢
  refine ⟨fun v hv => ?_, fun herr => ?_⟩
  · obtain ⟨hInv_p, hch, hR, hg⟩ := hs.1 v hv
    have hstep := hhs.to_resumes (Or.inl ⟨v, hv⟩)
    dsimp only at hstep
    have hev_eq : globN post "ev" = globN s "ev" := congrFun (globN_congr hg) "ev"
    have hfmp_eq : globN post "frame_mem_ptr" = globN s "frame_mem_ptr" := congrFun (globN_congr hg) "frame_mem_ptr"
    exact ⟨⟨hInv_p, headMemChainWF_of_headSafe hInv hHMWF hch hev_eq hfmp_eq hstep.2.2⟩, hch, hR, hg⟩
  · obtain ⟨hInv_p, hch, hR⟩ := hs.2 herr
    obtain ⟨ev, hev⟩ := herr
    have hstep := hhs.to_resumes (Or.inr ⟨_, ev, hev, by decide⟩)
    dsimp only at hstep
    have hev_eq : globN post "ev" = globN s "ev" := congrFun (globN_congr hstep.2.1) "ev"
    have hfmp_eq : globN post "frame_mem_ptr" = globN s "frame_mem_ptr" := congrFun (globN_congr hstep.2.1) "frame_mem_ptr"
    exact ⟨⟨hInv_p, headMemChainWF_of_headSafe hInv hHMWF hch hev_eq hfmp_eq hstep.2.2⟩, hch, hR⟩

theorem epsA_credit_state_gas_refund :
    EvmPreservingSpecA (fun _ => True)
      (fun s _ post => post.globals = s.globals)
      (ofString "credit_state_gas_refund") := by
  obtain ⟨params, body, retShape, hlk, hspec⟩ := eps_credit_state_gas_refund
  have hlk_eq := lookup_credit_state_gas_refund_b.symm.trans hlk
  injection hlk_eq with hprod
  rcases Prod.mk.inj hprod with ⟨rfl, hprod2⟩
  rcases Prod.mk.inj hprod2 with ⟨hbody_eq, rfl⟩
  subst hbody_eq
  refine ⟨_, _, _, lookup_credit_state_gas_refund_b, ?_⟩
  intro F s hcode hInv hHMWF hP hlookup hnt
  have hs := hspec s hcode hInv hP hlookup hnt
  obtain ⟨hev_pos, _, hev_bnd⟩ := evmInv_head_ev_bounds_g10 hInv
  have hhs := evaluate_headSafeProg stateGasRoCallees stateGasRoCallees_good
    (sourceFnBody Guest.Software.guestFn_credit_state_gas_refund) (by decide) s hcode hev_pos hev_bnd
  rcases hrun : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_credit_state_gas_refund) with ⟨r, post⟩
  rw [hrun] at hs hhs; dsimp only at hs hhs ⊢
  refine ⟨fun v hv => ?_, fun herr => ?_⟩
  · obtain ⟨hInv_p, hch, hR, hg⟩ := hs.1 v hv
    have hstep := hhs.to_resumes (Or.inl ⟨v, hv⟩)
    dsimp only at hstep
    have hev_eq : globN post "ev" = globN s "ev" := congrFun (globN_congr hg) "ev"
    have hfmp_eq : globN post "frame_mem_ptr" = globN s "frame_mem_ptr" := congrFun (globN_congr hg) "frame_mem_ptr"
    exact ⟨⟨hInv_p, headMemChainWF_of_headSafe hInv hHMWF hch hev_eq hfmp_eq hstep.2.2⟩, hch, hR, hg⟩
  · obtain ⟨hInv_p, hch, hR⟩ := hs.2 herr
    obtain ⟨ev, hev⟩ := herr
    have hstep := hhs.to_resumes (Or.inr ⟨_, ev, hev, by decide⟩)
    dsimp only at hstep
    have hev_eq : globN post "ev" = globN s "ev" := congrFun (globN_congr hstep.2.1) "ev"
    have hfmp_eq : globN post "frame_mem_ptr" = globN s "frame_mem_ptr" := congrFun (globN_congr hstep.2.1) "frame_mem_ptr"
    exact ⟨⟨hInv_p, headMemChainWF_of_headSafe hInv hHMWF hch hev_eq hfmp_eq hstep.2.2⟩, hch, hR⟩

theorem headMemChainWF_of_unhit_g10 {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hInv : EvmInv s) (hs : Group10.HeadMemChainWF s)
    (hchain : evmChain post = evmChain s)
    (hu : ∀ ec ∈ evmChain s, R16Shards.IvlUnhit s post (ec.1, 280) ∧
      R16Shards.IvlUnhit s post (ec.2, 104))
    (hev : globN post "ev" = globN s "ev")
    (hfmp : globN post "frame_mem_ptr" = globN s "frame_mem_ptr") :
    Group10.HeadMemChainWF post := by
  obtain ⟨hAs, S, _, _, _, _, hFWF, _⟩ := hInv
  refine Group10.headMemChainWF_of_agree hs hchain ?_ hev hfmp
  intro ec hec
  have hwf := hFWF ec hec
  obtain ⟨he_lt, hc_lt, _, _⟩ := frameWF_bounds hAs.2 hwf
  have he8 : ec.1 % 8 = 0 := (hwf.1 (ec.1, 280) (by simp)).2.1
  have hc8 : ec.2 % 8 = 0 := (hwf.1 (ec.2, 104) (by simp)).2.1
  obtain ⟨hue, huc⟩ := hu ec hec
  exact ⟨R16Shards.memW_eq_of_ivlUnhit hue (by omega) he_lt ⟨by omega, by omega⟩,
    R16Shards.memW_eq_of_ivlUnhit hue (by omega) he_lt ⟨by omega, by omega⟩,
    R16Shards.memW_eq_of_ivlUnhit hue (by omega) he_lt ⟨by omega, by omega⟩,
    R16Shards.memW_eq_of_ivlUnhit huc (by omega) hc_lt ⟨by omega, by omega⟩⟩

private theorem three_one_word_call_args_g10 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (fn : MlS) (e1 e2 e3 : ExpHOL 64)
    (body : ProgHOL 64) (retShape : ShapeHOL)
    (p1 p2 p3 : MlS)
    (hcode : s.code.lookup fn = some ([(p1, .one), (p2, .one), (p3, .one)], body, retShape))
    (hok : (evaluateHOLFiniteState s (.call (some (none, none)) fn [e1, e2, e3])).1 ≠ some .error) :
    ∃ w1 w2 w3 : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e1 = some (.val (.word w1)) ∧
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e2 = some (.val (.word w2)) ∧
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e3 = some (.val (.word w3)) := by
  rw [evaluateHOLFiniteState_call] at hok
  rcases hv1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e1 with _ | v1
  · simp [evalListHOLFinite, evalListHOLExact, hv1] at hok
  · rcases hv2 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e2 with _ | v2
    · simp [evalListHOLFinite, evalListHOLExact, hv1, hv2] at hok
    · rcases hv3 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e3 with _ | v3
      · simp [evalListHOLFinite, evalListHOLExact, hv1, hv2, hv3] at hok
      · have hevl : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [e1, e2, e3] =
            some [v1, v2, v3] := by
          simp [evalListHOLFinite, evalListHOLExact, hv1, hv2, hv3]
        rw [hevl] at hok; dsimp only at hok
        rcases hl : PanSemStateFiniteExact.lookupCodeHOLFinite s.code.lookup fn [v1, v2, v3] with _ | ⟨b, c, rs⟩
        · rw [hl] at hok; exact absurd rfl hok
        · have hraw : lookupCodeHOLExact s.code.lookup fn [v1, v2, v3] ≠ none := by
            intro hn
            unfold PanSemStateFiniteExact.lookupCodeHOLFinite at hl
            split at hl
            · simp at hl
            · rename_i hsome; rw [hn] at hsome; simp at hsome
          simp only [lookupCodeHOLExact, hcode, List.length_cons, List.length_nil, ↓reduceIte,
            List.zip, List.zipWith, List.all, Bool.and_true, Bool.and_eq_true] at hraw
          have hshapes : shapeEqHOL .one (shapeOfHOLExact v1) = true ∧
              shapeEqHOL .one (shapeOfHOLExact v2) = true ∧
              shapeEqHOL .one (shapeOfHOLExact v3) = true := by
            by_contra hns; simp [hns] at hraw
          have hw : ∀ v : ValueHOL 64, shapeEqHOL .one (shapeOfHOLExact v) = true → ∃ w, v = .val (.word w) := by
            intro v hsv
            rcases v with ⟨⟨w⟩⟩ | _ | _
            · exact ⟨w, rfl⟩
            · simp [shapeOfHOLExact, shapeEqHOL] at hsv
            · simp [shapeOfHOLExact, shapeEqHOL] at hsv
          obtain ⟨w1, rfl⟩ := hw v1 hshapes.1
          obtain ⟨w2, rfl⟩ := hw v2 hshapes.2.1
          obtain ⟨w3, rfl⟩ := hw v3 hshapes.2.2
          exact ⟨w1, w2, w3, rfl, rfl, rfl⟩

private theorem eval_seq_htab_set_ev_slot_unhit_g10 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (off : Nat) (keyVar : MlS) (v_ret : ValueHOL 64)
    (hoff : off < 280)
    (hcode : s.code = originalRuntimeCode)
    (hInv : EvmInv s)
    (ht0 : ∀ S, EvmInvAt s S → memW s (globN s "ev" + off) ∈ S)
    (hret : (evaluateHOLFiniteState s
      (.seq
        (.call (some (none, none)) (ofString "htab_set")
          [.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 off)]),
           .var .local keyVar, .const (BitVec.ofNat 64 1)])
        (.return (.const (BitVec.ofNat 64 0))))).1 = some (.returned v_ret)) :
    let post := (evaluateHOLFiniteState s
      (.seq
        (.call (some (none, none)) (ofString "htab_set")
          [.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 off)]),
           .var .local keyVar, .const (BitVec.ofNat 64 1)])
        (.return (.const (BitVec.ofNat 64 0))))).2
    ∀ ec ∈ evmChain s, R16Shards.IvlUnhit s post (ec.1, 280) ∧ R16Shards.IvlUnhit s post (ec.2, 104) := by
  dsimp only
  obtain ⟨hAs, S, hW, hrest⟩ := hInv
  have hInvAt : EvmInvAt s S := ⟨hW, hrest⟩
  rcases hrun_c : evaluateHOLFiniteState s
      (.seq
        (.call (some (none, none)) (ofString "htab_set")
          [.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 off)]),
           .var .local keyVar, .const (BitVec.ofNat 64 1)])
        (.return (.const (BitVec.ofNat 64 0)))) with ⟨res_c, post_c⟩
  have hret' : res_c = some (.returned v_ret) := by
    have := hret; rw [hrun_c] at this; exact this
  subst hret'
  dsimp only
  rw [evaluateHOLFiniteState_seq_line780] at hrun_c
  rcases hc_set : evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "htab_set")
        [.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 off)]),
         .var .local keyVar, .const (BitVec.ofNat 64 1)]) with ⟨r_set, s2⟩
  rw [hc_set] at hrun_c
  cases r_set with
  | some rs =>
    dsimp only at hrun_c
    exfalso
    have hrs_ret : rs = .returned v_ret := Option.some.inj (Prod.mk.inj hrun_c).1
    rw [evaluateHOLFiniteState_call] at hc_set
    split at hc_set
    · have h1 := Option.some.inj (Prod.mk.inj hc_set).1; rw [hrs_ret] at h1; cases h1
    · split at hc_set
      · have h1 := Option.some.inj (Prod.mk.inj hc_set).1; rw [hrs_ret] at h1; cases h1
      · split at hc_set
        · have h1 := Option.some.inj (Prod.mk.inj hc_set).1; rw [hrs_ret] at h1; cases h1
        · split at hc_set
          · have h1 := Option.some.inj (Prod.mk.inj hc_set).1; rw [hrs_ret] at h1; cases h1
          · have h1 := Option.some.inj (Prod.mk.inj hc_set).1; rw [hrs_ret] at h1; cases h1
          · have h1 := Option.some.inj (Prod.mk.inj hc_set).1; rw [hrs_ret] at h1; cases h1
          · split at hc_set
            · simp at hc_set
            · have h1 := Option.some.inj (Prod.mk.inj hc_set).1; rw [hrs_ret] at h1; cases h1
          · have h1 := Option.some.inj (Prod.mk.inj hc_set).1; rw [hrs_ret] at h1; cases h1
          · rename_i other _ _ heq_other _ _
            have h1 := Option.some.inj (Prod.mk.inj hc_set).1
            rw [hrs_ret] at h1; subst h1; exact heq_other v_ret rfl
  | none =>
    dsimp only at hrun_c
    rw [evaluateHOLFiniteState_return] at hrun_c
    have hev0_s2 : @evalHOLExact 64 F _ s2.toExact
        (fun a => Classical.propDecidable (s2.memaddrs a)) (.const (BitVec.ofNat 64 0)) =
        some (.val (.word 0)) := rfl
    have hsz0_s2 : sizeOfShapeWithContextHOL s2.structs
        (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) ≤ 32 := by
      simp [shapeOfHOLExact]
    rw [hev0_s2] at hrun_c; dsimp only at hrun_c; rw [if_pos hsz0_s2] at hrun_c
    injection hrun_c with _ hpost_c
    obtain ⟨tw, kw, vw, htw_ev, hkw_ev, hvw_ev⟩ :=
      three_one_word_call_args_g10 s (ofString "htab_set")
        (.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 off)]))
        (.var .local keyVar) (.const (BitVec.ofNat 64 1))
        _ _ (ofString "t") (ofString "key") (ofString "value")
        (by rw [hcode]; exact SoloHtabSet.lookup_htab_set)
        (by rw [hc_set]; simp)
    obtain ⟨hev_pos, _, hb_ev⟩ := evmInv_head_ev_bounds_g10 ⟨hAs, S, hInvAt⟩
    obtain ⟨evw, hevw_lk, hevw_nat⟩ := global_word_of_pos s "ev" hev_pos
    have htw_nat : tw.toNat = memW s (globN s "ev" + off) := by
      have had_eq : @evalHOLExact 64 F _ s.toExact
          (fun a => Classical.propDecidable (s.memaddrs a))
          (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 off)]) =
          some (.val (.word (BitVec.ofNat 64 (globN s "ev" + off)))) := by
        simp only [evalHOLExact, evalListHOLExact, hevw_lk, wordOpHOL, wordOp, valueIsWord, valueWord,
          List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr]
        have hz_add : BitVec.ofNat 64 off + (0 : BitVec 64) = BitVec.ofNat 64 off := BitVec.add_zero _
        rw [hz_add]
        congr 3
        apply BitVec.eq_of_toNat_eq
        have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := by norm_num
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, hevw_nat, h264,
          Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      unfold evalHOLExact at htw_ev
      rw [had_eq] at htw_ev; dsimp only at htw_ev
      unfold memLoadHOLExact at htw_ev
      split at htw_ev
      · split at htw_ev
        · injection htw_ev with htw_m
          unfold memW
          cases hm_cell : s.memory (BitVec.ofNat 64 (globN s "ev" + off)) with
          | word cw =>
            change ValueHOL.val (s.memory (BitVec.ofNat 64 (globN s "ev" + off))) = .val (.word tw) at htw_m
            rw [hm_cell] at htw_m
            injection htw_m with htw_m; injection htw_m with htw_m; subst htw_m; rfl
        · cases htw_ev
      · cases htw_ev
    rw [evaluateHOLFiniteState_call] at hc_set
    have hargs_set : evalListHOLFinite s
        (h := fun a => Classical.propDecidable (s.memaddrs a))
        [.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 off)]),
         .var .local keyVar, .const (BitVec.ofNat 64 1)] =
        some [.val (.word tw), .val (.word kw), .val (.word vw)] := by
      simp [evalListHOLFinite, evalListHOLExact, htw_ev, hkw_ev, hvw_ev]
    have hlook_set := pan_three_word_lookup s.code.lookup (ofString "htab_set")
      (ofString "t") (ofString "key") (ofString "value")
      (sourceFnBody Guest.Software.guestFn_htab_set) tw kw vw
      (by decide) (by decide) (by decide)
      (by rw [hcode]; exact SoloHtabSet.lookup_htab_set)
    rw [hargs_set] at hc_set; dsimp only at hc_set
    rw [hlook_set] at hc_set; dsimp only at hc_set
    by_cases hclk_s : s.clock = 0
    · rw [if_pos hclk_s] at hc_set; simp at hc_set
    · rw [if_neg hclk_s] at hc_set
      let cmap_s : HolFiniteMapExact MlS (ValueHOL 64) :=
        ((HolFiniteMapExact.empty.update (ofString "t", ValueHOL.val (.word tw))).update
          (ofString "key", ValueHOL.val (.word kw))).update (ofString "value", ValueHOL.val (.word vw))
      let entry_s := callEntryStateHOLFinite s cmap_s
      rcases hb_set : evaluateHOLFiniteState entry_s (sourceFnBody Guest.Software.guestFn_htab_set) with
        ⟨r_bs, cpost_s⟩
      have hb_set' : evaluateHOLFiniteState (callEntryStateHOLFinite s cmap_s)
          (sourceFnBody Guest.Software.guestFn_htab_set) = (r_bs, cpost_s) := hb_set
      rw [hb_set'] at hc_set
      have hr_bs_ret : ∃ rv_bs, r_bs = some (.returned rv_bs) ∧ s2 = { cpost_s with locals := s.locals } := by
        cases r_bs with
        | none => simp at hc_set
        | some rbi =>
          cases rbi with
          | returned rv_bs =>
            dsimp only at hc_set
            split at hc_set
            · exact ⟨rv_bs, rfl, (Prod.mk.inj hc_set).2.symm⟩
            · simp at hc_set
          | _ => simp at hc_set
      obtain ⟨rv_bs, rfl, hs2_eq⟩ := hr_bs_ret
      have ht0_S : memW s (globN s "ev" + off) ∈ S := ht0 S hInvAt
      have hcal_t : entry_s.locals.lookup (ofString "t") = some (.val (.word tw)) := by
        have h1 : ofString "value" ≠ ofString "t" := by decide
        have h2 : ofString "key" ≠ ofString "t" := by decide
        simp [entry_s, cmap_s, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, h1, h2, Ne.symm h1, Ne.symm h2]
      have hloc_ts : locN entry_s "t" = memW s (globN s "ev" + off) := by
        simp [locN, hcal_t, htw_nat]
      have hArg_s : HtabArgWF entry_s := by
        refine ⟨⟨guestInv_congr (s := s) rfl rfl rfl rfl hAs.1, hAs.2⟩, ?_, ?_⟩
        · rw [hloc_ts]
          exact (R16Shards.StateRestoreEpilogue.htabWF_lc s entry_s.locals s.globals entry_s.clock _).mpr
            (hInvAt.1.1.2.1 _ ht0_S).1
        · rw [hloc_ts]
          intro i hi
          exact ((hInvAt.1.1.2.1 _ ht0_S).2 i hi).1
      have hhl_entry : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "htab_set")
          [.val (.word tw), .val (.word kw), .val (.word vw)] =
          some (sourceFnBody Guest.Software.guestFn_htab_set, entry_s.locals, .one) := by
        rw [← hcode]; exact hlook_set
      obtain ⟨params_sp, body_sp, rs_sp, hlk_spec, hfn_spec⟩ := SoloHtabSet.htab_set_spec_proof
      have hbody_eq : ([(ofString "t", ShapeHOL.one), (ofString "key", ShapeHOL.one), (ofString "value", ShapeHOL.one)],
          sourceFnBody Guest.Software.guestFn_htab_set, ShapeHOL.one) = (params_sp, body_sp, rs_sp) :=
        Option.some.inj (SoloHtabSet.lookup_htab_set.symm.trans hlk_spec)
      rcases Prod.mk.inj hbody_eq with ⟨_, hbr⟩
      rcases Prod.mk.inj hbr with ⟨hb_eq, hrs_eq⟩
      subst hb_eq hrs_eq
      have hexit_s := hfn_spec entry_s hcode hArg_s ⟨_, hhl_entry⟩
        (by rw [hb_set]; simp) rv_bs (by rw [hb_set])
      have hcpost_eq : (evaluateHOLFiniteState entry_s (sourceFnBody Guest.Software.guestFn_htab_set)).2 = cpost_s := by
        rw [hb_set]
      rw [hcpost_eq] at hexit_s
      unfold HtabExit at hexit_s; dsimp only at hexit_s
      rw [hloc_ts] at hexit_s
      obtain ⟨hAp_s, _, _, _, hhp_s, _, hfr_s, _⟩ := hexit_s
      obtain ⟨⟨hT, _, _, _⟩, _, _, _, hFW_all, _, _, _, hFO_disj, _⟩ := hInvAt
      have hpost_mem : post_c.memory = cpost_s.memory := by
        rw [← hpost_c, hs2_eq]; rfl
      have hfr_sp : FrameOutside s post_c
          (htabFootprint s (memW s (globN s "ev" + off)))
          (globN s "heap_ptr", globN cpost_s "heap_ptr" - globN s "heap_ptr") := by
        intro a h1 h2
        rw [hpost_mem]
        exact hfr_s a h1 h2
      have hf_al1 : (globN s "heap_ptr") % 8 = 0 := hAs.2.2.2.2.2.2.1
      have hf_al2 : (globN cpost_s "heap_ptr" - globN s "heap_ptr") % 8 = 0 := by
        have := hAs.2.2.2.2.2.2.1; have := hAp_s.2.2.2.2.2.2.1; omega
      have ht0_al : ∀ j ∈ htabFootprint s (memW s (globN s "ev" + off)),
          j.1 % 8 = 0 ∧ j.2 % 8 = 0 := fun j hj => by
        have hw := ((hT.2.1 _ ht0_S).1.1 j hj).2; exact ⟨hw.1, hw.2.1⟩
      intro ec hec
      have hFW := hFW_all ec hec
      have h1 := hFW.1 (ec.1, 280) (by simp)
      have h2 := hFW.1 (ec.2, 104) (by simp)
      exact ⟨R16Shards.ivlUnhit_of_frameOutside ⟨h1.2.1, h1.2.2.1⟩ hfr_sp ht0_al ⟨hf_al1, hf_al2⟩
               (fun j hj => (hFO_disj ec hec (ec.1, 280) (by simp [frameObjects])).1 _ ht0_S j hj)
               (R16Shards.disj_fresh_of_allocated hAs.2 hAp_s.2 hhp_s (Or.inr h1.1)),
             R16Shards.ivlUnhit_of_frameOutside ⟨h2.2.1, h2.2.2.1⟩ hfr_sp ht0_al ⟨hf_al1, hf_al2⟩
               (fun j hj => (hFO_disj ec hec (ec.2, 104) (by simp [frameObjects])).1 _ ht0_S j hj)
               (R16Shards.disj_fresh_of_allocated hAs.2 hAp_s.2 hhp_s (Or.inr h2.1))⟩

theorem epsA_warm_address :
    EvmPreservingSpecA (fun _ => True)
      (fun s _ post => GlobalsKept ["heap_ptr"] s post ∧ evmR post = evmR s)
      (ofString "warm_address") := by
  obtain ⟨params, body, retShape, hlk, hspec⟩ := eps_warm_address
  have hlk_eq := lookup_warm_address.symm.trans hlk
  injection hlk_eq with hprod
  rcases Prod.mk.inj hprod with ⟨rfl, hprod2⟩
  rcases Prod.mk.inj hprod2 with ⟨hbody_eq, rfl⟩
  subst hbody_eq
  refine ⟨_, _, _, lookup_warm_address, ?_⟩
  intro F s hcode hInv hHMWF hP hlookup hnt
  have hs := hspec s hcode hInv hP hlookup hnt
  have hnc := evaluate_noCatchableRaise warmAccessNcrCallees warmAccessNcrCallees_good
    (sourceFnBody Guest.Software.guestFn_warm_address) (by decide) s hcode
  dsimp only at hs ⊢
  refine ⟨?_, fun ⟨ev, hev⟩ => False.elim (hnc (ofString "EvmErr") ev (by decide) hev)⟩
  intro v hv
  rcases hrun : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_warm_address) with ⟨r_wa, post⟩
  rw [hrun] at hs hv; dsimp only at hs hv ⊢
  obtain ⟨hInv_p, hch_p, hR_le, hg_p, hR_eq⟩ := hs.1 v hv
  have hb : sourceFnBody Guest.Software.guestFn_warm_address =
      .seq
        (.call (some (none, none)) (ofString "htab_set")
          [.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 168)]),
           .var .local (ofString "addr"), .const (BitVec.ofNat 64 1)])
        (.return (.const (BitVec.ofNat 64 0))) := rfl
  have hrun_b : evaluateHOLFiniteState s
      (.seq
        (.call (some (none, none)) (ofString "htab_set")
          [.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 168)]),
           .var .local (ofString "addr"), .const (BitVec.ofNat 64 1)])
        (.return (.const (BitVec.ofNat 64 0)))) = (r_wa, post) := by rwa [← hb]
  have hu : ∀ ec ∈ evmChain s, R16Shards.IvlUnhit s post (ec.1, 280) ∧
      R16Shards.IvlUnhit s post (ec.2, 104) := by
    have hu0 := eval_seq_htab_set_ev_slot_unhit_g10 s 168 (ofString "addr") v (by omega) hcode hInv
      (fun _ hIA => by
        have hhead : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by simp [evmChain, evmChainFrom]
        exact (hIA.2.2.2.2.1 _ hhead).2.2.2.2.2.2.2.2.1)
      (by rw [hrun_b]; exact hv)
    dsimp only at hu0; rwa [hrun_b] at hu0
  have hev_eq : globN post "ev" = globN s "ev" :=
    OpHandlers.globN_eq_of_lookup_eq (hg_p (ofString "ev") (by decide)).symm
  have hfmp_eq : globN post "frame_mem_ptr" = globN s "frame_mem_ptr" :=
    OpHandlers.globN_eq_of_lookup_eq (hg_p (ofString "frame_mem_ptr") (by decide)).symm
  exact ⟨⟨hInv_p, headMemChainWF_of_unhit_g10 hInv hHMWF hch_p hu hev_eq hfmp_eq⟩, hch_p, hR_le, hg_p, hR_eq⟩

theorem epsA_warm_after_charge :
    EvmPreservingSpecA (fun _ => True)
      (fun s _ post => GlobalsKept ["heap_ptr"] s post ∧ evmR post = evmR s)
      (ofString "warm_after_charge") := by
  obtain ⟨params, body, retShape, hlk, hspec⟩ := eps_warm_after_charge
  have hlk_eq := lookup_warm_after_charge.symm.trans hlk
  injection hlk_eq with hprod
  rcases Prod.mk.inj hprod with ⟨rfl, hprod2⟩
  rcases Prod.mk.inj hprod2 with ⟨hbody_eq, rfl⟩
  subst hbody_eq
  refine ⟨_, _, _, lookup_warm_after_charge, ?_⟩
  intro F s hcode hInv hHMWF hP hlookup hnt
  have hs := hspec s hcode hInv hP hlookup hnt
  have hnc := evaluate_noCatchableRaise warmAccessNcrCallees warmAccessNcrCallees_good
    (sourceFnBody Guest.Software.guestFn_warm_after_charge) (by decide) s hcode
  dsimp only at hs ⊢
  refine ⟨?_, fun ⟨ev, hev⟩ => False.elim (hnc (ofString "EvmErr") ev (by decide) hev)⟩
  intro v hv
  rcases hrun : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_warm_after_charge) with ⟨res, post⟩
  rw [hrun] at hs hv hnt; dsimp only at hs hv hnt ⊢
  obtain ⟨hInv_p, hch_p, hR_le, hg_p, hR_eq⟩ := hs.1 v hv
  subst hv
  have hb : sourceFnBody Guest.Software.guestFn_warm_after_charge =
      .seq
        (.ite (.cmp .equal (.var .local (ofString "c")) (.const (BitVec.ofNat 64 3000)))
          (.call (some (none, none)) (ofString "warm_address") [.var .local (ofString "addr")])
          .skip)
        (.return (.const (BitVec.ofNat 64 0))) := rfl
  have hHMWF_p : Group10.HeadMemChainWF post := by
    rw [hb, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hrun
    rcases hcond : @evalHOLExact 64 F _ s.toExact
        (fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .equal (.var .local (ofString "c")) (.const (BitVec.ofNat 64 3000))) with _ | cv
    · rw [hcond] at hrun; simp at hrun
    · rcases cv with ⟨⟨cw⟩⟩ | _ | _
      · rw [hcond] at hrun; dsimp only at hrun
        by_cases hcw0 : cw = 0
        · subst hcw0; simp only [↓reduceIte, evaluateHOLFiniteState_skip] at hrun
          rw [evaluateHOLFiniteState_return] at hrun
          have hev0 : @evalHOLExact 64 F _ s.toExact
              (fun a => Classical.propDecidable (s.memaddrs a)) (.const (BitVec.ofNat 64 0)) =
              some (.val (.word 0)) := rfl
          have hsz0 : sizeOfShapeWithContextHOL s.structs
              (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) ≤ 32 := by
            simp [shapeOfHOLExact]
          rw [hev0] at hrun; dsimp only at hrun; rw [if_pos hsz0] at hrun
          injection hrun with _ hp_eq
          rw [← hp_eq]
          exact Group10.headMemChainWF_locals s _ s.clock hHMWF
        · simp only [hcw0, ↓reduceIte] at hrun
          rcases hc_wa : evaluateHOLFiniteState s
              (.call (some (none, none)) (ofString "warm_address") [.var .local (ofString "addr")]) with ⟨r_wa, s1⟩
          rw [hc_wa] at hrun; dsimp only at hrun
          cases r_wa with
          | none =>
            rw [evaluateHOLFiniteState_call] at hc_wa
            rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
                [.var .local (ofString "addr")] with _ | vals
            · rw [hargs] at hc_wa; simp at hc_wa
            · rw [hargs] at hc_wa; dsimp only at hc_wa
              rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "warm_address") vals with _ | ⟨b_wa, cal_wa, rs_wa⟩
              · rw [hl] at hc_wa; simp at hc_wa
              · rw [hl] at hc_wa; dsimp only at hc_wa
                by_cases hz : s.clock = 0
                · rw [if_pos hz] at hc_wa; simp at hc_wa
                · rw [if_neg hz] at hc_wa
                  obtain ⟨params_wa, body_wa, ret_wa, hlook_wa, hspec_wa⟩ := epsA_warm_address
                  have hbody_eq := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "warm_address")
                    params_wa body_wa b_wa ret_wa rs_wa vals cal_wa (by rw [hcode]; exact hlook_wa) hl
                  subst b_wa
                  have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "warm_address") vals =
                      some (body_wa, cal_wa, rs_wa) := by rwa [← hcode]
                  have hInv_ce : EvmInv (callEntryStateHOLFinite s cal_wa) :=
                    localsFree_evmInv s cal_wa (s.clock - 1) hInv
                  have hHMWF_ce : Group10.HeadMemChainWF (callEntryStateHOLFinite s cal_wa) :=
                    Group10.headMemChainWF_locals s cal_wa (s.clock - 1) hHMWF
                  rcases hrun_wa : evaluateHOLFiniteState (callEntryStateHOLFinite s cal_wa) body_wa with ⟨res_wa, cpost⟩
                  rw [hrun_wa] at hc_wa
                  cases res_wa with
                  | none => simp at hc_wa
                  | some rw0 =>
                    cases rw0 with
                    | returned v_wa =>
                      dsimp only at hc_wa
                      split at hc_wa
                      · injection hc_wa with _ hs1
                        rw [evaluateHOLFiniteState_return] at hrun
                        have hev0 : @evalHOLExact 64 F _ s1.toExact
                            (fun a => Classical.propDecidable (s1.memaddrs a)) (.const (BitVec.ofNat 64 0)) =
                            some (.val (.word 0)) := rfl
                        have hsz0 : sizeOfShapeWithContextHOL s1.structs
                            (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) ≤ 32 := by
                          simp [shapeOfHOLExact]
                        rw [hev0] at hrun; dsimp only at hrun; rw [if_pos hsz0] at hrun
                        injection hrun with _ hp_eq
                        have hs_wa := (hspec_wa (callEntryStateHOLFinite s cal_wa) hcode hInv_ce hHMWF_ce trivial ⟨vals, ?_⟩
                          (by rw [hrun_wa]; simp)).1 v_wa (by rw [hrun_wa])
                        · dsimp only at hs_wa; rw [hrun_wa] at hs_wa
                          have hp_cp : post = { cpost with locals := post.locals, clock := cpost.clock } := by
                            rw [← hp_eq, ← hs1]; rfl
                          rw [hp_cp]
                          exact Group10.headMemChainWF_locals cpost post.locals cpost.clock hs_wa.1.2
                        · have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
                            s.code.lookup (ofString "warm_address") vals body_wa cal_wa rs_wa hl
                          rw [hcode] at hx; simp only [Flapjack.lookupCodeHOLExact, hlook_wa] at hx
                          split at hx
                          · have hrs : rs_wa = ret_wa := (congrArg (fun x => x.2.2) (Option.some.inj hx)).symm
                            rwa [← hrs]
                          · cases hx
                      · simp at hc_wa
                    | _ => simp at hc_wa
          | some r0 =>
            cases r0 with
            | returned _ =>
              rw [evaluateHOLFiniteState_call] at hc_wa
              rcases hargs2 : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
                  [.var .local (ofString "addr")] with _ | vals
              · rw [hargs2] at hc_wa; simp at hc_wa
              · rw [hargs2] at hc_wa; dsimp only at hc_wa
                rcases hl2 : lookupCodeHOLFinite s.code.lookup (ofString "warm_address") vals with _ | ⟨b_wa, cal_wa, rs_wa⟩
                · rw [hl2] at hc_wa; simp at hc_wa
                · rw [hl2] at hc_wa; dsimp only at hc_wa
                  split at hc_wa
                  · simp at hc_wa
                  · rcases hrun2 : evaluateHOLFiniteState (callEntryStateHOLFinite s cal_wa) b_wa with ⟨rw1, _⟩
                    rw [hrun2] at hc_wa
                    cases rw1 with
                    | none => simp at hc_wa
                    | some rw2 =>
                      cases rw2 with
                      | returned _ => dsimp only at hc_wa; split at hc_wa <;> simp at hc_wa
                      | _ => simp at hc_wa
            | _ => simp at hrun
      · rw [hcond] at hrun; simp at hrun
      · rw [hcond] at hrun; simp at hrun
  exact ⟨⟨hInv_p, hHMWF_p⟩, hch_p, hR_le, hg_p, hR_eq⟩

private theorem headMemChainWF_of_head_stack_push_g10 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {freshIvl : Ivl}
    (hInv : EvmInv s) (hHMWF : Group10.HeadMemChainWF s)
    (hApost : ArenaReady post)
    (heff : ScratchByteEff s post [freshIvl, (globN s "ev", 280), (memW s (globN s "ev" + 8), 32 * memW s (globN s "ev" + 232))])
    (hfresh : freshIvl = (0, 0) ∨
      (freshIvl.1 % 8 = 0 ∧ freshIvl.2 % 8 = 0 ∧
        Inside freshIvl (globN post "scratch_ptr") (globN s "scratch_ptr")))
    (he0_other : ∀ off, off + 8 ≤ 280 → off % 8 = 0 → off ≠ 8 → off ≠ 16 → off ≠ 232 →
      memW post (globN s "ev" + off) = memW s (globN s "ev" + off))
    (hchain : evmChain post = evmChain s) :
    Group10.HeadMemChainWF post := by
  obtain ⟨hAs, S, _, _, _, _, hFW_all, _, _, hFO_pw, _⟩ := hInv
  set e0 := globN s "ev"
  set c0 := globN s "cur_cont"
  set oldStk : Ivl := (memW s (e0 + 8), 32 * memW s (e0 + 232))
  have hch_cons : ∃ tl, evmChain s = (e0, c0) :: tl := ⟨_, rfl⟩
  obtain ⟨chTail, hch_eq⟩ := hch_cons
  have hhead_mem : (e0, c0) ∈ evmChain s := by rw [hch_eq]; exact List.mem_cons_self
  have hhead_FW := hFW_all _ hhead_mem
  have he0_8 : e0 % 8 = 0 := (hhead_FW.1 (e0, 280) (by simp)).2.1
  have holdStk_8 : oldStk.1 % 8 = 0 := (hhead_FW.1 oldStk (by simp [oldStk])).2.1
  have hRl_list : ∀ x ∈ ([freshIvl, (e0, 280), oldStk] : List Ivl), x.1 % 8 = 0 := by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rcases hfresh with rfl | ⟨h8, _⟩
      · rfl
      · exact h8
    · exact he0_8
    · exact holdStk_8
  have hglob_eq : ∀ g, ofString g ≠ ofString "scratch_ptr" → globN post g = globN s g :=
    fun g hg => OpHandlers.globN_eq_of_lookup_eq (heff.glob_other g hg)
  have hmemW_disj : ∀ {base sz k : Nat}, base + sz ≤ 2 ^ 64 → base % 8 = 0 → k % 8 = 0 → k + 8 ≤ sz →
      (∀ x ∈ ([freshIvl, (e0, 280), oldStk] : List Ivl), Disj x (base, sz)) →
      memW post (base + k) = memW s (base + k) := by
    intro base sz k hbnd hb8 hk8 hk hdj
    unfold memW
    have ha : base + k < 2 ^ 64 := by omega
    have hbk8 : (base + k) % 8 = 0 := by omega
    have hbit : (BitVec.ofNat 64 (base + k)).toNat = base + k := Nat.mod_eq_of_lt ha
    rw [heff.cell_frame (BitVec.ofNat 64 (base + k))]
    intro x hx; rw [hbit]
    exact not_cellHits_of_disj_aligned (i := (base, sz)) hbk8 (hRl_list x hx)
      (Nat.le_add_right base k) (Nat.add_le_add_left hk base) (R11Shards.Disj.symm (hdj x hx))
  have hpw_head_tail :
      (frameObjects s (e0, c0)).Pairwise Disj ∧
      (∀ o1 ∈ frameObjects s (e0, c0),
        ∀ ec ∈ chTail, ∀ o2 ∈ frameObjects s ec, Disj o1 o2) := by
    have hpw := hFO_pw
    rw [hch_eq, List.map_cons, List.flatten_cons, List.pairwise_append] at hpw
    refine ⟨hpw.1, fun o1 ho1 ec hec o2 ho2 => hpw.2.2 o1 ho1 o2 ?_⟩
    exact List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨ec, hec, rfl⟩, ho2⟩
  have hfresh_disj_ec : ∀ ec ∈ evmChain s, Disj freshIvl (ec.1, 280) ∧ Disj freshIvl (ec.2, 104) := by
    intro ec hec
    rcases hfresh with rfl | ⟨_, _, hfin1, _⟩
    · exact ⟨Or.inl rfl, Or.inl rfl⟩
    · have hFW := hFW_all ec hec
      have h3 := hApost.2.2.2.2.1
      rw [hglob_eq "frame_mem_ptr" (by decide)] at h3
      obtain ⟨hin1, _⟩ := (hFW.1 (ec.1, 280) (by simp)).1
      obtain ⟨hin2, _⟩ := (hFW.1 (ec.2, 104) (by simp)).1
      exact ⟨Or.inr (Or.inr (Or.inl (by dsimp only at hin1 ⊢; omega))),
             Or.inr (Or.inr (Or.inl (by dsimp only at hin2 ⊢; omega)))⟩
  have hhead_pw := hpw_head_tail.1
  unfold frameObjects at hhead_pw
  have hp0 := List.pairwise_cons.1 hhead_pw
  have hp1 := List.pairwise_cons.1 hp0.2
  refine Group10.headMemChainWF_of_agree hHMWF hchain ?_
    (hglob_eq "ev" (by decide)) (hglob_eq "frame_mem_ptr" (by decide))
  intro ec hec
  have hFW := hFW_all ec hec
  obtain ⟨hb_e, hb_c, _, _⟩ := frameWF_bounds hAs.2 hFW
  have he8 : ec.1 % 8 = 0 := (hFW.1 (ec.1, 280) (by simp)).2.1
  have hc8 : ec.2 % 8 = 0 := (hFW.1 (ec.2, 104) (by simp)).2.1
  have hdj_f := hfresh_disj_ec ec hec
  have he_eq : ∀ k, k + 8 ≤ 280 → k % 8 = 0 → k ≠ 8 → k ≠ 16 → k ≠ 232 →
      memW post (ec.1 + k) = memW s (ec.1 + k) := by
    intro k hk hk8 hk8' hk16 hk232
    rw [hch_eq, List.mem_cons] at hec
    rcases hec with rfl | htail
    · exact he0_other k hk hk8 hk8' hk16 hk232
    · apply hmemW_disj hb_e he8 hk8 hk
      intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact hdj_f.1
      · exact hpw_head_tail.2 _ (by simp [frameObjects]) ec htail _ (by simp [frameObjects])
      · exact hpw_head_tail.2 _ (by simp [frameObjects, oldStk]) ec htail _ (by simp [frameObjects])
  have hc56 : memW post (ec.2 + 56) = memW s (ec.2 + 56) := by
    apply hmemW_disj hb_c hc8 (by omega) (by omega)
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rw [hch_eq, List.mem_cons] at hec
    rcases hec with rfl | htail
    · rcases hx with rfl | rfl | rfl
      · exact hdj_f.2
      · exact hp0.1 _ (by simp)
      · exact R11Shards.Disj.symm (hp1.1 _ (by simp [oldStk]))
    · rcases hx with rfl | rfl | rfl
      · exact hdj_f.2
      · exact hpw_head_tail.2 _ (by simp [frameObjects]) ec htail _ (by simp [frameObjects])
      · exact hpw_head_tail.2 _ (by simp [frameObjects, oldStk]) ec htail _ (by simp [frameObjects])
  exact ⟨he_eq 24 (by omega) (by omega) (by omega) (by omega) (by omega),
         he_eq 32 (by omega) (by omega) (by omega) (by omega) (by omega),
         he_eq 40 (by omega) (by omega) (by omega) (by omega) (by omega),
         hc56⟩

private theorem raise3_unchanged_hmwf_g10 {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (hHMWF : Group10.HeadMemChainWF s)
    (L_wrap : HolFiniteMapExact MlS (ValueHOL 64) → HolFiniteMapExact MlS (ValueHOL 64))
    (ht_eq : t = { s with locals := t.locals, clock := t.clock }) :
    let out := evaluateHOLFiniteState t (.raise (ofString "EvmErr") (.const 3#64))
    (∀ v, out.1 = some (.returned v) →
      Group10.HeadMemChainWF { out.2 with locals := L_wrap out.2.locals }) ∧
    (IsEvmErr out.1 →
      Group10.HeadMemChainWF { out.2 with locals := L_wrap out.2.locals }) := by
  dsimp only
  rw [evaluateHOLFiniteState_raise]; dsimp only [evalHOLExact]
  cases ht_esh : t.eshapes.lookup (ofString "EvmErr") with
  | none =>
    dsimp only
    constructor
    · intro _ h; cases h
    · rintro ⟨_, h⟩; cases h
  | some sh =>
    dsimp only
    by_cases hcond : shapeOfHOLExact (.val (.word 3#64)) = sh ∧
        sizeOfShapeWithContextHOL t.structs (shapeOfHOLExact (.val (.word 3#64))) ≤ 32
    · rw [if_pos hcond]; dsimp only
      let post := { t.emptyLocalsHOLFinite with locals := L_wrap t.emptyLocalsHOLFinite.locals }
      have hp_eq : post = { s with locals := post.locals, clock := t.clock } := by
        dsimp only [post, emptyLocalsHOLFinite]; conv_lhs => rw [ht_eq]
      have hHMWF_p : Group10.HeadMemChainWF post := by
        have h := Group10.headMemChainWF_locals s post.locals t.clock hHMWF
        rwa [← hp_eq] at h
      constructor
      · intro _ h; cases h
      · intro _; exact hHMWF_p
    · rw [if_neg hcond]; dsimp only
      constructor
      · intro _ h; cases h
      · rintro ⟨_, h⟩; cases h

theorem epsA_stack_push :
    EvmPreservingSpecA (fun _ => True)
      (fun s _ post => ∀ g : String, ofString g ≠ ofString "scratch_ptr" → globN post g = globN s g)
      (ofString "stack_push") := by
  obtain ⟨params_sp, body_sp, retShape_sp, hlk_sp, hspec_sp⟩ := eps_stack_push
  have hlk_eq := lookup_stack_push.symm.trans hlk_sp
  injection hlk_eq with hprod
  rcases Prod.mk.inj hprod with ⟨rfl, hprod2⟩
  rcases Prod.mk.inj hprod2 with ⟨hbody_eq, rfl⟩
  subst hbody_eq
  refine ⟨_, _, _, lookup_stack_push, ?_⟩
  intro F s hcode hInv hHMWF _ ⟨vals, hlk_entry⟩ hnt
  have hs_base := hspec_sp s hcode hInv trivial ⟨vals, hlk_entry⟩ hnt
  clear hspec_sp hlk_sp
  dsimp only at hs_base ⊢
  suffices hhm :
      let r := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_stack_push)).1
      let post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_stack_push)).2
      (∀ v, r = some (.returned v) → Group10.HeadMemChainWF post) ∧
      (IsEvmErr r → Group10.HeadMemChainWF post) by
    dsimp only at hhm
    refine ⟨fun v hv => ?_, fun herr => ?_⟩
    · obtain ⟨hInv_p, hch_p, hR_p, hg_p⟩ := hs_base.1 v hv
      exact ⟨⟨hInv_p, hhm.1 v hv⟩, hch_p, hR_p, hg_p⟩
    · obtain ⟨hInv_p, hch_p, hR_p⟩ := hs_base.2 herr
      exact ⟨⟨hInv_p, hhm.2 herr⟩, hch_p, hR_p⟩
  have hv_struct : ∃ w0 w1 w2 w3 : BitVec 64,
      s.locals.lookup (ofString "v") =
        some (.rStruct [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3)]) := by
    have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
      originalRuntimeCode.lookup (ofString "stack_push") vals
      (sourceFnBody Guest.Software.guestFn_stack_push) s.locals .one hlk_entry
    simp only [Flapjack.lookupCodeHOLExact, lookup_stack_push] at hx
    rcases vals with _ | ⟨v0, _ | _⟩
    · simp at hx
    · split at hx
      · rename_i hcond
        have heq := Option.some.inj hx
        rcases Prod.mk.inj heq with ⟨_, hrest⟩
        rcases Prod.mk.inj hrest with ⟨hloc, _⟩
        have hsh : shapeEqHOL (.comb [.one, .one, .one, .one]) (shapeOfHOLExact v0) = true := by
          simpa [List.map] using hcond
        rw [shapeEqHOL_eq_true] at hsh
        have hfn : s.locals.lookup (ofString "v") = some v0 := by
          have := congrFun hloc.symm (ofString "v")
          simpa [FUPDATE_LIST, FUPDATE] using this
        rcases v0 with _ | fs | _
        · simp [shapeOfHOLExact] at hsh
        · simp only [shapeOfHOLExact, ShapeHOL.comb.injEq] at hsh
          rcases fs with _ | ⟨f0, _ | ⟨f1, _ | ⟨f2, _ | ⟨f3, _ | _⟩⟩⟩⟩
          · simp at hsh
          · simp at hsh
          · simp at hsh
          · simp at hsh
          · simp only [List.map, List.cons.injEq] at hsh
            obtain ⟨h0, h1, h2, h3, _⟩ := hsh
            rcases f0 with ⟨⟨w0⟩⟩ | _ | _ <;> simp [shapeOfHOLExact] at h0
            rcases f1 with ⟨⟨w1⟩⟩ | _ | _ <;> simp [shapeOfHOLExact] at h1
            rcases f2 with ⟨⟨w2⟩⟩ | _ | _ <;> simp [shapeOfHOLExact] at h2
            rcases f3 with ⟨⟨w3⟩⟩ | _ | _ <;> simp [shapeOfHOLExact] at h3
            exact ⟨w0, w1, w2, w3, hfn⟩
          · simp at hsh
        · simp [shapeOfHOLExact] at hsh
      · cases hx
    · simp at hx
  obtain ⟨vw0, vw1, vw2, vw3, hv_loc⟩ := hv_struct
  have hhead_mem : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by simp [evmChain, evmChainFrom]
  have hFW0 := hInv.2.choose_spec.2.2.2.2.1 _ hhead_mem
  have hb_ev := (frameWF_bounds hInv.1.2 hFW0).1
  dsimp only at hb_ev
  have hev_pos : 0 < globN s "ev" := by
    obtain ⟨hin1, _⟩ := (hFW0.1 (globN s "ev", 280) (by simp)).1
    have h1 := hInv.1.2.2.2.1; have h2 := hInv.1.2.2.2.2.1
    rw [R11Shards.scratchStart_val] at h1; dsimp only at hin1; omega
  obtain ⟨evw, hevw, hevw_nat⟩ := global_word_of_pos s "ev" hev_pos
  obtain ⟨hp_w, fp_w, sp_g_w, hhp_lk, hhp_nat, hfp_lk, hfp_nat, hsp_g_lk, hsp_g_nat⟩ :=
    Wave8Contracts.M26.arenaOK_globals s hInv.1.2
  have herr_triv : ∀ {P1 P2 : Prop},
      (∀ v, (some PanSemResultExact.error : Option (PanSemResultExact 64)) = some (.returned v) → P1) ∧
      (IsEvmErr (some PanSemResultExact.error) → P2) := by
    intro _ _; constructor
    · intro _ h; cases h
    · rintro ⟨_, h⟩; cases h
  let growBranch : ProgHOL 64 :=
    .seq
      (.ite (.cmp .notLower (.var .local (ofString "cap")) (.const 1024#64))
        (.raise (ofString "EvmErr") (.const 3#64))
        .skip)
      (.dec (ofString "ncap") .one (.panop .mul [.var .local (ofString "cap"), .const 2#64])
        (.seq
          (.ite (.cmp .lower (.const 1024#64) (.var .local (ofString "ncap")))
            (.assign .local (ofString "ncap") (.const 1024#64))
            .skip)
          (.decCall (ofString "ns") .one (ofString "scratch_alloc")
            [.panop .mul [.var .local (ofString "ncap"), .const 32#64]]
            (.seq
              (.call (some (none, none)) (ofString "memcpy")
                [.var .local (ofString "ns"),
                 .load .one (.op .add [.var .global (ofString "ev"), .const 8#64]),
                 .panop .mul [.var .local (ofString "sp"), .const 32#64]])
              (.seq
                (.store (.op .add [.var .global (ofString "ev"), .const 8#64]) (.var .local (ofString "ns")))
                (.store (.op .add [.var .global (ofString "ev"), .const 232#64]) (.var .local (ofString "ncap"))))))))
  let tailProg : ProgHOL 64 :=
    .seq
      (.ite (.cmp .equal (.var .local (ofString "sp")) (.const 1024#64))
        (.raise (ofString "EvmErr") (.const 3#64))
        .skip)
      (.seq
        (.store
          (.op .add
            [.load .one (.op .add [.var .global (ofString "ev"), .const 8#64]),
             .panop .mul [.var .local (ofString "sp"), .const 32#64]])
          (.var .local (ofString "v")))
        (.seq
          (.store (.op .add [.var .global (ofString "ev"), .const 16#64])
            (.op .add [.var .local (ofString "sp"), .const 1#64]))
          (.return (.const 0#64))))
  have hbody : sourceFnBody Guest.Software.guestFn_stack_push =
      .dec (ofString "sp") .one (.load .one (.op .add [.var .global (ofString "ev"), .const 16#64]))
        (.dec (ofString "cap") .one (.load .one (.op .add [.var .global (ofString "ev"), .const 232#64]))
          (.seq
            (.ite (.cmp .notLower (.var .local (ofString "sp")) (.var .local (ofString "cap")))
              growBranch
              .skip)
            tailProg)) := rfl
  dsimp only
  rw [hbody] at hnt ⊢
  rw [evaluateHOLFiniteState_dec_total] at hnt ⊢; dsimp only at hnt ⊢
  rcases hload_sp : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.load .one (.op .add [.var .global (ofString "ev"), .const 16#64])) with _ | vsp
  · exact herr_triv
  · simp only [hload_sp] at hnt ⊢
    obtain ⟨spw, rfl, hspw_eq⟩ := evalAt_loadG_word s "ev" 16#64 vsp hload_sp
    have h16_n : (16#64 : BitVec 64).toNat = 16 := rfl
    rw [h16_n] at hspw_eq
    have hsh_sp : shapeEqHOL .one (shapeOfHOLExact (.val (.word spw))) = true := by
      simp [shapeEqHOL, shapeOfHOLExact]
    rw [if_pos hsh_sp] at hnt ⊢; dsimp only at hnt ⊢
    set s1 := setVarHOLFinite (ofString "sp") (.val (.word spw)) s with hs1
    rw [evaluateHOLFiniteState_dec_total] at hnt ⊢; dsimp only at hnt ⊢
    rcases hload_cap : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
        (.load .one (.op .add [.var .global (ofString "ev"), .const 232#64])) with _ | vcap
    · exact herr_triv
    · simp only [hload_cap] at hnt ⊢
      obtain ⟨capw, rfl, hcapw_eq⟩ := evalAt_loadG_word s1 "ev" 232#64 vcap hload_cap
      have h232_n : (232#64 : BitVec 64).toNat = 232 := rfl
      have hs1_gm : memW s1 (globN s1 "ev" + 232) = memW s (globN s "ev" + 232) := rfl
      rw [h232_n, hs1_gm] at hcapw_eq
      have hsh_cap : shapeEqHOL .one (shapeOfHOLExact (.val (.word capw))) = true := by
        simp [shapeEqHOL, shapeOfHOLExact]
      rw [if_pos hsh_cap] at hnt ⊢; dsimp only at hnt ⊢
      set s2 := setVarHOLFinite (ofString "cap") (.val (.word capw)) s1 with hs2
      have hs2_sp : s2.locals.lookup (ofString "sp") = some (.val (.word spw)) := by
        simp [hs2, hs1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "cap" ≠ ofString "sp" by decide]
      have hs2_cap : s2.locals.lookup (ofString "cap") = some (.val (.word capw)) := by
        simp [hs2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hs2_v : s2.locals.lookup (ofString "v") =
          some (.rStruct [.val (.word vw0), .val (.word vw1), .val (.word vw2), .val (.word vw3)]) := by
        simp [hs2, hs1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hv_loc,
          show ofString "cap" ≠ ofString "v" by decide, show ofString "sp" ≠ ofString "v" by decide]
      have hcap_ge1 : 1 ≤ capw.toNat := by rw [hcapw_eq]; exact hFW0.2.2.2.1
      have hsp_le_cap : spw.toNat ≤ capw.toNat := by rw [hspw_eq, hcapw_eq]; exact hFW0.2.2.2.2.1
      have hcap_le1024 : capw.toNat ≤ 1024 := by rw [hcapw_eq]; exact hFW0.2.2.2.2.2.1
      have run_tail : ∀ (m : PanSemStateFiniteExact 64 F) (freshIvl : Ivl),
          ArenaReady m →
          globN m "scratch_ptr" ≤ globN s "scratch_ptr" →
          (∀ g : String, ofString g ≠ ofString "scratch_ptr" → m.globals.lookup (ofString g) = s.globals.lookup (ofString g)) →
          ScratchByteEff s m [freshIvl, (globN s "ev", 280), (memW s (globN s "ev" + 8), 32 * memW s (globN s "ev" + 232))] →
          (freshIvl = (0, 0) ∨
            (freshIvl.1 % 8 = 0 ∧ freshIvl.2 % 8 = 0 ∧
              Inside freshIvl (globN m "scratch_ptr") (globN s "scratch_ptr"))) →
          (∀ off, off + 8 ≤ 280 → off % 8 = 0 → off ≠ 8 → off ≠ 16 → off ≠ 232 →
            memW m (globN s "ev" + off) = memW s (globN s "ev" + off)) →
          ((freshIvl.2 = 0 ∧ memW m (globN s "ev" + 8) = memW s (globN s "ev" + 8) ∧
              memW m (globN s "ev" + 232) = memW s (globN s "ev" + 232)) ∨
            (freshIvl.2 ≠ 0 ∧ (memW m (globN s "ev" + 8), 32 * memW m (globN s "ev" + 232)) = freshIvl)) →
          spw.toNat < memW m (globN s "ev" + 232) →
          memW m (globN s "ev" + 232) ≤ 1024 →
          memW m (globN s "ev" + 16) = spw.toNat →
          m.locals.lookup (ofString "sp") = some (.val (.word spw)) →
          m.locals.lookup (ofString "v") =
            some (.rStruct [.val (.word vw0), .val (.word vw1), .val (.word vw2), .val (.word vw3)]) →
          let out := evaluateHOLFiniteState m tailProg
          let post := { out.2 with
            locals := (out.2.locals.resVarEq (ofString "cap", s1.locals.lookup (ofString "cap"))).resVarEq
              (ofString "sp", s.locals.lookup (ofString "sp")) }
          (∀ v, out.1 = some (.returned v) → Group10.HeadMemChainWF post) ∧
          (IsEvmErr out.1 → Group10.HeadMemChainWF post) := by
        intro m freshIvl hAm hsc_m hm_glob_other heff_m hfresh_m he0_m hnew_m hsp_lt_mcap hmcap_le _hm_sp16 hm_sp hm_v
        dsimp only [tailProg]
        have hm_ev : m.globals.lookup (ofString "ev") = some (.val (.word evw)) := by
          rw [hm_glob_other "ev" (by decide)]; exact hevw
        have hsp_ne1024 : spw ≠ 1024#64 := by
          intro heq; subst heq
          have : (1024#64 : BitVec 64).toNat = 1024 := rfl
          omega
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
        have hcmp_sp : @evalHOLExact 64 F _ m.toExact (fun a => Classical.propDecidable (m.memaddrs a))
            (.cmp .equal (.var .local (ofString "sp")) (.const 1024#64)) = some (.val (.word 0#64)) := by
          simp [evalHOLExact, hm_sp, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hsp_ne1024]
        rw [hcmp_sp]; simp only [↓reduceIte, evaluateHOLFiniteState_skip]
        have h0_eq : (0#64 : BitVec 64) = 0 := rfl
        simp only [h0_eq, ↓reduceIte, evaluateHOLFiniteState_skip]
        rw [evaluateHOLFiniteState_seq_line780]
        let dstStkExp : ExpHOL 64 :=
          .op .add
            [.load .one (.op .add [.var .global (ofString "ev"), .const 8#64]),
             .panop .mul [.var .local (ofString "sp"), .const 32#64]]
        rcases hst_v : evaluateHOLFiniteState m (.store dstStkExp (.var .local (ofString "v"))) with ⟨rv_st, m1⟩
        simp only [hst_v]
        cases rv_st with
        | some res_v =>
          have herr := store_some_eq_error' hst_v; subst herr; dsimp only; exact herr_triv
        | none =>
          dsimp only
          have hstk_ptr_bound : memW m (globN s "ev" + 8) + 32 * memW m (globN s "ev" + 232) ≤ 2 ^ 64 := by
            rcases hnew_m with ⟨_, h8_eq, h232_eq⟩ | ⟨hnz, hstk_eq⟩
            · rw [h8_eq, h232_eq]
              obtain ⟨_, hin2⟩ := (hFW0.1 (memW s (globN s "ev" + 8), 32 * memW s (globN s "ev" + 232)) (by simp)).1
              rw [R11Shards.scratchEnd_val] at hin2; dsimp only at hin2; omega
            · rcases hfresh_m with rfl | ⟨_, _, _, hfin2⟩
              · exact absurd rfl hnz
              · have h4 := hInv.1.2.2.2.2.2.1; rw [R11Shards.scratchEnd_val] at h4
                rw [← hstk_eq] at hfin2; dsimp only at hfin2; omega
          have hd_v_stk := ScratchByteEff.of_store_struct4
            (Rl := [freshIvl, (memW s (globN s "ev" + 8), 32 * memW s (globN s "ev" + 232))])
            hAm.1.memaddrs hst_v
            (fun v hv => by
              change m.locals.lookup (ofString "v") = some v at hv
              rw [hm_v] at hv; injection hv with hv'; exact ⟨vw0, vw1, vw2, vw3, hv'.symm⟩)
            (fun addr hdst => by
              dsimp only [dstStkExp] at hdst
              have hmem_load8 : ∃ stkw : BitVec 64, m.memory (evw + 8#64) = .word stkw ∧
                  addr = stkw + spw * 32#64 := by
                rcases hm8 : m.memory (evw + 8#64) with ⟨stkw⟩
                refine ⟨stkw, rfl, ?_⟩
                simp [evalHOLExact, evalListHOLExact, hm_ev, hm_sp,
                  wordOpHOL, wordOp, panOpHOL, valueIsWord, valueWord, memLoadHOLExact, hm8] at hdst
                by_cases hdm8 : m.memaddrs (evw + 8#64)
                · simp [hdm8, valueIsWord, valueWord] at hdst; exact hdst.symm
                · simp [hdm8] at hdst
              obtain ⟨stkw, hm8, haddr_eq⟩ := hmem_load8
              have hev8_eq : evw + 8#64 = BitVec.ofNat 64 (globN s "ev" + 8) := by
                apply BitVec.eq_of_toNat_eq
                have : (8#64 : BitVec 64).toNat = 8 := rfl
                rw [BitVec.toNat_add, hevw_nat, this, BitVec.toNat_ofNat]
              have hstkw_nat : stkw.toNat = memW m (globN s "ev" + 8) := by
                unfold memW; rw [← hev8_eq, hm8]
              have hsp32_nat : (spw * 32#64).toNat = 32 * spw.toNat := by
                have : (32#64 : BitVec 64).toNat = 32 := rfl
                rw [BitVec.toNat_mul, this, Nat.mod_eq_of_lt (by omega)]; omega
              have haddr_nat : addr.toNat = memW m (globN s "ev" + 8) + 32 * spw.toNat := by
                rw [haddr_eq, BitVec.toNat_add, hstkw_nat, hsp32_nat, Nat.mod_eq_of_lt (by omega)]
              refine ⟨by omega, ?_⟩
              rcases hnew_m with ⟨_, h8_eq, h232_eq⟩ | ⟨_, hstk_eq⟩
              · exact ⟨(memW s (globN s "ev" + 8), 32 * memW s (globN s "ev" + 232)),
                  by simp, by dsimp only; omega, by dsimp only; omega⟩
              · refine ⟨freshIvl, by simp, ?_, ?_⟩
                · rw [← hstk_eq]; dsimp only; omega
                · rw [← hstk_eq]; dsimp only; omega)
          obtain ⟨heff_st_v_stk, hm1_loc, hm1_glob⟩ := hd_v_stk
          have heff_st_v : ScratchByteEff m m1
              [freshIvl, (globN s "ev", 280), (memW s (globN s "ev" + 8), 32 * memW s (globN s "ev" + 232))] :=
            heff_st_v_stk.mono (fun x hx => by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
              rcases hx with hx1 | hx2
              · rw [hx1]; exact ⟨_, List.mem_cons_self, le_refl _, le_refl _⟩
              · rw [hx2]; exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), le_refl _, le_refl _⟩)
          have hm1_e0_eq : ∀ off, off + 8 ≤ 280 → off % 8 = 0 →
              memW m1 (globN s "ev" + off) = memW m (globN s "ev" + off) := by
            intro off hoff hoff8
            unfold memW
            rw [heff_st_v_stk.cell_frame (BitVec.ofNat 64 (globN s "ev" + off))]
            intro x hx
            have htn : (BitVec.ofNat 64 (globN s "ev" + off)).toNat = globN s "ev" + off :=
              Nat.mod_eq_of_lt (by omega)
            rw [htn]
            have he0_8 : (globN s "ev") % 8 = 0 := (hFW0.1 (globN s "ev", 280) (by simp)).2.1
            have ha8 : (globN s "ev" + off) % 8 = 0 := by omega
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
            rcases hx with rfl | rfl
            · rcases hfresh_m with rfl | ⟨hf8, _, _, hfin2⟩
              · intro ⟨_, hc2⟩; dsimp only at hc2; omega
              · obtain ⟨he0_scr, _⟩ := (hFW0.1 (globN s "ev", 280) (by simp)).1
                exact not_cellHits_of_disj_aligned (i := (globN s "ev", 280)) ha8 hf8
                  (Nat.le_add_right _ off) (Nat.add_le_add_left hoff _)
                  (Or.inr (Or.inr (Or.inr (by dsimp only at he0_scr ⊢; omega))))
            · have hold_8 : (memW s (globN s "ev" + 8)) % 8 = 0 :=
                (hFW0.1 (memW s (globN s "ev" + 8), 32 * memW s (globN s "ev" + 232)) (by simp)).2.1
              have hpw_fo := hInv.2.choose_spec.2.2.2.2.2.2.2.1
              have hch_s : ∃ tl, evmChain s = (globN s "ev", globN s "cur_cont") :: tl := ⟨_, rfl⟩
              obtain ⟨tl_s, hch_s_eq⟩ := hch_s
              rw [hch_s_eq, List.map_cons, List.flatten_cons, List.pairwise_append] at hpw_fo
              have hd_stk : Disj (globN s "ev", 280) (memW s (globN s "ev" + 8), 32 * memW s (globN s "ev" + 232)) := by
                have hp0 := hpw_fo.1; unfold frameObjects at hp0
                exact (List.pairwise_cons.1 hp0).1 _ (by simp)
              exact not_cellHits_of_disj_aligned (i := (globN s "ev", 280)) ha8 hold_8
                (Nat.le_add_right _ off) (Nat.add_le_add_left hoff _) hd_stk
          rw [evaluateHOLFiniteState_seq_line780]
          rcases hst_sp : evaluateHOLFiniteState m1
              (.store (.op .add [.var .global (ofString "ev"), .const 16#64])
                (.op .add [.var .local (ofString "sp"), .const 1#64])) with ⟨rsp_st, m2⟩
          simp only [hst_sp]
          cases rsp_st with
          | some res_sp =>
            have herr := store_some_eq_error' hst_sp; subst herr; dsimp only; exact herr_triv
          | none =>
            dsimp only
            have hm1_ev : m1.globals.lookup (ofString "ev") = some (.val (.word evw)) := by
              rw [hm1_glob]; exact hm_ev
            have hm1_sp : m1.locals.lookup (ofString "sp") = some (.val (.word spw)) := by
              rw [hm1_loc]; exact hm_sp
            obtain ⟨w_sp1, hw_sp1_ev, hm2_eq⟩ := R14Shards.OpHandlersA.store_global_off_word (t := m1) (post := m2)
              (gname := "ev") (gbase := globN s "ev") (off := 16) hm1_ev hevw_nat (by omega)
              (fun v hv => by
                simp [evalHOLExact, evalListHOLExact, hm1_sp, wordOpHOL, wordOp, valueIsWord, valueWord] at hv
                exact ⟨_, hv.symm⟩) hst_sp
            have hw_sp1_val : w_sp1 = spw + 1#64 := by
              simp [evalHOLExact, evalListHOLExact, hm1_sp, wordOpHOL, wordOp, valueIsWord, valueWord] at hw_sp1_ev
              exact hw_sp1_ev.symm
            subst hw_sp1_val
            have heff_st_sp := (ByteRegionEffect.of_store_word (Rl := [(globN s "ev", 280)])
              (heff_st_v.memaddrs.trans hAm.1.memaddrs) hst_sp
              (fun v hv => by
                simp [evalHOLExact, evalListHOLExact, hm1_sp, wordOpHOL, wordOp, valueIsWord, valueWord] at hv
                exact ⟨_, hv.symm⟩)
              (fun addr hdst _ => by
                simp [evalHOLExact, evalListHOLExact, hm1_ev, wordOpHOL, wordOp, valueIsWord, valueWord] at hdst
                have h16_eq : (evw + 16#64).toNat = globN s "ev" + 16 := by
                  have : (16#64 : BitVec 64).toNat = 16 := rfl
                  rw [BitVec.toNat_add, hevw_nat, this, Nat.mod_eq_of_lt (by omega)]
                exact ⟨(globN s "ev", 280), by simp, by rw [← hdst, h16_eq]; dsimp only; omega,
                  by rw [← hdst, h16_eq]; dsimp only; omega⟩)).1
            have heff_st_sp_sbe : ScratchByteEff m1 m2
                [freshIvl, (globN s "ev", 280), (memW s (globN s "ev" + 8), 32 * memW s (globN s "ev" + 232))] :=
              (ScratchByteEff.of_bre heff_st_sp).mono (fun x hx => by
                simp at hx; subst hx; exact ⟨(globN s "ev", 280), by simp, le_refl _, le_refl _⟩)
            rw [evaluateHOLFiniteState_return]
            have hc0_m2 : @evalHOLExact 64 F _ m2.toExact (fun a => Classical.propDecidable (m2.memaddrs a)) (.const (0 : BitVec 64)) =
                some (.val (.word 0)) := rfl
            have hc0_m2' : @evalHOLExact 64 F _ m2.toExact (fun a => Classical.propDecidable (m2.memaddrs a)) (.const 0#64) =
                some (.val (.word 0#64)) := rfl
            simp only [hc0_m2, hc0_m2']
            have hsz0 : sizeOfShapeWithContextHOL m2.structs
                (shapeOfHOLExact (.val (.word (0 : BitVec 64)))) ≤ 32 := by
              simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
            have hsz0' : sizeOfShapeWithContextHOL m2.structs
                (shapeOfHOLExact (.val (.word 0#64))) ≤ 32 := by
              simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
            simp only [hsz0, hsz0', ↓reduceIte]
            let post := { m2.emptyLocalsHOLFinite with
              locals := (m2.emptyLocalsHOLFinite.locals.resVarEq (ofString "cap", s1.locals.lookup (ofString "cap"))).resVarEq
                (ofString "sp", s.locals.lookup (ofString "sp")) }
            have heff_total : ScratchByteEff s post
                [freshIvl, (globN s "ev", 280), (memW s (globN s "ev" + 8), 32 * memW s (globN s "ev" + 232))] :=
              ((heff_m.trans heff_st_v).trans heff_st_sp_sbe).with_locals_clock post.locals m2.clock
            have hpost_glob_m : post.globals = m.globals := by
              simp [post, emptyLocalsHOLFinite, hm2_eq, hm1_glob]
            have hApost : ArenaReady post :=
              ⟨guestInv_congr (s := m) (by simp [post, emptyLocalsHOLFinite, hm2_eq, heff_st_v.code])
                (by simp [post, emptyLocalsHOLFinite, hm2_eq, heff_st_v.memaddrs])
                (by simp [post, emptyLocalsHOLFinite, hm2_eq, heff_st_v.shMemaddrs])
                (by simp [post, emptyLocalsHOLFinite, hm2_eq, heff_st_v.baseAddr]) hAm.1,
               arenaOK_congr hpost_glob_m hAm.2⟩
            have hsc_post : globN post "scratch_ptr" ≤ globN s "scratch_ptr" := by
              unfold globN; rw [hpost_glob_m]; exact hsc_m
            have hfresh_post : freshIvl = (0, 0) ∨
                (freshIvl.1 % 8 = 0 ∧ freshIvl.2 % 8 = 0 ∧
                  Inside freshIvl (globN post "scratch_ptr") (globN s "scratch_ptr")) := by
              unfold globN; rw [hpost_glob_m]; exact hfresh_m
            have hm2_memW_ne16 : ∀ off, off + 8 ≤ 280 → off % 8 = 0 → off ≠ 16 →
                memW post (globN s "ev" + off) = memW m (globN s "ev" + off) := by
              intro off hoff hoff8 hne16
              change memW m2 (globN s "ev" + off) = memW m (globN s "ev" + off)
              rw [hm2_eq, R14Shards.OpHandlersA.memW_updW_ne m1 (globN s "ev" + 16) (globN s "ev" + off) _ (by omega) (by omega) (by omega),
                  hm1_e0_eq off hoff hoff8]
            have hm2_memW_16 : memW post (globN s "ev" + 16) = spw.toNat + 1 := by
              change memW m2 (globN s "ev" + 16) = spw.toNat + 1
              rw [hm2_eq, R14Shards.OpHandlersA.memW_updW_same m1 (globN s "ev" + 16) (spw + 1#64)]
              have : (1#64 : BitVec 64).toNat = 1 := rfl
              rw [BitVec.toNat_add, this, Nat.mod_eq_of_lt (by omega)]
            have he0_post : ∀ off, off + 8 ≤ 280 → off % 8 = 0 → off ≠ 8 → off ≠ 16 → off ≠ 232 →
                memW post (globN s "ev" + off) = memW s (globN s "ev" + off) := by
              intro off hoff hoff8 h8 h16 h232
              rw [hm2_memW_ne16 off hoff hoff8 h16, he0_m off hoff hoff8 h8 h16 h232]
            have hnew_post :
                (freshIvl.2 = 0 ∧ memW post (globN s "ev" + 8) = memW s (globN s "ev" + 8) ∧
                  memW post (globN s "ev" + 232) = memW s (globN s "ev" + 232)) ∨
                (freshIvl.2 ≠ 0 ∧ (memW post (globN s "ev" + 8), 32 * memW post (globN s "ev" + 232)) = freshIvl) := by
              rw [hm2_memW_ne16 8 (by omega) (by omega) (by omega),
                  hm2_memW_ne16 232 (by omega) (by omega) (by omega)]
              exact hnew_m
            have hcap_post :
                1 ≤ memW post (globN s "ev" + 232) ∧
                memW post (globN s "ev" + 16) ≤ memW post (globN s "ev" + 232) ∧
                memW post (globN s "ev" + 232) ≤ 1024 := by
              rw [hm2_memW_ne16 232 (by omega) (by omega) (by omega), hm2_memW_16]
              exact ⟨by omega, by omega, hmcap_le⟩
            obtain ⟨_, hch_p, _⟩ := evmInv_of_head_stack_push hInv hApost hsc_post
              heff_total hfresh_post he0_post hnew_post hcap_post
            have hHMWF_p := headMemChainWF_of_head_stack_push_g10 hInv hHMWF hApost
              heff_total hfresh_post he0_post hch_p
            constructor
            · intro _ _; exact hHMWF_p
            · rintro ⟨_, h⟩; cases h
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt ⊢
      have hcmp_grow : @evalHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a))
          (.cmp .notLower (.var .local (ofString "sp")) (.var .local (ofString "cap"))) =
          some (.val (.word (if capw ≤ spw then 1 else 0))) := by
        simp only [evalHOLExact, hs2_sp, hs2_cap, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, BitVec.le_def]
        by_cases hle : capw.toNat ≤ spw.toNat
        · have hnot : ¬ spw.toNat < capw.toNat := by omega
          simp [hle, hnot]
        · have hlt : spw.toNat < capw.toNat := by omega
          simp [hle, hlt]
      rw [hcmp_grow] at hnt ⊢; dsimp only at hnt ⊢
      by_cases hgrow : capw ≤ spw
      · have hsp_eq_cap : spw.toNat = capw.toNat := by
          rw [BitVec.le_def] at hgrow; omega
        have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
        simp only [hgrow, ↓reduceIte, h10] at hnt ⊢
        dsimp only [growBranch] at hnt ⊢
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt ⊢
        have hcmp_cap1024 : @evalHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a))
            (.cmp .notLower (.var .local (ofString "cap")) (.const 1024#64)) =
            some (.val (.word (if 1024 ≤ capw.toNat then 1 else 0))) := by
          have h1024 : (1024#64 : BitVec 64).toNat = 1024 := rfl
          simp only [evalHOLExact, hs2_cap, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, h1024]
          by_cases hle : 1024 ≤ capw.toNat
          · have hnot : ¬ capw.toNat < 1024 := by omega
            simp [hle, hnot]
          · have hlt : capw.toNat < 1024 := by omega
            simp [hle, hlt]
        rw [hcmp_cap1024] at hnt ⊢; dsimp only at hnt ⊢
        by_cases hcap1024 : 1024 ≤ capw.toNat
        · simp only [hcap1024, ↓reduceIte, h10] at hnt ⊢
          rcases hr3 : evaluateHOLFiniteState s2 (.raise (ofString "EvmErr") (.const 3#64)) with ⟨rr3, sr3⟩
          have hr3_nn : rr3 ≠ none := by
            intro h; subst h; exact raise_ne_none s2 _ (.const 3#64) (by rw [hr3])
          simp only [hr3]
          cases rr3 with
          | none => exact absurd rfl hr3_nn
          | some _ =>
            dsimp only
            have hru := raise3_unchanged_hmwf_g10 (s := s) (t := s2) hHMWF
              (fun L => (L.resVarEq (ofString "cap", s1.locals.lookup (ofString "cap"))).resVarEq
                (ofString "sp", s.locals.lookup (ofString "sp")))
              (by cases s; rfl)
            dsimp only at hru; rw [hr3] at hru; exact hru
        · have hcap_lt1024 : capw.toNat < 1024 := by omega
          simp only [hcap1024, ↓reduceIte, evaluateHOLFiniteState_skip] at hnt ⊢
          rw [evaluateHOLFiniteState_dec_total] at hnt ⊢; dsimp only at hnt ⊢
          have hmul2 : @evalHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a))
              (.panop .mul [.var .local (ofString "cap"), .const 2#64]) =
              some (.val (.word (capw * 2#64))) := by
            simp [evalHOLExact, evalListHOLExact, hs2_cap, panOpHOL, valueIsWord, valueWord]
          rw [hmul2] at hnt ⊢; dsimp only at hnt ⊢
          have hsh_ncap : shapeEqHOL .one (shapeOfHOLExact (.val (.word (capw * 2#64)))) = true := by
            simp [shapeEqHOL, shapeOfHOLExact]
          rw [if_pos hsh_ncap] at hnt ⊢; dsimp only at hnt ⊢
          set s3 := setVarHOLFinite (ofString "ncap") (.val (.word (capw * 2#64))) s2 with hs3
          have hncap0_nat : (capw * 2#64).toNat = 2 * capw.toNat := by
            have : (2#64 : BitVec 64).toNat = 2 := rfl
            rw [BitVec.toNat_mul, this, Nat.mod_eq_of_lt (by omega)]; omega
          have hite_ncap : ∃ (s4 : PanSemStateFiniteExact 64 F) (ncapw : BitVec 64),
              evaluateHOLFiniteState s3
                (.ite (.cmp .lower (.const 1024#64) (.var .local (ofString "ncap")))
                  (.assign .local (ofString "ncap") (.const 1024#64))
                  .skip) = (none, s4) ∧
              s4 = { s with locals := s4.locals, clock := s.clock } ∧
              s4.locals.lookup (ofString "ncap") = some (.val (.word ncapw)) ∧
              s4.locals.lookup (ofString "sp") = some (.val (.word spw)) ∧
              s4.locals.lookup (ofString "v") =
                some (.rStruct [.val (.word vw0), .val (.word vw1), .val (.word vw2), .val (.word vw3)]) ∧
              capw.toNat < ncapw.toNat ∧ ncapw.toNat ≤ 1024 := by
            have hs3_ncap : s3.locals.lookup (ofString "ncap") = some (.val (.word (capw * 2#64))) := by
              simp [hs3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
            rw [evaluateHOLFiniteState_ite]
            have hcmp_nc : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
                (.cmp .lower (.const 1024#64) (.var .local (ofString "ncap"))) =
                some (.val (.word (if 1024#64 < capw * 2#64 then 1 else 0))) := by
              simp [evalHOLExact, hs3_ncap, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
            rw [hcmp_nc]; dsimp only
            by_cases hgt1024 : 1024#64 < capw * 2#64
            · simp only [hgt1024, ↓reduceIte, h10, evaluateHOLFiniteState_assign]
              have hev1024 : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
                  (.const 1024#64) = some (.val (.word 1024#64)) := rfl
              have hval1024 : s3.isValidValueHOLFinite .local (ofString "ncap") (.val (.word 1024#64)) = true := by
                simp [isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLExact, hs3_ncap, shapeOfHOLExact, shapeEqHOL]
              rw [hev1024]; dsimp only; rw [if_pos hval1024]
              let s4 := setKvarHOLFinite .local (ofString "ncap") (.val (.word 1024#64)) s3
              have h1024_n : (1024#64 : BitVec 64).toNat = 1024 := rfl
              refine ⟨s4, 1024#64, rfl, by cases s; rfl, ?_, ?_, ?_, by omega, by omega⟩
              · simp [s4, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
              · simp [s4, hs3, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs2_sp,
                  show ofString "ncap" ≠ ofString "sp" by decide]
              · simp [s4, hs3, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs2_v,
                  show ofString "ncap" ≠ ofString "v" by decide]
            · simp only [hgt1024, ↓reduceIte, evaluateHOLFiniteState_skip]
              have hle1024 : (capw * 2#64).toNat ≤ 1024 := by
                rw [BitVec.lt_def] at hgt1024
                have : (1024#64 : BitVec 64).toNat = 1024 := rfl
                omega
              refine ⟨s3, capw * 2#64, rfl, by cases s; rfl, hs3_ncap, ?_, ?_, by omega, hle1024⟩
              · simp [hs3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs2_sp,
                  show ofString "ncap" ≠ ofString "sp" by decide]
              · simp [hs3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs2_v,
                  show ofString "ncap" ≠ ofString "v" by decide]
          obtain ⟨s4, ncapw, hs4_run, hs4_eq, hs4_ncap, hs4_sp, hs4_v, hncap_gt, hncap_le1024⟩ := hite_ncap
          rw [evaluateHOLFiniteState_seq_line780, hs4_run] at hnt ⊢; dsimp only at hnt ⊢
          rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt ⊢
          have hargs_sa : evalListHOLFinite s4 (h := fun a => Classical.propDecidable (s4.memaddrs a))
              [.panop .mul [.var .local (ofString "ncap"), .const 32#64]] =
              some [.val (.word (ncapw * 32#64))] := by
            simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hs4_ncap, panOpHOL, valueIsWord, valueWord]
          have hs4_code : s4.code = originalRuntimeCode := by rw [hs4_eq]; exact hcode
          have hlk_sa := pan_one_word_lookup s4.code.lookup (ofString "scratch_alloc") (ofString "n")
            (sourceFnBody Guest.Software.guestFn_scratch_alloc) (ncapw * 32#64)
            (by rw [hs4_code]; exact scratch_alloc_lookup_pub)
          rw [hargs_sa] at hnt ⊢; dsimp only at hnt ⊢
          rw [hlk_sa] at hnt ⊢; dsimp only at hnt ⊢
          by_cases hs4_clk0 : s4.clock = 0
          · rw [if_pos hs4_clk0] at hnt; simp at hnt
          · rw [if_neg hs4_clk0] at hnt ⊢
            let saCallee := HolFiniteMapExact.empty.update (ofString "n", ValueHOL.val (.word (ncapw * 32#64)))
            let saEntry := callEntryStateHOLFinite s4 saCallee
            have hsa_code : saEntry.code = originalRuntimeCode := hs4_code
            have hsa_no_evmErr := scratch_alloc_body_no_evmErr saEntry hsa_code
            rcases hsa_run : evaluateHOLFiniteState saEntry
                (sourceFnBody Guest.Software.guestFn_scratch_alloc) with ⟨rsa, saPost⟩
            rw [hsa_run] at hsa_no_evmErr
            have hsa_run_raw : evaluateHOLFiniteState
                (callEntryStateHOLFinite s4 (HolFiniteMapExact.empty.update (ofString "n", ValueHOL.val (.word (ncapw * 32#64)))))
                (sourceFnBody Guest.Software.guestFn_scratch_alloc) = (rsa, saPost) := hsa_run
            simp only [hsa_run_raw] at hnt ⊢
            cases rsa with
            | none => exact herr_triv
            | some rsa0 =>
              cases rsa0 with
              | timeOut => simp at hnt
              | exception eid ev =>
                dsimp only at hnt ⊢
                by_cases heid : eid = ofString "EvmErr"
                · subst heid; exact absurd ⟨ev, rfl⟩ hsa_no_evmErr
                · constructor
                  · intro _ h; cases h
                  · rintro ⟨_, h⟩; injection h with h'; injection h' with h1 _; exact (heid h1).elim
              | «break» => exact herr_triv
              | «continue» => exact herr_triv
              | finalFfi _ =>
                constructor
                · intro _ h; cases h
                · rintro ⟨_, h⟩; cases h
              | error => exact herr_triv
              | returned vsa =>
                have hsa_sp_lk : saEntry.globals.lookup (ofString "scratch_ptr") = some (.val (.word sp_g_w)) := by
                  change s4.globals.lookup _ = _; rw [hs4_eq]; exact hsp_g_lk
                have hsa_fp_lk : saEntry.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word fp_w)) := by
                  change s4.globals.lookup _ = _; rw [hs4_eq]; exact hfp_lk
                have hsa_n_lk : saEntry.locals.lookup (ofString "n") = some (.val (.word (ncapw * 32#64))) := by
                  simp [saEntry, saCallee, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                obtain ⟨rfl, hcmp1_sa, hcmp2_sa, hsaPost_eq_raw⟩ :=
                  Wave8Contracts.M26.scratch_alloc_body_run saEntry sp_g_w fp_w (ncapw * 32#64)
                    hsa_code hsa_sp_lk hsa_fp_lk hsa_n_lk vsa (by rw [hsa_run])
                have hsaPost_eq : saPost = { saEntry with
                    globals := saEntry.globals.update (ofString "scratch_ptr", .val (.word ((sp_g_w - ncapw * 32#64) &&& ((0 : BitVec 64) - 8)))),
                    locals := saPost.locals } := by
                  rw [hsa_run] at hsaPost_eq_raw; exact hsaPost_eq_raw
                dsimp only [saEntry] at hsaPost_eq
                set nsw : BitVec 64 := (sp_g_w - ncapw * 32#64) &&& ((0 : BitVec 64) - 8)
                have hsh_ns : (shapeEqHOL (shapeOfHOLExact (.val (.word nsw) : ValueHOL 64)) .one &&
                    shapeEqHOL (shapeOfHOLExact (.val (.word nsw) : ValueHOL 64)) .one) = true := by
                  simp [shapeEqHOL, shapeOfHOLExact]
                have hsh_ns' : (shapeEqHOL (shapeOfHOLExact (.val (.word nsw) : ValueHOL 64)) .one &&
                    shapeEqHOL .one (shapeOfHOLExact (.val (.word nsw) : ValueHOL 64))) = true := by
                  simp [shapeEqHOL, shapeOfHOLExact]
                dsimp only at hnt ⊢
                simp only [hsh_ns, hsh_ns', ↓reduceIte] at hnt ⊢
                have hn_bytes : (ncapw * 32#64).toNat = 32 * ncapw.toNat := by
                  have : (32#64 : BitVec 64).toNat = 32 := rfl
                  rw [BitVec.toNat_mul, this, Nat.mod_eq_of_lt (by omega)]; omega
                have hsub_pf : (sp_g_w - fp_w).toNat = sp_g_w.toNat - fp_w.toNat := by
                  rw [BitVec.toNat_sub]
                  have hle_fp_sp : globN s "frame_mem_ptr" ≤ globN s "scratch_ptr" := hInv.1.2.2.2.2.1
                  omega
                have hsp_g_al : sp_g_w.toNat % 8 = 0 := by
                  have h8 : globN s "scratch_ptr" % 8 = 0 := hInv.1.2.2.2.2.2.2.2.2.1
                  rw [hsp_g_nat]; exact h8
                have hn_le_sp_g : (ncapw * 32#64).toNat ≤ sp_g_w.toNat := by
                  have := sp_g_w.isLt; have := fp_w.isLt; omega
                have hsub_pn : (sp_g_w - ncapw * 32#64).toNat = sp_g_w.toNat - 32 * ncapw.toNat := by
                  rw [BitVec.toNat_sub, hn_bytes]; omega
                have hnsw_nat : nsw.toNat = sp_g_w.toNat - 32 * ncapw.toNat := by
                  have hand := and_neg8_toNat (sp_g_w - ncapw * 32#64)
                  change nsw.toNat = (sp_g_w - ncapw * 32#64).toNat / 8 * 8 at hand
                  rw [hsub_pn] at hand; omega
                have hnsw_al : nsw.toNat % 8 = 0 := by omega
                have hnsw_ge_fp : globN s "frame_mem_ptr" ≤ nsw.toNat := by
                  rw [← hfp_nat]; exact Nat.le_of_not_lt hcmp2_sa
                have hnsw_end : nsw.toNat + 32 * ncapw.toNat = globN s "scratch_ptr" := by
                  rw [← hsp_g_nat]; omega
                set s5 := setVarHOLFinite (ofString "ns") (.val (.word nsw)) { saPost with locals := s4.locals } with hs5
                have hs5_ns : s5.locals.lookup (ofString "ns") = some (.val (.word nsw)) := by
                  simp [hs5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                have hs5_ncap : s5.locals.lookup (ofString "ncap") = some (.val (.word ncapw)) := by
                  simp [hs5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs4_ncap,
                    show ofString "ns" ≠ ofString "ncap" by decide]
                have hs5_sp : s5.locals.lookup (ofString "sp") = some (.val (.word spw)) := by
                  simp [hs5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs4_sp,
                    show ofString "ns" ≠ ofString "sp" by decide]
                have hs5_v : s5.locals.lookup (ofString "v") =
                    some (.rStruct [.val (.word vw0), .val (.word vw1), .val (.word vw2), .val (.word vw3)]) := by
                  simp [hs5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs4_v,
                    show ofString "ns" ≠ ofString "v" by decide]
                have hs5_mem : s5.memory = s.memory := by
                  change saPost.memory = s.memory; rw [hsaPost_eq]; dsimp only [callEntryStateHOLFinite]; rw [hs4_eq]
                have hs5_glob : s5.globals = s.globals.update (ofString "scratch_ptr", .val (.word nsw)) := by
                  change saPost.globals = _; rw [hsaPost_eq]; dsimp only [callEntryStateHOLFinite]; rw [hs4_eq]
                have hs5_code : s5.code = originalRuntimeCode := by
                  change saPost.code = _; rw [hsaPost_eq]; exact hsa_code
                have hs5_ma : s5.memaddrs = ordinaryDomain := by
                  change saPost.memaddrs = _; rw [hsaPost_eq]; dsimp only [callEntryStateHOLFinite]; rw [hs4_eq]; exact hInv.1.1.memaddrs
                have hs5_ev : s5.globals.lookup (ofString "ev") = some (.val (.word evw)) := by
                  rw [hs5_glob]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hevw,
                    show ofString "scratch_ptr" ≠ ofString "ev" by decide]
                let mcCall : ProgHOL 64 :=
                  .call (some (none, none)) (ofString "memcpy")
                    [.var .local (ofString "ns"),
                     .load .one (.op .add [.var .global (ofString "ev"), .const 8#64]),
                     .panop .mul [.var .local (ofString "sp"), .const 32#64]]
                let st8Prog : ProgHOL 64 :=
                  .store (.op .add [.var .global (ofString "ev"), .const 8#64]) (.var .local (ofString "ns"))
                let st232Prog : ProgHOL 64 :=
                  .store (.op .add [.var .global (ofString "ev"), .const 232#64]) (.var .local (ofString "ncap"))
                rcases hs5_m8 : s5.memory (evw + 8#64) with ⟨oldStkw⟩
                have hs5_dom8 : s5.memaddrs (evw + 8#64) := by
                  rw [hs5_ma, hInv.1.1.memaddrs.symm]
                  have hev8_eq : evw + 8#64 = BitVec.ofNat 64 (globN s "ev" + 8) := by
                    apply BitVec.eq_of_toNat_eq
                    have : (8#64 : BitVec 64).toNat = 8 := rfl
                    rw [BitVec.toNat_add, hevw_nat, this, BitVec.toNat_ofNat]
                  rw [hev8_eq]
                  exact ((hFW0.1 (globN s "ev", 280) (by simp)).2.2.2 1 (by omega)).choose_spec.1
                have hev_mc_src : @evalHOLExact 64 F _ s5.toExact (fun a => Classical.propDecidable (s5.memaddrs a))
                    (.load .one (.op .add [.var .global (ofString "ev"), .const 8#64])) =
                    some (.val (.word oldStkw)) := by
                  simp [evalHOLExact, evalListHOLExact, hs5_ev, wordOpHOL, wordOp, valueIsWord, valueWord,
                    memLoadHOLExact, hs5_dom8, hs5_m8]
                have hev_mc_dst : @evalHOLExact 64 F _ s5.toExact (fun a => Classical.propDecidable (s5.memaddrs a))
                    (.var .local (ofString "ns")) = some (.val (.word nsw)) := hs5_ns
                have hev_mc_n : @evalHOLExact 64 F _ s5.toExact (fun a => Classical.propDecidable (s5.memaddrs a))
                    (.panop .mul [.var .local (ofString "sp"), .const 32#64]) =
                    some (.val (.word (spw * 32#64))) := by
                  simp [evalHOLExact, evalListHOLExact, hs5_sp, panOpHOL, valueIsWord, valueWord]
                have hsp32_nat : (spw * 32#64).toNat = 32 * spw.toNat := by
                  have : (32#64 : BitVec 64).toNat = 32 := rfl
                  rw [BitVec.toNat_mul, this, Nat.mod_eq_of_lt (by omega)]; omega
                let freshIvl : Ivl := (nsw.toNat, 32 * ncapw.toNat)
                have hnt_mc : (evaluateHOLFiniteState s5 mcCall).1 ≠ some .timeOut := by
                  intro hto
                  rcases hmc_to : evaluateHOLFiniteState s5
                      (.call (some (none, none)) (ofString "memcpy")
                        [.var .local (ofString "ns"),
                         .load .one (.op .add [.var .global (ofString "ev"), .const 8#64]),
                         .panop .mul [.var .local (ofString "sp"), .const 32#64]]) with ⟨rmc_to, smc_to⟩
                  have hto' : rmc_to = some .timeOut := by
                    dsimp only [mcCall] at hto; rw [hmc_to] at hto; exact hto
                  subst hto'
                  rw [evaluateHOLFiniteState_seq_line780] at hnt
                  simp [hmc_to] at hnt
                have hmc := M11.eval_call_memcpy_bre s5 _ _ _ nsw oldStkw (spw * 32#64) [freshIvl]
                  hs5_code hs5_ma hev_mc_dst hev_mc_src hev_mc_n
                  (fun _ => ⟨freshIvl, by simp, le_refl _, by dsimp only [freshIvl]; omega⟩) hnt_mc
                dsimp only at hmc
                rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
                rcases hmc_run : evaluateHOLFiniteState s5 mcCall with ⟨rmc, s6⟩
                rw [hmc_run] at hmc
                have hmc_run_raw : evaluateHOLFiniteState s5
                    (.call (some (none, none)) (ofString "memcpy")
                      [.var .local (ofString "ns"),
                       .load .one (.op .add [.var .global (ofString "ev"), .const 8#64]),
                       .panop .mul [.var .local (ofString "sp"), .const 32#64]]) = (rmc, s6) := hmc_run
                simp only [hmc_run_raw] at hnt ⊢
                cases rmc with
                | some rmc0 =>
                  dsimp only at hnt ⊢
                  have hnr := hmc.2 (by simp)
                  refine ⟨fun v hv => absurd (Or.inl ⟨v, hv⟩) hnr, ?_⟩
                  rintro ⟨ev, hv⟩
                  injection hv with hv'; subst hv'
                  exact absurd (Or.inr ⟨ofString "EvmErr", ev, rfl, by decide⟩) hnr
                | none =>
                  dsimp only at hnt ⊢
                  obtain ⟨heff_mc_m11, hs6_loc⟩ := hmc.1 rfl
                  have heff_mc : ScratchByteEff s5 s6 [freshIvl] := ScratchByteEff.of_m11_bre heff_mc_m11
                  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
                  rcases hst8 : evaluateHOLFiniteState s6 st8Prog with ⟨rst8, s7⟩
                  have hst8_raw : evaluateHOLFiniteState s6
                      (.store (.op .add [.var .global (ofString "ev"), .const 8#64]) (.var .local (ofString "ns"))) = (rst8, s7) := hst8
                  simp only [hst8_raw] at hnt ⊢
                  cases rst8 with
                  | some res8 =>
                    have herr := store_some_eq_error' hst8; subst herr; dsimp only; exact herr_triv
                  | none =>
                    dsimp only at hnt ⊢
                    have hs6_ev : s6.globals.lookup (ofString "ev") = some (.val (.word evw)) := by
                      rw [heff_mc_m11.globals]; exact hs5_ev
                    have hs6_ns : s6.locals.lookup (ofString "ns") = some (.val (.word nsw)) := by
                      rw [hs6_loc]; exact hs5_ns
                    obtain ⟨w_ns', hw_ns_ev, hs7_eq⟩ := R14Shards.OpHandlersA.store_global_off_word (t := s6) (post := s7)
                      (gname := "ev") (gbase := globN s "ev") (off := 8) hs6_ev hevw_nat (by omega)
                      (fun v hv => by
                        change s6.locals.lookup (ofString "ns") = some v at hv
                        rw [hs6_ns] at hv; injection hv with hv'; exact ⟨nsw, hv'.symm⟩) hst8
                    have hw_ns_val : nsw = w_ns' := by
                      change s6.locals.lookup (ofString "ns") = some (.val (.word w_ns')) at hw_ns_ev
                      rw [hs6_ns] at hw_ns_ev
                      injection hw_ns_ev with h1; injection h1 with h2; injection h2 with h3
                    subst w_ns'
                    have heff_st8 := (ByteRegionEffect.of_store_word (Rl := [(globN s "ev", 280)])
                      (heff_mc_m11.memaddrs.trans hs5_ma) hst8
                      (fun v hv => by
                        change s6.locals.lookup (ofString "ns") = some v at hv
                        rw [hs6_ns] at hv; injection hv with hv'; exact ⟨nsw, hv'.symm⟩)
                      (fun addr hdst _ => by
                        simp [evalHOLExact, evalListHOLExact, hs6_ev, wordOpHOL, wordOp, valueIsWord, valueWord] at hdst
                        have h8_eq : (evw + 8#64).toNat = globN s "ev" + 8 := by
                          have : (8#64 : BitVec 64).toNat = 8 := rfl
                          rw [BitVec.toNat_add, hevw_nat, this, Nat.mod_eq_of_lt (by omega)]
                        exact ⟨(globN s "ev", 280), by simp, by rw [← hdst, h8_eq]; dsimp only; omega,
                          by rw [← hdst, h8_eq]; dsimp only; omega⟩)).1
                    rcases hst232 : evaluateHOLFiniteState s7 st232Prog with ⟨rst232, s8⟩
                    have hst232_raw : evaluateHOLFiniteState s7
                        (.store (.op .add [.var .global (ofString "ev"), .const 232#64]) (.var .local (ofString "ncap"))) = (rst232, s8) := hst232
                    simp only [hst232_raw] at hnt ⊢
                    cases rst232 with
                    | some res232 =>
                      have herr := store_some_eq_error' hst232; subst herr; dsimp only; exact herr_triv
                    | none =>
                      dsimp only at hnt ⊢
                      have hs7_ev : s7.globals.lookup (ofString "ev") = some (.val (.word evw)) := by
                        rw [hs7_eq]; exact hs6_ev
                      have hs7_ncap : s7.locals.lookup (ofString "ncap") = some (.val (.word ncapw)) := by
                        rw [hs7_eq]; dsimp only; rw [hs6_loc]; exact hs5_ncap
                      obtain ⟨w_ncap', hw_ncap_ev, hs8_eq⟩ := R14Shards.OpHandlersA.store_global_off_word (t := s7) (post := s8)
                        (gname := "ev") (gbase := globN s "ev") (off := 232) hs7_ev hevw_nat (by omega)
                        (fun v hv => by
                          change s7.locals.lookup (ofString "ncap") = some v at hv
                          rw [hs7_ncap] at hv; injection hv with hv'; exact ⟨ncapw, hv'.symm⟩) hst232
                      have hw_ncap_val : ncapw = w_ncap' := by
                        change s7.locals.lookup (ofString "ncap") = some (.val (.word w_ncap')) at hw_ncap_ev
                        rw [hs7_ncap] at hw_ncap_ev
                        injection hw_ncap_ev with h1; injection h1 with h2; injection h2 with h3
                      subst w_ncap'
                      have heff_st232 := (ByteRegionEffect.of_store_word (Rl := [(globN s "ev", 280)])
                        (by rw [hs7_eq]; exact heff_mc_m11.memaddrs.trans hs5_ma) hst232
                        (fun v hv => by
                          change s7.locals.lookup (ofString "ncap") = some v at hv
                          rw [hs7_ncap] at hv; injection hv with hv'; exact ⟨ncapw, hv'.symm⟩)
                        (fun addr hdst _ => by
                          simp [evalHOLExact, evalListHOLExact, hs7_ev, wordOpHOL, wordOp, valueIsWord, valueWord] at hdst
                          have h232_eq : (evw + 232#64).toNat = globN s "ev" + 232 := by
                            have : (232#64 : BitVec 64).toNat = 232 := rfl
                            rw [BitVec.toNat_add, hevw_nat, this, Nat.mod_eq_of_lt (by omega)]
                          exact ⟨(globN s "ev", 280), by simp, by rw [← hdst, h232_eq]; dsimp only; omega,
                            by rw [← hdst, h232_eq]; dsimp only; omega⟩)).1
                      let m : PanSemStateFiniteExact 64 F :=
                        { s8 with
                          locals := (s8.locals.resVarEq (ofString "ns", s4.locals.lookup (ofString "ns"))).resVarEq
                            (ofString "ncap", s2.locals.lookup (ofString "ncap")) }
                      change (let out := evaluateHOLFiniteState m tailProg
                        let post := { out.2 with
                          locals := (out.2.locals.resVarEq (ofString "cap", s1.locals.lookup (ofString "cap"))).resVarEq
                            (ofString "sp", s.locals.lookup (ofString "sp")) }
                        (∀ v, out.1 = some (.returned v) → Group10.HeadMemChainWF post) ∧
                        (IsEvmErr out.1 → Group10.HeadMemChainWF post))
                      have hm_glob : m.globals = s.globals.update (ofString "scratch_ptr", .val (.word nsw)) := by
                        dsimp only [m]; rw [hs8_eq, hs7_eq]; dsimp only; rw [heff_mc_m11.globals, hs5_glob]
                      have hm_sp_glob : globN m "scratch_ptr" = nsw.toNat := by
                        unfold globN; rw [hm_glob]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
                      have hm_other_glob : ∀ g : String, ofString g ≠ ofString "scratch_ptr" →
                          m.globals.lookup (ofString g) = s.globals.lookup (ofString g) := by
                        intro g hg; rw [hm_glob]
                        simp [HolFiniteMapExact.lookup_update, FUPDATE, hg, Ne.symm hg]
                      have hm_G : GuestInv m := by
                        have hcode_m : m.code = s.code := by
                          dsimp only [m]; rw [hs8_eq, hs7_eq]; dsimp only
                          rw [heff_mc_m11.code, hs5_code, hcode]
                        have hma_m : m.memaddrs = s.memaddrs := by
                          dsimp only [m]; rw [hs8_eq, hs7_eq]; dsimp only
                          rw [heff_mc_m11.memaddrs, hs5_ma, hInv.1.1.memaddrs]
                        have hsh_m : m.shMemaddrs = s.shMemaddrs := by
                          dsimp only [m]; rw [hs8_eq, hs7_eq]; dsimp only
                          rw [heff_mc_m11.shMemaddrs]
                          change saPost.shMemaddrs = s.shMemaddrs
                          rw [hsaPost_eq]; dsimp only [callEntryStateHOLFinite]; rw [hs4_eq]
                        have hba_m : m.baseAddr = s.baseAddr := by
                          dsimp only [m]; rw [hs8_eq, hs7_eq]; dsimp only
                          rw [heff_mc_m11.baseAddr]
                          change saPost.baseAddr = s.baseAddr
                          rw [hsaPost_eq]; dsimp only [callEntryStateHOLFinite]; rw [hs4_eq]
                        exact guestInv_congr hcode_m hma_m hsh_m hba_m hInv.1.1
                      have hsc_m : globN m "scratch_ptr" ≤ globN s "scratch_ptr" := by
                        rw [hm_sp_glob]; omega
                      have hAm : ArenaReady m := by
                        refine ⟨hm_G, ?_⟩
                        unfold ArenaOK
                        have hhp_m : globN m "heap_ptr" = globN s "heap_ptr" :=
                          OpHandlers.globN_eq_of_lookup_eq (hm_other_glob "heap_ptr" (by decide))
                        have hfp_m : globN m "frame_mem_ptr" = globN s "frame_mem_ptr" :=
                          OpHandlers.globN_eq_of_lookup_eq (hm_other_glob "frame_mem_ptr" (by decide))
                        rw [hhp_m, hfp_m, hm_sp_glob]
                        have hA := hInv.1.2
                        exact ⟨hA.1, hA.2.1, hA.2.2.1, hnsw_ge_fp,
                          le_trans (by omega : nsw.toNat ≤ globN s "scratch_ptr") hA.2.2.2.2.1,
                          hA.2.2.2.2.2.1, hA.2.2.2.2.2.2.1, hnsw_al,
                          globalsWord_update (ofString "scratch_ptr") nsw hm_glob hA.2.2.2.2.2.2.2.2⟩
                      have heff_s_s5 : ScratchByteEff s s5 [freshIvl, (globN s "ev", 280), (memW s (globN s "ev" + 8), 32 * memW s (globN s "ev" + 232))] :=
                        ⟨hs5_code.trans hcode.symm,
                         hs5_ma.trans hInv.1.1.memaddrs.symm,
                         by change saPost.shMemaddrs = _; rw [hsaPost_eq]; dsimp only [callEntryStateHOLFinite]; rw [hs4_eq],
                         by change saPost.baseAddr = _; rw [hsaPost_eq]; dsimp only [callEntryStateHOLFinite]; rw [hs4_eq],
                         by change saPost.be = _; rw [hsaPost_eq]; dsimp only [callEntryStateHOLFinite]; rw [hs4_eq],
                         fun g hg => by
                           change saPost.globals.lookup (ofString g) = _; rw [hsaPost_eq]
                           dsimp only [callEntryStateHOLFinite]; rw [hs4_eq]
                           simp [HolFiniteMapExact.lookup_update, FUPDATE, hg, Ne.symm hg],
                         fun a _ => by rw [hs5_mem],
                         fun a _ => by rw [hs5_mem],
                         fun b _ _ => by
                           unfold memB; rw [hs5_mem]
                           have hbe5 : s5.be = s.be := by
                             change saPost.be = _; rw [hsaPost_eq]; dsimp only [callEntryStateHOLFinite]; rw [hs4_eq]
                           rw [hbe5]⟩
                      have heff_m : ScratchByteEff s m
                          [freshIvl, (globN s "ev", 280), (memW s (globN s "ev" + 8), 32 * memW s (globN s "ev" + 232))] := by
                        have h1 := heff_mc.mono (R2 := [freshIvl, (globN s "ev", 280), (memW s (globN s "ev" + 8), 32 * memW s (globN s "ev" + 232))])
                          (fun x hx => by simp at hx; subst hx; exact ⟨freshIvl, by simp, le_refl _, le_refl _⟩)
                        have h2 := (ScratchByteEff.of_bre heff_st8).mono
                          (R2 := [freshIvl, (globN s "ev", 280), (memW s (globN s "ev" + 8), 32 * memW s (globN s "ev" + 232))])
                          (fun x hx => by simp at hx; subst hx; exact ⟨(globN s "ev", 280), by simp, le_refl _, le_refl _⟩)
                        have h3 := (ScratchByteEff.of_bre heff_st232).mono
                          (R2 := [freshIvl, (globN s "ev", 280), (memW s (globN s "ev" + 8), 32 * memW s (globN s "ev" + 232))])
                          (fun x hx => by simp at hx; subst hx; exact ⟨(globN s "ev", 280), by simp, le_refl _, le_refl _⟩)
                        exact (((heff_s_s5.trans h1).trans h2).trans h3).with_locals_clock m.locals s8.clock
                      have hs6_e0_eq : ∀ off, off + 8 ≤ 280 → off % 8 = 0 →
                          memW s6 (globN s "ev" + off) = memW s (globN s "ev" + off) := by
                        intro off hoff hoff8
                        unfold memW
                        rw [heff_mc_m11.cell_frame (BitVec.ofNat 64 (globN s "ev" + off)), hs5_mem]
                        intro x hx; simp at hx; subst hx
                        have htn : (BitVec.ofNat 64 (globN s "ev" + off)).toNat = globN s "ev" + off :=
                          Nat.mod_eq_of_lt (by omega)
                        rw [htn]
                        have he0_8 : (globN s "ev") % 8 = 0 := (hFW0.1 (globN s "ev", 280) (by simp)).2.1
                        have ha8 : (globN s "ev" + off) % 8 = 0 := by omega
                        obtain ⟨he0_scr, _⟩ := (hFW0.1 (globN s "ev", 280) (by simp)).1
                        exact not_cellHits_of_disj_aligned (i := (globN s "ev", 280)) ha8 hnsw_al
                          (Nat.le_add_right _ off) (Nat.add_le_add_left hoff _)
                          (Or.inr (Or.inr (Or.inr (by dsimp only [freshIvl] at he0_scr ⊢; omega))))
                      have hm_e0_other : ∀ off, off + 8 ≤ 280 → off % 8 = 0 → off ≠ 8 → off ≠ 232 →
                          memW m (globN s "ev" + off) = memW s (globN s "ev" + off) := by
                        intro off hoff hoff8 hne8 hne232
                        change memW s8 (globN s "ev" + off) = memW s (globN s "ev" + off)
                        rw [hs8_eq, R14Shards.OpHandlersA.memW_updW_ne s7 (globN s "ev" + 232) (globN s "ev" + off) _ (by omega) (by omega) (by omega),
                            hs7_eq, R14Shards.OpHandlersA.memW_updW_ne s6 (globN s "ev" + 8) (globN s "ev" + off) _ (by omega) (by omega) (by omega),
                            hs6_e0_eq off hoff hoff8]
                      have hm_e0_8 : memW m (globN s "ev" + 8) = nsw.toNat := by
                        change memW s8 (globN s "ev" + 8) = nsw.toNat
                        rw [hs8_eq, R14Shards.OpHandlersA.memW_updW_ne s7 (globN s "ev" + 232) (globN s "ev" + 8) _ (by omega) (by omega) (by omega),
                            hs7_eq, R14Shards.OpHandlersA.memW_updW_same s6 (globN s "ev" + 8) nsw]
                      have hm_e0_232 : memW m (globN s "ev" + 232) = ncapw.toNat := by
                        change memW s8 (globN s "ev" + 232) = ncapw.toNat
                        rw [hs8_eq, R14Shards.OpHandlersA.memW_updW_same s7 (globN s "ev" + 232) ncapw]
                      have hfresh_m : freshIvl = (0, 0) ∨
                          (freshIvl.1 % 8 = 0 ∧ freshIvl.2 % 8 = 0 ∧
                            Inside freshIvl (globN m "scratch_ptr") (globN s "scratch_ptr")) := by
                        right; refine ⟨hnsw_al, by dsimp only [freshIvl]; omega, ?_⟩
                        rw [hm_sp_glob]; exact ⟨le_refl _, le_of_eq hnsw_end⟩
                      have hnew_m :
                          (freshIvl.2 = 0 ∧ memW m (globN s "ev" + 8) = memW s (globN s "ev" + 8) ∧
                            memW m (globN s "ev" + 232) = memW s (globN s "ev" + 232)) ∨
                          (freshIvl.2 ≠ 0 ∧ (memW m (globN s "ev" + 8), 32 * memW m (globN s "ev" + 232)) = freshIvl) := by
                        right; refine ⟨by dsimp only [freshIvl]; omega, ?_⟩
                        rw [hm_e0_8, hm_e0_232]
                      have hm_loc_s4 : ∀ k, k ≠ ofString "ns" → k ≠ ofString "ncap" →
                          m.locals.lookup k = s4.locals.lookup k := by
                        intro k hk1 hk2
                        have hres_ne : ∀ (mp : HolFiniteMapExact MlS (ValueHOL 64)) (key q : MlS) (old : Option (ValueHOL 64)),
                            key ≠ q → (mp.resVarEq (key, old)).lookup q = mp.lookup q := by
                          intro mp key q old hne
                          unfold HolFiniteMapExact.resVarEq
                          cases old with
                          | none => simp [HolFiniteMapExact.eraseEq, FDOMSUB_HOL, hne.symm]
                          | some v => simp [HolFiniteMapExact.updateEq, FUPDATE_HOL, hne.symm]
                        have hs8_l : s8.locals = s5.locals := by
                          rw [hs8_eq, hs7_eq]; exact hs6_loc
                        dsimp only [m]
                        rw [hres_ne _ _ _ _ hk2.symm,
                            hres_ne _ _ _ _ hk1.symm,
                            hs8_l]
                        simp [hs5, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hk1, Ne.symm hk1]
                      exact run_tail m freshIvl hAm hsc_m hm_other_glob heff_m hfresh_m
                        (fun off hoff hoff8 h8 _ h232 => hm_e0_other off hoff hoff8 h8 h232)
                        hnew_m
                        (by rw [hm_e0_232]; omega)
                        (by rw [hm_e0_232]; exact hncap_le1024)
                        (by rw [hm_e0_other 16 (by omega) (by omega) (by omega) (by omega), ← hspw_eq])
                        (by rw [hm_loc_s4 (ofString "sp") (by decide) (by decide)]; exact hs4_sp)
                        (by rw [hm_loc_s4 (ofString "v") (by decide) (by decide)]; exact hs4_v)
      · have hsp_lt_cap : spw.toNat < capw.toNat := by
          rw [BitVec.le_def] at hgrow; omega
        simp only [hgrow, ↓reduceIte, evaluateHOLFiniteState_skip] at hnt ⊢
        exact run_tail s2 (0, 0)
          ⟨guestInv_congr (s := s) rfl rfl rfl rfl hInv.1.1, hInv.1.2⟩
          (le_refl _)
          (fun _ _ => rfl)
          ((ScratchByteEff.refl s _).with_locals_clock s2.locals s.clock)
          (Or.inl rfl)
          (fun _ _ _ _ _ _ => rfl)
          (Or.inl ⟨rfl, rfl, rfl⟩)
          (by change spw.toNat < memW s (globN s "ev" + 232); rw [← hcapw_eq]; exact hsp_lt_cap)
          (by change memW s (globN s "ev" + 232) ≤ 1024; rw [← hcapw_eq]; exact hcap_le1024)
          (by change memW s (globN s "ev" + 16) = spw.toNat; exact hspw_eq.symm)
          hs2_sp hs2_v

private theorem epsA_seq_call_ret0 {fname : MlS}
    (hf : EvmPreservingSpecA (fun _ => True)
      (fun s _ post => ∀ g : String, ofString g ≠ ofString "scratch_ptr" → globN post g = globN s g) fname)
    {F : Type} (s : PanSemStateFiniteExact 64 F) (args : List (ExpHOL 64))
    (hcode : s.code = originalRuntimeCode) (hInv : EvmInv s) (hHMWF : Group10.HeadMemChainWF s)
    (hnt : (evaluateHOLFiniteState s (.seq (.call (some (none, none)) fname args) (.return (.const 0#64)))).1 ≠ some .timeOut) :
    let r := (evaluateHOLFiniteState s (.seq (.call (some (none, none)) fname args) (.return (.const 0#64)))).1
    let post := (evaluateHOLFiniteState s (.seq (.call (some (none, none)) fname args) (.return (.const 0#64)))).2
    (∀ v, r = some (.returned v) →
      (EvmInv post ∧ Group10.HeadMemChainWF post) ∧ evmChain post = evmChain s ∧ evmR post ≤ evmR s ∧
      (∀ g : String, ofString g ≠ ofString "scratch_ptr" → globN post g = globN s g)) ∧
    (IsEvmErr r →
      (EvmInv post ∧ Group10.HeadMemChainWF post) ∧ evmChain post = evmChain s ∧ evmR post ≤ evmR s) := by
  dsimp only
  have herr_triv : ∀ {P1 P2 : Prop},
      (∀ v, (some PanSemResultExact.error : Option (PanSemResultExact 64)) = some (.returned v) → P1) ∧
      (IsEvmErr (some PanSemResultExact.error) → P2) := by
    intro _ _; constructor
    · intro _ h; cases h
    · rintro ⟨_, h⟩; cases h
  obtain ⟨params, body, retShape, hlk, hspec⟩ := hf
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_call] at hnt ⊢
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vals
  · exact herr_triv
  · simp only [hargs] at hnt ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname vals with _ | ⟨body', callee, ret'⟩
    · exact herr_triv
    · simp only [hl] at hnt ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt ⊢
        have hbody_eq : body' = body :=
          lookupCodeHOLFinite_installed_body s.code.lookup fname params body body' retShape ret' vals callee
            (by rw [hcode]; exact hlk) hl
        subst body'
        have hret_eq : ret' = retShape := by
          have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some s.code.lookup fname vals body callee ret' hl
          rw [hcode] at hx; simp only [Flapjack.lookupCodeHOLExact, hlk] at hx
          split at hx
          · exact (congrArg (fun x => x.2.2) (Option.some.inj hx)).symm
          · cases hx
        subst ret'
        have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup fname vals = some (body, callee, retShape) := by
          rwa [← hcode]
        have hInv_ce : EvmInv (callEntryStateHOLFinite s callee) := localsFree_evmInv s callee (s.clock - 1) hInv
        have hHMWF_ce : Group10.HeadMemChainWF (callEntryStateHOLFinite s callee) :=
          Group10.headMemChainWF_locals s callee (s.clock - 1) hHMWF
        have hc_ce := evm_congr (s := s) (t := callEntryStateHOLFinite s callee) rfl rfl
        have hs_spec := hspec (callEntryStateHOLFinite s callee) hcode hInv_ce hHMWF_ce trivial ⟨vals, hl_orig⟩
        dsimp only at hs_spec
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨res, cpost⟩
        simp only [hrun] at hnt hs_spec ⊢
        cases res with
        | none => exact herr_triv
        | some r0 =>
          cases r0 with
          | timeOut => simp at hnt
          | returned vr =>
            by_cases hsh : shapeEqHOL (shapeOfHOLExact vr) retShape = true
            · simp only [hsh, ↓reduceIte]
              obtain ⟨⟨hInv_cp, hHMWF_cp⟩, hch_cp, hR_cp, hg_cp⟩ := (hs_spec (by simp)).1 vr rfl
              rw [evaluateHOLFiniteState_return]; dsimp only [evalHOLExact]
              have hsz0 : sizeOfShapeWithContextHOL cpost.structs
                  (shapeOfHOLExact (.val (.word 0#64))) ≤ 32 := by
                simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
              rw [if_pos hsz0]; dsimp only
              let post := ({ cpost with locals := s.locals } : PanSemStateFiniteExact 64 F).emptyLocalsHOLFinite
              have hInv_p : EvmInv post := localsFree_evmInv cpost post.locals cpost.clock hInv_cp
              have hHMWF_p : Group10.HeadMemChainWF post :=
                Group10.headMemChainWF_locals cpost post.locals cpost.clock hHMWF_cp
              have hc_p := evm_congr (s := cpost) (t := post) rfl rfl
              have hch_final : evmChain post = evmChain s := by
                have h1 : evmChain post = evmChain cpost := evmChain_congr rfl rfl
                have h2 : evmChain (callEntryStateHOLFinite s callee) = evmChain s := evmChain_congr rfl rfl
                exact h1.trans (hch_cp.trans h2)
              have hR_final : evmR post ≤ evmR s := by
                rw [hc_p.2.1]; rw [hc_ce.2.1] at hR_cp; exact hR_cp
              have hg_final : ∀ g : String, ofString g ≠ ofString "scratch_ptr" → globN post g = globN s g :=
                fun g hg => hg_cp g hg
              constructor
              · intro _ _; exact ⟨⟨hInv_p, hHMWF_p⟩, hch_final, hR_final, hg_final⟩
              · rintro ⟨_, h⟩; cases h
            · simp only [hsh, Bool.false_eq_true, ↓reduceIte]
              exact herr_triv
          | exception eid ev =>
            dsimp only
            by_cases heid : eid = ofString "EvmErr"
            · subst heid
              obtain ⟨⟨hInv_cp, hHMWF_cp⟩, hch_cp, hR_cp⟩ := (hs_spec (by simp)).2 ⟨ev, rfl⟩
              have hInv_el : EvmInv cpost.emptyLocalsHOLFinite := localsFree_evmInv cpost _ cpost.clock hInv_cp
              have hHMWF_el : Group10.HeadMemChainWF cpost.emptyLocalsHOLFinite :=
                Group10.headMemChainWF_locals cpost _ cpost.clock hHMWF_cp
              have hc_el := evm_congr (s := cpost) (t := cpost.emptyLocalsHOLFinite) rfl rfl
              have hch_final : evmChain cpost.emptyLocalsHOLFinite = evmChain s := by
                have h1 : evmChain cpost.emptyLocalsHOLFinite = evmChain cpost := evmChain_congr rfl rfl
                have h2 : evmChain (callEntryStateHOLFinite s callee) = evmChain s := evmChain_congr rfl rfl
                exact h1.trans (hch_cp.trans h2)
              have hR_final : evmR cpost.emptyLocalsHOLFinite ≤ evmR s := by
                rw [hc_el.2.1]; rw [hc_ce.2.1] at hR_cp; exact hR_cp
              constructor
              · intro _ h; cases h
              · intro _; exact ⟨⟨hInv_el, hHMWF_el⟩, hch_final, hR_final⟩
            · constructor
              · intro _ h; cases h
              · rintro ⟨_, h⟩; injection h with h'; injection h' with h1 _; exact (heid h1).elim
          | «break» => exact herr_triv
          | «continue» => exact herr_triv
          | finalFfi _ =>
            constructor
            · intro _ h; cases h
            · rintro ⟨_, h⟩; cases h
          | error => exact herr_triv

theorem epsA_stack_push_word :
    EvmPreservingSpecA (fun _ => True)
      (fun s _ post => ∀ g : String, ofString g ≠ ofString "scratch_ptr" → globN post g = globN s g)
      (ofString "stack_push_word") := by
  refine ⟨_, _, _, lookup_stack_push_word, ?_⟩
  intro F s hcode hInv hHMWF _ _ hnt
  have hb : sourceFnBody Guest.Software.guestFn_stack_push_word =
      .seq
        (.call (some (none, none)) (ofString "stack_push")
          [.rstruct [.var .local (ofString "w"), .const 0#64, .const 0#64, .const 0#64]])
        (.return (.const 0#64)) := rfl
  dsimp only; rw [hb] at hnt ⊢
  exact epsA_seq_call_ret0 epsA_stack_push s _ hcode hInv hHMWF hnt

theorem epsA_stack_push_bool :
    EvmPreservingSpecA (fun _ => True)
      (fun s _ post => ∀ g : String, ofString g ≠ ofString "scratch_ptr" → globN post g = globN s g)
      (ofString "stack_push_bool") := by
  refine ⟨_, _, _, lookup_stack_push_bool, ?_⟩
  intro F s hcode hInv hHMWF _ _ hnt
  have hb : sourceFnBody Guest.Software.guestFn_stack_push_bool =
      .seq
        (.ite (.cmp .notEqual (.var .local (ofString "b")) (.const 0#64))
          (.call (some (none, none)) (ofString "stack_push")
            [.rstruct [.const 1#64, .const 0#64, .const 0#64, .const 0#64]])
          (.call (some (none, none)) (ofString "stack_push")
            [.rstruct [.const 0#64, .const 0#64, .const 0#64, .const 0#64]]))
        (.return (.const 0#64)) := rfl
  dsimp only; rw [hb] at hnt ⊢
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt ⊢
  revert hnt
  split
  · rename_i cw _
    by_cases hcw0 : cw = 0
    · subst hcw0; simp only [↓reduceIte]
      rw [← evaluateHOLFiniteState_seq_line780]
      intro hnt; exact epsA_seq_call_ret0 epsA_stack_push s _ hcode hInv hHMWF hnt
    · simp only [hcw0, ↓reduceIte]
      rw [← evaluateHOLFiniteState_seq_line780]
      intro hnt; exact epsA_seq_call_ret0 epsA_stack_push s _ hcode hInv hHMWF hnt
  · intro _
    constructor
    · intro _ h; cases h
    · rintro ⟨_, h⟩; cases h

theorem evmInv_of_head_retdata_reset {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (hInv : EvmInv s)
    (hGp : GuestInv post)
    (hglob : post.globals = s.globals)
    (hbe : post.be = s.be)
    (hmem_out : ∀ x : BitVec 64,
      (∀ off ∈ ([144, 152, 216] : List Nat), x ≠ BitVec.ofNat 64 (globN s "ev" + off)) →
      post.memory x = s.memory x)
    (h216 : memW post (globN s "ev" + 216) = 0)
    (h144 : memW post (globN s "ev" + 144) = globN s "evm_empty") :
    EvmInv post ∧ evmChain post = evmChain s ∧ evmR post = evmR s := by
  obtain ⟨hAs, S, hW, hch_ne, hch_len, hch_last, hFW_all, hFR_all, hRW, hFO_pw, hFO_disj, hAT, hMarks, hRoles, hGas⟩ := hInv
  obtain ⟨Nd_at, hTr_at, hAT_at⟩ := hAT
  have hWT : WorldTypedWith s S Nd_at := ⟨hW.1, hW.2.1, hW.2.2.1, hTr_at⟩
  set e0 := globN s "ev"
  set c0 := globN s "cur_cont"
  have hch_cons : ∃ tl, evmChain s = (e0, c0) :: tl := ⟨_, rfl⟩
  obtain ⟨chTail, hch_eq⟩ := hch_cons
  have hhead_mem : (e0, c0) ∈ evmChain s := by rw [hch_eq]; exact List.mem_cons_self
  have hhead_FW := hFW_all _ hhead_mem
  obtain ⟨hb1, _, _, _⟩ := frameWF_bounds hAs.2 hhead_FW
  dsimp only at hb1
  have he0_8 : e0 % 8 = 0 := (hhead_FW.1 (e0, 280) (by simp)).2.1
  have hdom_eq : post.memaddrs = s.memaddrs := hGp.memaddrs.trans hAs.1.memaddrs.symm
  have hoff_props : ∀ off ∈ ([144, 152, 216] : List Nat),
      off + 8 ≤ 280 ∧ off % 8 = 0 ∧ s.memaddrs (BitVec.ofNat 64 (e0 + off)) := by
    intro off hoff
    have hdiv : off + 8 ≤ 280 ∧ off % 8 = 0 ∧ off / 8 < 280 / 8 ∧ 8 * (off / 8) = off := by
      revert off hoff; decide
    obtain ⟨_, hdom, _⟩ := (hhead_FW.1 (e0, 280) (by simp)).2.2.2 (off / 8) hdiv.2.2.1
    exact ⟨hdiv.1, hdiv.2.1, by simpa [hdiv.2.2.2] using hdom⟩
  have heff : ByteRegionEffect s post [(e0, 280)] := by
    refine ⟨hGp.code.trans hAs.1.code.symm, hdom_eq,
      hGp.shMemaddrs.trans hAs.1.shMemaddrs.symm,
      hGp.baseAddr.trans hAs.1.baseAddr.symm, hbe, hglob, ?_, ?_, ?_⟩
    · intro a hna
      apply hmem_out a
      intro off hoff rfl
      exact hna (hoff_props off hoff).2.2
    · intro a ha
      apply hmem_out a
      intro off hoff rfl
      have hp := hoff_props off hoff
      have htn : (BitVec.ofNat 64 (e0 + off)).toNat = e0 + off := Nat.mod_eq_of_lt (by omega)
      exact ha (e0, 280) (by simp) ⟨by rw [htn]; omega, by rw [htn]; omega⟩
    · intro b hb hno
      unfold memB
      have hal_b : (panByteAlignHOL (BitVec.ofNat 64 b)).toNat = b / 8 * 8 := by
        rw [panByteAlign_toNat64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
      rw [hmem_out (panByteAlignHOL (BitVec.ofNat 64 b)), hbe]
      intro off hoff heq
      have hp := hoff_props off hoff
      have htn : (BitVec.ofNat 64 (e0 + off)).toNat = e0 + off := Nat.mod_eq_of_lt (by omega)
      have := congrArg BitVec.toNat heq
      rw [hal_b, htn] at this
      exact hno (e0, 280) (by simp) ⟨by dsimp only; omega, by dsimp only; omega⟩
  have hRl8_e0 : ∀ x ∈ ([(e0, 280)] : List Ivl), x.1 % 8 = 0 := by
    intro x hx; simp only [List.mem_singleton] at hx; subst hx; exact he0_8
  have hglob_eq : ∀ nm, globN post nm = globN s nm := fun nm => by simp [globN, hglob]
  have hApost : ArenaReady post := ⟨hGp, arenaOK_congr hglob hAs.2⟩
  have hh : globN s "heap_ptr" ≤ globN post "heap_ptr" := by rw [hglob_eq]
  have hsc : globN post "scratch_ptr" ≤ globN s "scratch_ptr" := by rw [hglob_eq]
  have hrec_fo : (e0, 280) ∈ frameObjects s (e0, c0) := by simp [frameObjects]
  have hrec_disj_wti : ∀ i ∈ worldTypedIvls s S Nd_at, i.2 = 0 ∨ Disj (e0, 280) i := by
    intro i hi
    unfold worldTypedIvls at hi
    simp only [List.mem_append] at hi
    rcases hi with ((((h1 | h2) | h3) | h4) | h5) | h6
    · obtain ⟨t, ht, hfp⟩ := List.mem_flatMap.1 h1
      exact Or.inr ((hFO_disj _ hhead_mem _ hrec_fo).1 t ht i hfp)
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 h2
      exact Or.inr ((hFO_disj _ hhead_mem _ hrec_fo).2 _ (typedRec_in_fixedObjects s hr))
    · simp only [List.mem_singleton] at h3; subst h3
      have hfix_j : (if globN s "journal_cap" = 0 then 0 else globN s "journal", 32 * globN s "journal_cap") ∈ fixedObjects s := by
        unfold fixedObjects
        exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (by simp)))
      exact Or.inr ((hFO_disj _ hhead_mem _ hrec_fo).2 _ hfix_j)
    · exact Or.inr ((hFO_disj _ hhead_mem _ hrec_fo).2 _ (blockOut_in_fixedObjects h4))
    · exact Or.inr ((hFO_disj _ hhead_mem _ hrec_fo).2 _ (bal_in_fixedObjects h5))
    · exact Or.inr (hAT_at _ (List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨_, hhead_mem, rfl⟩, hrec_fo⟩) i h6)
  have hcell : SameTypedCells s post S Nd_at :=
    ByteRegionEffect.sameTypedCells (Rl := []) (extra := [(e0, 280)]) hAs.1.memaddrs hWT
      (fun _ h => by simp at h)
      (fun x hx => by simp at hx; subst hx; exact hrec_disj_wti)
      (by simpa using heff)
  have hfeq := fixedObjects_eq_of_nonHeapGlobalsKept hAs.2 hWT.1 hWT.2.2.1 hcell
    (fun name _ _ _ => by rw [hglob])
  have hFT_post := fixedTyped_of_eq hApost hWT.2.2.1 hh hsc hfeq
  obtain ⟨hWT_post, _⟩ := worldTypedWith_congr_w1 hAs hApost hh hsc
    (fun g _ => hglob_eq g) hcell hWT
    ⟨hFT_post, fun o ho => Or.inl (by rw [← hfeq]; exact ho)⟩
  have hW_post : WorldTyped post S :=
    ⟨hWT_post.1, hWT_post.2.1, hWT_post.2.2.1, Nd_at, hWT_post.2.2.2⟩
  have hmemW_ne : ∀ a : Nat, a < 2 ^ 64 →
      (∀ off ∈ ([144, 152, 216] : List Nat), a ≠ e0 + off) → memW post a = memW s a := by
    intro a ha hne
    unfold memW
    rw [hmem_out (BitVec.ofNat 64 a)]
    intro off hoff heq
    have hp := hoff_props off hoff
    have := congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (by omega)] at this
    exact hne off hoff this
  have hpw_head_tail :
      (frameObjects s (e0, c0)).Pairwise Disj ∧
      (∀ o1 ∈ frameObjects s (e0, c0),
        ∀ ec ∈ chTail, ∀ o2 ∈ frameObjects s ec, Disj o1 o2) := by
    have hpw := hFO_pw
    rw [hch_eq, List.map_cons, List.flatten_cons, List.pairwise_append] at hpw
    refine ⟨hpw.1, fun o1 ho1 ec hec o2 ho2 => hpw.2.2 o1 ho1 o2 ?_⟩
    exact List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨ec, hec, rfl⟩, ho2⟩
  have hhead_disj_rest : ∀ o ∈ ((c0, 104) :: (memW s (e0 + 8), 32 * memW s (e0 + 232)) ::
      (memW s (e0 + 24), memW s (e0 + 40)) :: (memW s (e0 + 88), 24) ::
      frameLogs s (e0, c0) :: frameRet s (e0, c0) :: frameLogObjects s (e0, c0)),
      Disj (e0, 280) o := by
    have hpw0 := hpw_head_tail.1
    unfold frameObjects at hpw0
    exact (List.pairwise_cons.1 hpw0).1
  have hdisj_e0_nonrec : ∀ ec ∈ evmChain s,
      Disj (e0, 280) (ec.2, 104) ∧
      Disj (e0, 280) (memW s (ec.1 + 88), 24) ∧
      Disj (e0, 280) (frameLogs s ec) ∧
      (∀ i < memW s (memW s (ec.1 + 88) + 8),
        Disj (e0, 280) (memW s (memW s (memW s (ec.1 + 88)) + 8 * i), 40)) := by
    intro ec hec
    rw [hch_eq, List.mem_cons] at hec
    rcases hec with rfl | htail
    · refine ⟨hhead_disj_rest _ (by simp), hhead_disj_rest _ (by simp),
        hhead_disj_rest _ (by simp), fun i hi => hhead_disj_rest _ ?_⟩
      simp only [List.mem_cons]
      right; right; right; right; right; right
      unfold frameLogObjects; dsimp only
      exact List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, by unfold logOwnedIvls logRecordIvls; exact List.mem_filter.2 ⟨by simp, by simp⟩⟩
    · refine ⟨hpw_head_tail.2 _ hrec_fo ec htail _ (by simp [frameObjects]),
        hpw_head_tail.2 _ hrec_fo ec htail _ (by simp [frameObjects]),
        hpw_head_tail.2 _ hrec_fo ec htail _ (by simp [frameObjects]),
        fun i hi => hpw_head_tail.2 _ hrec_fo ec htail _ ?_⟩
      unfold frameObjects; apply List.mem_append_right
      unfold frameLogObjects; dsimp only
      exact List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, by unfold logOwnedIvls logRecordIvls; exact List.mem_filter.2 ⟨by simp, by simp⟩⟩
  have hrec_eq : ∀ ec ∈ evmChain s,
      (∀ k, k + 8 ≤ 280 → k ∉ ([144, 152, 216] : List Nat) → memW post (ec.1 + k) = memW s (ec.1 + k)) ∧
      (∀ k, k + 8 ≤ 104 → k % 8 = 0 → memW post (ec.2 + k) = memW s (ec.2 + k)) ∧
      (∀ k, k + 8 ≤ 24 → k % 8 = 0 → memW post (memW s (ec.1 + 88) + k) = memW s (memW s (ec.1 + 88) + k)) := by
    intro ec hec
    have hFW := hFW_all ec hec
    obtain ⟨hb_e, hb_c, hb_88, _⟩ := frameWF_bounds hAs.2 hFW
    have hc8 : ec.2 % 8 = 0 := (hFW.1 (ec.2, 104) (by simp)).2.1
    have h88_8 : (memW s (ec.1 + 88)) % 8 = 0 := (hFW.1 (memW s (ec.1 + 88), 24) (by simp)).2.1
    obtain ⟨hd_c, hd_88, _, _⟩ := hdisj_e0_nonrec ec hec
    refine ⟨?_,
      fun k hk hk8 => memW_eq_of_disj_eff heff hRl8_e0 hb_c hc8 hk8 hk (fun x hx => by simp at hx; subst hx; exact hd_c),
      fun k hk hk8 => memW_eq_of_disj_eff heff hRl8_e0 hb_88 h88_8 hk8 hk (fun x hx => by simp at hx; subst hx; exact hd_88)⟩
    intro k hk hknot
    apply hmemW_ne (ec.1 + k) (by omega)
    intro off hoff heq
    have hp := hoff_props off hoff
    rw [hch_eq, List.mem_cons] at hec
    rcases hec with rfl | htail
    · have : k = off := by dsimp only at heq; omega
      exact hknot (this ▸ hoff)
    · have hd := hpw_head_tail.2 (e0, 280) hrec_fo ec htail (ec.1, 280) (by simp [frameObjects])
      rcases hd with h0 | h0 | h1 | h2 <;> dsimp only at * <;> omega
  have htail_rec_eq : ∀ ec ∈ chTail, ∀ k, k + 8 ≤ 280 → memW post (ec.1 + k) = memW s (ec.1 + k) := by
    intro ec htail k hk
    have hFW := hFW_all ec (by rw [hch_eq]; exact List.mem_cons_of_mem _ htail)
    obtain ⟨hb_e, _, _, _⟩ := frameWF_bounds hAs.2 hFW
    apply hmemW_ne (ec.1 + k) (by omega)
    intro off hoff heq
    have hp := hoff_props off hoff
    have hd := hpw_head_tail.2 (e0, 280) hrec_fo ec htail (ec.1, 280) (by simp [frameObjects])
    rcases hd with h0 | h0 | h1 | h2 <;> dsimp only at * <;> omega
  have hchain_aux : ∀ (fuel e c : Nat),
      (∀ ec ∈ evmChainFrom s fuel e c, ec ∈ evmChain s) →
      evmChainFrom post fuel e c = evmChainFrom s fuel e c := by
    intro fuel; induction fuel with
    | zero => intros; rfl
    | succ fuel ih =>
      intro e c hsub
      have hec : (e, c) ∈ evmChain s := hsub (e, c) (by simp [evmChainFrom])
      obtain ⟨_, hc_eq, _⟩ := hrec_eq (e, c) hec
      have hc16 := hc_eq 16 (by omega) (by omega)
      have hc0 : memW post c = memW s c := by simpa using hc_eq 0 (by omega) (by omega)
      have hc8 := hc_eq 8 (by omega) (by omega)
      simp only [evmChainFrom, hc16, hc0, hc8]
      split
      · rfl
      · rename_i hne16
        rw [ih]; intro ec' hec'; exact hsub ec' (by simp [evmChainFrom, hne16, hec'])
  have hchain_eq : evmChain post = evmChain s := by
    unfold evmChain; rw [hglob_eq "ev", hglob_eq "cur_cont"]
    exact hchain_aux _ _ _ (fun _ h => h)
  have hframeLogs_eq : ∀ ec ∈ evmChain s, frameLogs post ec = frameLogs s ec := by
    intro ec hec
    obtain ⟨he_eq, _, h88_eq⟩ := hrec_eq ec hec
    unfold frameLogs
    rw [he_eq 88 (by omega) (by decide),
        show memW post (memW s (ec.1 + 88)) = memW s (memW s (ec.1 + 88)) by simpa using h88_eq 0 (by omega) (by omega),
        h88_eq 16 (by omega) (by omega)]
  have hhead_frameRet : frameRet post (e0, c0) = (0, 0) := by
    unfold frameRet; simp [h216]
  have htail_frameRet_eq : ∀ ec ∈ chTail, frameRet post ec = frameRet s ec := by
    intro ec htail
    unfold frameRet
    rw [htail_rec_eq ec htail 216 (by omega), htail_rec_eq ec htail 144 (by omega)]
  have hlogs_congr : ∀ ec ∈ evmChain s,
      frameLogObjects post ec = frameLogObjects s ec ∧ LogsListOK post (memW post (ec.1 + 88)) := by
    intro ec hec
    have hFW := hFW_all ec hec
    obtain ⟨_, _, _, hfob⟩ := frameWF_bounds hAs.2 hFW
    obtain ⟨he_eq, _, h88_eq⟩ := hrec_eq ec hec
    obtain ⟨_, _, hd_fl, hd_lr⟩ := hdisj_e0_nonrec ec hec
    have hl0 : memW post (memW s (ec.1 + 88)) = memW s (memW s (ec.1 + 88)) := by
      simpa using h88_eq 0 (by omega) (by omega)
    have hl8 : memW post (memW s (ec.1 + 88) + 8) = memW s (memW s (ec.1 + 88) + 8) :=
      h88_eq 8 (by omega) (by omega)
    have hl16 : memW post (memW s (ec.1 + 88) + 16) = memW s (memW s (ec.1 + 88) + 16) :=
      h88_eq 16 (by omega) (by omega)
    have harr_eq : ∀ i, i < memW s (memW s (ec.1 + 88) + 8) →
        memW post (memW s (memW s (ec.1 + 88)) + 8 * i) = memW s (memW s (memW s (ec.1 + 88)) + 8 * i) := by
      intro i hi
      have hfl_in : frameLogs s ec ∈ frameObjects s ec := by simp [frameObjects]
      have hlen_le : memW s (memW s (ec.1 + 88) + 8) ≤ memW s (memW s (ec.1 + 88) + 16) :=
        hFW.2.2.2.2.2.2.2.2.2.2.2.1
      have hfl_b : (frameLogs s ec).1 + (frameLogs s ec).2 ≤ 2 ^ 64 := by
        rcases hfob _ hfl_in with h0 | hb
        · unfold frameLogs at h0; dsimp only at h0; omega
        · exact hb
      have hfl_8 : (memW s (memW s (ec.1 + 88))) % 8 = 0 := hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
      exact memW_eq_of_disj_eff heff hRl8_e0 hfl_b hfl_8 (by omega)
        (by unfold frameLogs; dsimp only; omega)
        (fun x hx => by simp at hx; subst hx; exact hd_fl)
    have hlr_eq : ∀ i (hi : i < memW s (memW s (ec.1 + 88) + 8)) off, off + 8 ≤ 40 → off % 8 = 0 →
        memW post (memW s (memW s (memW s (ec.1 + 88)) + 8 * i) + off) =
          memW s (memW s (memW s (memW s (ec.1 + 88)) + 8 * i) + off) := by
      intro i hi off hoff hoff8
      have hlr_in : (memW s (memW s (memW s (ec.1 + 88)) + 8 * i), 40) ∈ frameObjects s ec := by
        unfold frameObjects; apply List.mem_append_right
        unfold frameLogObjects; dsimp only
        exact List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, by unfold logOwnedIvls logRecordIvls; exact List.mem_filter.2 ⟨by simp, by simp⟩⟩
      have hlr_b : memW s (memW s (memW s (ec.1 + 88)) + 8 * i) + 40 ≤ 2 ^ 64 := by
        rcases hfob _ hlr_in with h0 | hb
        · dsimp only at h0; omega
        · exact hb
      have hlr_8 : (memW s (memW s (memW s (ec.1 + 88)) + 8 * i)) % 8 = 0 := by
        rcases hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with hz | ⟨_, _, _, _, hent⟩
        · have he88_in := (hFW.1 (memW s (ec.1 + 88), 24) (by simp)).1.1
          have h1 := hAs.2.2.2.1; have h2 := hAs.2.2.2.2.1
          rw [R11Shards.scratchStart_val] at h1; dsimp only at he88_in; omega
        · exact (hent i hi).2.1.1
      exact memW_eq_of_disj_eff heff hRl8_e0 hlr_b hlr_8 hoff8 hoff
        (fun x hx => by simp at hx; subst hx; exact hd_lr i hi)
    refine ⟨?_, ?_⟩
    · unfold frameLogObjects; dsimp only
      rw [he_eq 88 (by omega) (by decide), hl8]
      apply List.flatMap_congr; intro i hi; rw [List.mem_range] at hi
      rw [hl0, harr_eq i hi]
      have r0 := hlr_eq i hi 0 (by omega) (by omega)
      have r8 := hlr_eq i hi 8 (by omega) (by omega)
      have r16 := hlr_eq i hi 16 (by omega) (by omega)
      have r24 := hlr_eq i hi 24 (by omega) (by omega)
      have r32 := hlr_eq i hi 32 (by omega) (by omega)
      simp only [Nat.add_zero] at r0
      unfold logOwnedIvls logRecordIvls
      rw [r0, r8, r16, r24, r32, hglob_eq "vm_system_address"]
    · rw [he_eq 88 (by omega) (by decide)]
      rcases hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with hz | ⟨hw_l, hal_l, hlt28, hle_cap, hent⟩
      · exact Or.inl hz
      · right
        refine ⟨(wordsOK_congr_dom hdom_eq).2 hw_l, allocated_mono hh hsc hal_l,
          by rw [hl8]; exact hlt28, by rw [hl8, hl16]; exact hle_cap, fun i hi => ?_⟩
        rw [hl8] at hi; rw [hl0]
        obtain ⟨hwa, hle⟩ := hent i hi
        refine ⟨(wordAt_congr_dom hdom_eq).2 hwa, ?_⟩
        rw [harr_eq i hi]
        have r0 := hlr_eq i hi 0 (by omega) (by omega)
        have r8 := hlr_eq i hi 8 (by omega) (by omega)
        have r16 := hlr_eq i hi 16 (by omega) (by omega)
        have r24 := hlr_eq i hi 24 (by omega) (by omega)
        have r32 := hlr_eq i hi 32 (by omega) (by omega)
        simp only [Nat.add_zero] at r0
        unfold LogEntryOK at hle ⊢
        rw [r0, r8, r16, r24, r32, hglob_eq "heap_ptr"]
        exact ⟨(wordsOK_congr_dom hdom_eq).2 hle.1, hle.2⟩
  have htail_fo_eq : ∀ ec ∈ chTail, frameObjects post ec = frameObjects s ec := by
    intro ec htail
    have hec : ec ∈ evmChain s := by rw [hch_eq]; exact List.mem_cons_of_mem _ htail
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    unfold frameObjects
    rw [he_eq 8 (by omega) (by decide), he_eq 232 (by omega) (by decide),
        he_eq 24 (by omega) (by decide), he_eq 40 (by omega) (by decide),
        he_eq 88 (by omega) (by decide),
        hframeLogs_eq ec hec, htail_frameRet_eq ec htail, (hlogs_congr ec hec).1]
  have hfo_post_cases : ∀ ec ∈ evmChain s, ∀ o ∈ frameObjects post ec,
      o ∈ frameObjects s ec ∨ o = (0, 0) := by
    intro ec hec o ho
    rw [hch_eq, List.mem_cons] at hec
    rcases hec with rfl | htail
    · obtain ⟨he_eq, _, _⟩ := hrec_eq (e0, c0) hhead_mem
      unfold frameObjects at ho
      rw [he_eq 8 (by omega) (by decide), he_eq 232 (by omega) (by decide),
          he_eq 24 (by omega) (by decide), he_eq 40 (by omega) (by decide),
          he_eq 88 (by omega) (by decide),
          hframeLogs_eq _ hhead_mem, hhead_frameRet, (hlogs_congr _ hhead_mem).1] at ho
      rcases List.mem_append.1 ho with ho7 | holog
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at ho7
        rcases ho7 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact Or.inl (by simp [frameObjects])
        · exact Or.inl (by simp [frameObjects])
        · exact Or.inl (by simp [frameObjects])
        · exact Or.inl (by simp [frameObjects])
        · exact Or.inl (by simp [frameObjects])
        · exact Or.inl (by simp [frameObjects])
        · exact Or.inr rfl
      · exact Or.inl (by unfold frameObjects; exact List.mem_append_right _ holog)
    · exact Or.inl (by rwa [htail_fo_eq ec htail] at ho)
  have hframeScratch_eq : ∀ ec ∈ evmChain s, frameScratch post ec = frameScratch s ec := by
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    unfold frameScratch
    rw [he_eq 8 (by omega) (by decide), he_eq 232 (by omega) (by decide),
        he_eq 88 (by omega) (by decide)]
  have hfo_idx3_eq : ∀ ec ∈ evmChain s, (frameObjects post ec)[3]! = (frameObjects s ec)[3]! := by
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    unfold frameObjects
    simp [he_eq 24 (by omega) (by decide), he_eq 40 (by omega) (by decide)]
  have hframeRoleSlots_eq : frameRoleSlots post (evmChain s) = frameRoleSlots s (evmChain s) := by
    unfold frameRoleSlots; apply List.flatMap_congr; intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    rw [he_eq 136 (by omega) (by decide), he_eq 168 (by omega) (by decide),
        he_eq 176 (by omega) (by decide)]
  have hfp_eq_all : ∀ t ∈ S, htabFootprint post t = htabFootprint s t :=
    fun t ht => htabFootprint_eq hcell ht (hWT.1.2.1 t ht).1
  have hR_eq : evmR post = evmR s :=
    evmR_eq_of_chain_and_words hchain_eq (fun ec hec =>
      ⟨(hrec_eq ec hec).1 64 (by omega) (by decide),
       (hrec_eq ec hec).1 192 (by omega) (by decide)⟩)
  refine ⟨⟨hApost, S, hW_post, ?_⟩, hchain_eq, hR_eq⟩
  dsimp only; rw [hchain_eq]
  refine ⟨hch_ne, hch_len, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨ec, hec, hk0⟩ := hch_last
    have hec_mem := List.mem_of_mem_getLast? hec
    exact ⟨ec, hec, by rw [(hrec_eq ec hec_mem).2.1 16 (by omega) (by omega)]; exact hk0⟩
  · intro ec hec
    obtain ⟨he_eq, _, h88_eq⟩ := hrec_eq ec hec
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, _, c17⟩ := hFW_all ec hec
    have hlo_ok := (hlogs_congr ec hec).2
    have hmsg_ok : MsgOwned post S (memW post (ec.1 + 112)) := by
      rw [he_eq 112 (by omega) (by decide)]
      obtain ⟨hal_m, hw_m, hdt, hdf, hdfo, Nd_m, hTr_m, hdj_m⟩ := c17
      obtain ⟨hTr_int, hsub_int⟩ := R11Shards.triesTypedWith_inter hTr_at hTr_m
      set Ndi := Nd_at.filter (fun n => decide (n ∈ Nd_m))
      have hcell_i : SameTypedCells s post S Ndi := by
        have hwti_sub : ∀ i ∈ worldTypedIvls s S Ndi, i ∈ worldTypedIvls s S Nd_at := by
          intro i hi; unfold worldTypedIvls at hi ⊢
          rcases List.mem_append.1 hi with hpre | hne
          · exact List.mem_append_left _ hpre
          · apply List.mem_append_right; unfold nodeExtents at hne ⊢
            obtain ⟨n, hn, hnx⟩ := List.mem_flatMap.1 hne
            exact List.mem_flatMap.2 ⟨n, (List.mem_filter.1 hn).1, hnx⟩
        refine ⟨hcell.1, hcell.2.1, hcell.2.2.1, hcell.2.2.2.1,
          fun a ha ha8 ⟨i, hi, h1, h2⟩ => hcell.2.2.2.2.1 a ha ha8 ⟨i, hwti_sub i hi, h1, h2⟩,
          fun b hb ⟨i, hi, h1, h2⟩ => hcell.2.2.2.2.2 b hb ⟨i, hwti_sub i hi, h1, h2⟩⟩
      obtain ⟨hWT_i_post, _⟩ := worldTypedWith_congr_w1 hAs hApost hh hsc
        (fun g _ => hglob_eq g) hcell_i ⟨hWT.1, hWT.2.1, hWT.2.2.1, hTr_int⟩
        ⟨hFT_post, fun o ho => Or.inl (by rw [← hfeq]; exact ho)⟩
      refine ⟨allocated_mono hh hsc hal_m, (wordsOK_congr_dom hdom_eq).2 hw_m,
        fun t ht i hi => by rw [hfp_eq_all t ht] at hi; exact hdt t ht i hi,
        by rw [hfeq]; exact hdf,
        ?_,
        Ndi, hWT_i_post.2.2.2, fun o ho j hj => ?_⟩
      · rw [hchain_eq]; intro ec' hec' o ho
        rcases hfo_post_cases ec' hec' o ho with ho_old | rfl
        · exact hdfo ec' hec' o ho_old
        · exact Or.inr (Or.inl rfl)
      · rw [nodeExtents_eq hTr_int.1 hcell_i] at hj
        exact hdj_m o ho j (hsub_int j hj).2
    unfold FrameWF; dsimp only
    rw [he_eq 8 (by omega) (by decide), he_eq 232 (by omega) (by decide),
        he_eq 88 (by omega) (by decide), he_eq 24 (by omega) (by decide),
        he_eq 40 (by omega) (by decide), he_eq 16 (by omega) (by decide),
        he_eq 32 (by omega) (by decide), he_eq 136 (by omega) (by decide),
        he_eq 168 (by omega) (by decide), he_eq 176 (by omega) (by decide),
        h88_eq 16 (by omega) (by omega), h88_eq 8 (by omega) (by omega),
        hframeLogs_eq ec hec,
        hglob_eq "scratch_ptr", hglob_eq "frame_mem_ptr", hglob_eq "heap_ptr", hglob_eq "evm_empty"]
    rw [he_eq 88 (by omega) (by decide)] at hlo_ok
    refine ⟨fun i hi => ⟨(c1 i hi).1, (wordsOK_congr_dom hdom_eq).2 (c1 i hi).2⟩,
      c2, (wordsOK_congr_dom hdom_eq).2 c3, c4, c5, c6, c7, c8, c9, c10, c11, c12,
      c13, (wordsOK_congr_dom hdom_eq).2 c14, ?_, hlo_ok, hmsg_ok⟩
    rw [hch_eq, List.mem_cons] at hec
    rcases hec with rfl | htail
    · exact Or.inl ⟨h216, h144⟩
    · rw [htail_rec_eq ec htail 216 (by omega), htail_rec_eq ec htail 144 (by omega),
          htail_frameRet_eq ec htail]
      rcases c15 with h0 | ⟨hin, hw⟩
      · exact Or.inl h0
      · exact Or.inr ⟨hin, (wordsOK_congr_dom hdom_eq).2 hw⟩
  · intro ec hec
    have hec_mem := List.mem_of_mem_tail hec
    unfold FrameRoom
    rw [(hrec_eq ec hec_mem).1 16 (by omega) (by decide),
        (hrec_eq ec hec_mem).1 232 (by omega) (by decide)]
    exact hFR_all ec hec
  · intro i hi
    have hi0 : (evmChain s)[i]'(by omega) ∈ evmChain s := List.getElem_mem _
    have hi1 : (evmChain s)[i + 1] ∈ evmChain s := List.getElem_mem _
    rw [(hrec_eq _ hi0).2.1 80 (by omega) (by omega),
        (hrec_eq _ hi0).2.1 72 (by omega) (by omega),
        (hrec_eq _ hi1).1 40 (by omega) (by decide)]
    exact hRW i hi
  · have htail_map_eq : chTail.map (frameObjects post) = chTail.map (frameObjects s) :=
      List.map_congr_left htail_fo_eq
    rw [hch_eq, List.map_cons, List.flatten_cons, htail_map_eq, List.pairwise_append]
    have hFO_pw' := hFO_pw
    rw [hch_eq, List.map_cons, List.flatten_cons, List.pairwise_append] at hFO_pw'
    refine ⟨?_, hFO_pw'.2.1, ?_⟩
    · obtain ⟨he_eq, _, _⟩ := hrec_eq (e0, c0) hhead_mem
      have hhead_pw := hpw_head_tail.1
      unfold frameObjects at hhead_pw ⊢
      rw [he_eq 8 (by omega) (by decide), he_eq 232 (by omega) (by decide),
          he_eq 24 (by omega) (by decide), he_eq 40 (by omega) (by decide),
          he_eq 88 (by omega) (by decide),
          hframeLogs_eq _ hhead_mem, hhead_frameRet, (hlogs_congr _ hhead_mem).1]
      change ((e0, 280) :: (c0, 104) :: (memW s (e0 + 8), 32 * memW s (e0 + 232)) ::
        (memW s (e0 + 24), memW s (e0 + 40)) :: (memW s (e0 + 88), 24) ::
        frameLogs s (e0, c0) :: (0, 0) :: frameLogObjects s (e0, c0)).Pairwise Disj
      have hp0 := List.pairwise_cons.1 hhead_pw
      have hp1 := List.pairwise_cons.1 hp0.2
      have hp2 := List.pairwise_cons.1 hp1.2
      have hp3 := List.pairwise_cons.1 hp2.2
      have hp4 := List.pairwise_cons.1 hp3.2
      have hp5 := List.pairwise_cons.1 hp4.2
      have hp6 := List.pairwise_cons.1 hp5.2
      have hd_z : ∀ x : Ivl, Disj x (0, 0) := fun _ => Or.inr (Or.inl rfl)
      have hz_d : ∀ x : Ivl, Disj (0, 0) x := fun _ => Or.inl rfl
      refine List.pairwise_cons.2 ⟨?_, List.pairwise_cons.2 ⟨?_, List.pairwise_cons.2 ⟨?_,
        List.pairwise_cons.2 ⟨?_, List.pairwise_cons.2 ⟨?_, List.pairwise_cons.2 ⟨?_,
          List.pairwise_cons.2 ⟨fun o _ => hz_d o, hp6.2⟩⟩⟩⟩⟩⟩⟩
      · intro o ho; simp only [List.mem_cons] at ho
        rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | ho_l
        · exact hp0.1 _ (by simp)
        · exact hp0.1 _ (by simp)
        · exact hp0.1 _ (by simp)
        · exact hp0.1 _ (by simp)
        · exact hp0.1 _ (by simp)
        · exact hd_z _
        · exact hp0.1 _ (by simp [ho_l])
      · intro o ho; simp only [List.mem_cons] at ho
        rcases ho with rfl | rfl | rfl | rfl | rfl | ho_l
        · exact hp1.1 _ (by simp)
        · exact hp1.1 _ (by simp)
        · exact hp1.1 _ (by simp)
        · exact hp1.1 _ (by simp)
        · exact hd_z _
        · exact hp1.1 _ (by simp [ho_l])
      · intro o ho; simp only [List.mem_cons] at ho
        rcases ho with rfl | rfl | rfl | rfl | ho_l
        · exact hp2.1 _ (by simp)
        · exact hp2.1 _ (by simp)
        · exact hp2.1 _ (by simp)
        · exact hd_z _
        · exact hp2.1 _ (by simp [ho_l])
      · intro o ho; simp only [List.mem_cons] at ho
        rcases ho with rfl | rfl | rfl | ho_l
        · exact hp3.1 _ (by simp)
        · exact hp3.1 _ (by simp)
        · exact hd_z _
        · exact hp3.1 _ (by simp [ho_l])
      · intro o ho; simp only [List.mem_cons] at ho
        rcases ho with rfl | rfl | ho_l
        · exact hp4.1 _ (by simp)
        · exact hd_z _
        · exact hp4.1 _ (by simp [ho_l])
      · intro o ho; simp only [List.mem_cons] at ho
        rcases ho with rfl | ho_l
        · exact hd_z _
        · exact hp5.1 _ (by simp [ho_l])
    · intro o1 ho1 o2 ho2
      rcases hfo_post_cases _ hhead_mem o1 ho1 with ho1_old | rfl
      · exact hFO_pw'.2.2 o1 ho1_old o2 ho2
      · exact Or.inl rfl
  · intro ec hec o ho
    rw [hfeq]
    rcases hfo_post_cases ec hec o ho with ho_old | rfl
    · exact ⟨fun t ht i hi => by rw [hfp_eq_all t ht] at hi; exact (hFO_disj ec hec o ho_old).1 t ht i hi,
        (hFO_disj ec hec o ho_old).2⟩
    · exact ⟨fun _ _ _ _ => Or.inl rfl, fun _ _ => Or.inl rfl⟩
  · refine ⟨Nd_at, hWT_post.2.2.2, fun o ho j hj => ?_⟩
    rw [nodeExtents_eq hTr_at.1 hcell] at hj
    obtain ⟨fo, hfo_map, ho_in⟩ := List.mem_flatten.1 ho
    obtain ⟨ec, hec, rfl⟩ := List.mem_map.1 hfo_map
    rcases hfo_post_cases ec hec o ho_in with ho_old | rfl
    · exact hAT_at o (List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨ec, hec, rfl⟩, ho_old⟩) j hj
    · exact Or.inl rfl
  · have hworldRefs_eq : worldTableRefs post S = worldTableRefs s S := by
      unfold worldTableRefs recordSlots
      rw [hglob_eq "ws", hglob_eq "bs", hglob_eq "ts",
          show globalTableRoots.map (globN post) = globalTableRoots.map (globN s) by
            simp only [globalTableRoots, List.map, hglob_eq],
          balRecords_eq hWT.1 hcell (hglob_eq "bal_accounts"),
          hglob_eq "journal_n", hglob_eq "journal"]
      have hws_sl : (if globN s "ws" = 0 then [] else wsTableSlots.map fun k => memW post (globN s "ws" + k)) =
          (if globN s "ws" = 0 then [] else wsTableSlots.map fun k => memW s (globN s "ws" + k)) := by
        split; · rfl
        rename_i hnz; apply List.map_congr_left; intro k hk
        exact memW_typedRec_eq hAs.2 hWT.2.2.1 hcell (sz := 40) (by decide) hnz
          (by simp only [wsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk; rcases hk with rfl | rfl <;> omega)
      have hbs_sl : (if globN s "bs" = 0 then [] else bsTableSlots.map fun k => memW post (globN s "bs" + k)) =
          (if globN s "bs" = 0 then [] else bsTableSlots.map fun k => memW s (globN s "bs" + k)) := by
        split; · rfl
        rename_i hnz; apply List.map_congr_left; intro k hk
        exact memW_typedRec_eq hAs.2 hWT.2.2.1 hcell (sz := 80) (by decide) hnz
          (by simp only [bsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk; rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
      have hts_sl : (if globN s "ts" = 0 then [] else tsTableSlots.map fun k => memW post (globN s "ts" + k)) =
          (if globN s "ts" = 0 then [] else tsTableSlots.map fun k => memW s (globN s "ts" + k)) := by
        split; · rfl
        rename_i hnz; apply List.map_congr_left; intro k hk
        exact memW_typedRec_eq hAs.2 hWT.2.2.1 hcell (sz := 72) (by decide) hnz
          (by simp only [tsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk; rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
      have hnest_bs : (if globN s "bs" ≠ 0 ∧ memW post (globN s "bs" + 32) ∈ S then htabValues post (memW post (globN s "bs" + 32)) else []) =
          (if globN s "bs" ≠ 0 ∧ memW s (globN s "bs" + 32) ∈ S then htabValues s (memW s (globN s "bs" + 32)) else []) := by
        by_cases hnz : globN s "bs" = 0
        · simp [hnz]
        · rw [memW_typedRec_eq hAs.2 hWT.2.2.1 hcell (sz := 80) (by decide) hnz (by omega)]
          by_cases hmS : memW s (globN s "bs" + 32) ∈ S
          · simp [hnz, hmS, htabValues_eq hcell hmS (hWT.1.2.1 _ hmS).1]
          · simp [hnz, hmS]
      have hnest_ts : (if globN s "ts" ≠ 0 ∧ memW post (globN s "ts" + 32) ∈ S then htabValues post (memW post (globN s "ts" + 32)) else []) =
          (if globN s "ts" ≠ 0 ∧ memW s (globN s "ts" + 32) ∈ S then htabValues s (memW s (globN s "ts" + 32)) else []) := by
        by_cases hnz : globN s "ts" = 0
        · simp [hnz]
        · rw [memW_typedRec_eq hAs.2 hWT.2.2.1 hcell (sz := 72) (by decide) hnz (by omega)]
          by_cases hmS : memW s (globN s "ts" + 32) ∈ S
          · simp [hnz, hmS, htabValues_eq hcell hmS (hWT.1.2.1 _ hmS).1]
          · simp [hnz, hmS]
      have hbal_fl : (balRecords s).flatMap (fun ad => [memW post ad, memW post (ad + 8)]) =
          (balRecords s).flatMap (fun ad => [memW s ad, memW s (ad + 8)]) := by
        apply List.flatMap_congr; intro ad had
        have had_mem := balRecord_ivl_mem had
        rcases fixedObject_le_2pow64 hAs.2 hWT.2.2.1 (bal_in_fixedObjects had_mem) with h0 | had_bnd
        · dsimp only at h0; omega
        · dsimp only at had_bnd
          have hwti_ad := mem_worldTypedIvls_bal (S := S) (Nd := Nd_at) had_mem
          rw [memW_eq_of_cellHits hcell (by omega) hwti_ad ⟨by dsimp only; omega, by dsimp only; omega⟩,
              memW_eq_of_cellHits hcell (by omega) hwti_ad ⟨by dsimp only; omega, by dsimp only; omega⟩]
      have hjrn_mp : (List.range (globN s "journal_n")).map (fun k => memW post (globN s "journal" + 32 * k)) =
          (List.range (globN s "journal_n")).map (fun k => memW s (globN s "journal" + 32 * k)) := by
        apply List.map_congr_left; intro k hk; rw [List.mem_range] at hk
        have hjc_le := hWT.2.1.1
        have hjc_ne : globN s "journal_cap" ≠ 0 := by omega
        rcases hWT.2.1.2.2.1 with h0 | ⟨hal, _⟩
        · exact absurd h0 hjc_ne
        · have hbnd := allocated_le_2pow64 hAs.2 hal; dsimp only at hbnd
          have hkle : 32 * k + 8 ≤ 32 * globN s "journal_cap" := by omega
          exact memW_eq_of_cellHits hcell (by omega) (mem_worldTypedIvls_journal (S := S) (Nd := Nd_at) hjc_ne)
            ⟨by dsimp only; omega, by dsimp only; omega⟩
      dsimp only
      rw [hglob_eq "bs", hglob_eq "ts", hws_sl, hbs_sl, hts_sl, hnest_bs, hnest_ts, hbal_fl, hjrn_mp]
    have hdelEx_iff : ∀ i t, DelExclusive post S (evmChain s) i t ↔ DelExclusive s S (evmChain s) i t := by
      intro i t; unfold DelExclusive; rw [hworldRefs_eq]
      refine and_congr Iff.rfl (forall_congr' fun j => forall_congr' fun hj =>
        forall_congr' fun k => imp_congr_right fun hk => ?_)
      have hj_mem : (evmChain s)[j] ∈ evmChain s := List.getElem_mem _
      have hk_ok : k + 8 ≤ 280 ∧ k ∉ ([144, 152, 216] : List Nat) := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl <;> exact ⟨by omega, by decide⟩
      rw [(hrec_eq _ hj_mem).1 k hk_ok.1 hk_ok.2]
    intro i hi
    have hi_mem : (evmChain s)[i]'(by omega) ∈ evmChain s := List.getElem_mem _
    have hm_eq := (hrec_eq _ hi_mem).2.1 48 (by omega) (by omega)
    have hmm_eq := (hrec_eq _ hi_mem).2.1 56 (by omega) (by omega)
    have he24_eq := (hrec_eq _ hi_mem).1 24 (by omega) (by decide)
    have htake_eq : ((evmChain s).take (i + 1)).map (fun ec => memW post (ec.1 + 136)) =
        ((evmChain s).take (i + 1)).map (fun ec => memW s (ec.1 + 136)) := by
      apply List.map_congr_left; intro ec hec
      exact (hrec_eq ec (List.mem_of_mem_take hec)).1 136 (by omega) (by decide)
    have hM := hMarks i hi; dsimp only at hM ⊢
    rw [hm_eq, hmm_eq, he24_eq, hframeScratch_eq _ hi_mem, hfeq, htake_eq]
    obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9⟩ := hM
    refine ⟨m1, m2, m3, m4, ?_, m6, m7, ?_, m9⟩
    · intro j hj hij
      have hj_mem : (evmChain s)[j] ∈ evmChain s := List.getElem_mem _
      rw [hframeScratch_eq _ hj_mem, hfo_idx3_eq _ hj_mem, hframeLogs_eq _ hj_mem,
          (hrec_eq _ hj_mem).1 112 (by omega) (by decide)]
      exact m5 j hj hij
    · intro t ht
      rw [hfp_eq_all t ht, hdelEx_iff i t]; exact m8 t ht
  · have hcg : ∀ g ∈ coreWorldGlobals, globN post g = globN s g := fun g _ => hglob_eq g
    rw [worldRoleSlots_eq hAs.2 hWT.1 hWT.2.2.1 hcell hcg,
        hframeRoleSlots_eq,
        journalRoleSlots_eq hAs.2 hWT.2.1 hWT.2.2.1 hcell hcg]
    unfold RolesOK at hRoles ⊢
    refine ⟨fun a ha => ?_, hRoles.2⟩
    obtain ⟨haS, hkl⟩ := hRoles.1 a ha
    have htb := ((hWT.1.2.1 a.1 haS).1.1 (a.1, 88) (by simp [htabFootprint])).1
    rw [htab_hdr_eq hcell haS htb 0 (by omega)]; exact ⟨haS, hkl⟩
  · have hsum_eq : ((evmChain s).map fun ec => memW post (ec.1 + 64) + memW post (ec.1 + 192)).sum =
        ((evmChain s).map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)).sum := by
      congr 1; apply List.map_congr_left; intro ec hec
      rw [(hrec_eq ec hec).1 64 (by omega) (by decide),
          (hrec_eq ec hec).1 192 (by omega) (by decide)]
    rw [hsum_eq]; exact hGas

theorem epsA_set_retdata_empty :
    EvmPreservingSpecA
      (fun s => s.locals.lookup (ofString "n") = some (.val (.word 0#64)))
      (fun s _ post =>
        post.globals = s.globals ∧
        evmR post = evmR s ∧
        post.be = s.be ∧
        ∀ x : BitVec 64,
          (∀ off ∈ ([144, 152, 216] : List Nat), x ≠ BitVec.ofNat 64 (globN s "ev" + off)) →
          post.memory x = s.memory x)
      (ofString "set_retdata") := by
  refine ⟨_, _, _, lookup_set_retdata, ?_⟩
  intro F s _ hInv hWF hn0 _ _
  obtain ⟨hev_pos, _, hb_ev⟩ := evmInv_head_ev_bounds_g10 hInv
  obtain ⟨evw, hevw_lk, hevw_nat⟩ := global_word_of_pos s "ev" hev_pos
  obtain ⟨w_emp, hw_emp⟩ := hInv.1.2.2.2.2.2.2.2.2.2 "evm_empty" (by decide)
  have hw_emp_nat : w_emp.toNat = globN s "evm_empty" := by
    unfold GlobalWord at hw_emp
    simp [globN, hw_emp]
  have herr_triv : ∀ {P1 P2 : Prop} {r : PanSemResultExact 64}, r = .error →
      (∀ v, (some r : Option (PanSemResultExact 64)) = some (.returned v) → P1) ∧
      (IsEvmErr (some r) → P2) := by
    intro _ _ r hr; subst hr; constructor
    · intro _ h; cases h
    · rintro ⟨_, h⟩; cases h
  have hb : sourceFnBody Guest.Software.guestFn_set_retdata =
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
        (extractFn Guest.Software.guestFn_set_retdata).body := rfl
  dsimp only
  rw [hb]
  dsimp only [extractFn, Guest.Software.guestFn_set_retdata,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    List.map, Option.map]
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
  have hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .equal (.var .local (ofString "n")) (.const 0#64)) =
      some (.val (.word 1#64)) := by
    simp [evalHOLExact, hn0, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  have h10 : ¬ ((1#64 : BitVec 64) = 0) := by decide
  rw [hcond]; simp only [h10, ↓reduceIte]
  rw [evaluateHOLFiniteState_seq_line780]
  rcases hst1 : evaluateHOLFiniteState s
      (.store (.op .add [.var .global (ofString "ev"), .const 144#64])
        (.var .global (ofString "evm_empty"))) with ⟨r1, s1⟩
  cases r1 with
  | some res1 =>
    dsimp only
    exact herr_triv (store_some_eq_error_g10 hst1)
  | none =>
    dsimp only
    obtain ⟨w1, hw1_ev, hs1_eq⟩ := R14Shards.OpHandlersA.store_global_off_word
      (t := s) (post := s1) (gname := "ev") (gbase := globN s "ev") (off := 144)
      hevw_lk hevw_nat (by omega)
      (fun v0 hv0 => by
        change s.globals.lookup (ofString "evm_empty") = some v0 at hv0
        rw [hw_emp] at hv0; injection hv0 with hv'; exact ⟨w_emp, hv'.symm⟩) hst1
    have hw1_eq : w1 = w_emp := by
      change s.globals.lookup (ofString "evm_empty") = some (.val (.word w1)) at hw1_ev
      rw [hw_emp] at hw1_ev
      injection hw1_ev with h1; injection h1 with h2; injection h2 with h3; exact h3.symm
    rw [hw1_eq] at hs1_eq
    rw [evaluateHOLFiniteState_seq_line780]
    rcases hst2 : evaluateHOLFiniteState s1
        (.store (.op .add [.var .global (ofString "ev"), .const 152#64]) (.const 0#64)) with ⟨r2, s2⟩
    cases r2 with
    | some res2 =>
      dsimp only
      exact herr_triv (store_some_eq_error_g10 hst2)
    | none =>
      dsimp only
      obtain ⟨w2, hw2_ev, hs2_eq⟩ := R14Shards.OpHandlersA.store_global_off_word
        (t := s1) (post := s2) (gname := "ev") (gbase := globN s "ev") (off := 152)
        (by rw [hs1_eq]; exact hevw_lk) hevw_nat (by omega)
        (fun v0 hv0 => by simp [evalHOLExact] at hv0; exact ⟨0#64, hv0.symm⟩) hst2
      have hw2_eq : w2 = 0#64 := by
        simp [evalHOLExact] at hw2_ev; exact hw2_ev.symm
      subst hw2_eq
      rw [evaluateHOLFiniteState_seq_line780]
      rcases hst3 : evaluateHOLFiniteState s2
          (.store (.op .add [.var .global (ofString "ev"), .const 216#64]) (.const 0#64)) with ⟨r3, s3⟩
      cases r3 with
      | some res3 =>
        dsimp only
        exact herr_triv (store_some_eq_error_g10 hst3)
      | none =>
        dsimp only
        obtain ⟨w3, hw3_ev, hs3_eq⟩ := R14Shards.OpHandlersA.store_global_off_word
          (t := s2) (post := s3) (gname := "ev") (gbase := globN s "ev") (off := 216)
          (by rw [hs2_eq, hs1_eq]; exact hevw_lk) hevw_nat (by omega)
          (fun v0 hv0 => by simp [evalHOLExact] at hv0; exact ⟨0#64, hv0.symm⟩) hst3
        have hw3_eq : w3 = 0#64 := by
          simp [evalHOLExact] at hw3_ev; exact hw3_ev.symm
        subst hw3_eq
        rw [evaluateHOLFiniteState_return]
        dsimp only [evalHOLExact]
        have hsz0 : sizeOfShapeWithContextHOL s3.structs
            (shapeOfHOLExact (.val (.word 0#64))) ≤ 32 := by
          simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
        rw [if_pos hsz0]
        dsimp only
        let post := emptyLocalsHOLFinite s3
        have hGp : GuestInv post := guestInv_congr (s := s)
          (by simp [post, emptyLocalsHOLFinite, hs3_eq, hs2_eq, hs1_eq])
          (by simp [post, emptyLocalsHOLFinite, hs3_eq, hs2_eq, hs1_eq])
          (by simp [post, emptyLocalsHOLFinite, hs3_eq, hs2_eq, hs1_eq])
          (by simp [post, emptyLocalsHOLFinite, hs3_eq, hs2_eq, hs1_eq]) hInv.1.1
        have hglob_p : post.globals = s.globals := by
          simp [post, emptyLocalsHOLFinite, hs3_eq, hs2_eq, hs1_eq]
        have hbe_p : post.be = s.be := by
          simp [post, emptyLocalsHOLFinite, hs3_eq, hs2_eq, hs1_eq]
        have hmem_out : ∀ x : BitVec 64,
            (∀ off ∈ ([144, 152, 216] : List Nat), x ≠ BitVec.ofNat 64 (globN s "ev" + off)) →
            post.memory x = s.memory x := by
          intro x hx
          have hn144 := hx 144 (by simp)
          have hn152 := hx 152 (by simp)
          have hn216 := hx 216 (by simp)
          change s3.memory x = s.memory x
          rw [hs3_eq, hs2_eq, hs1_eq]
          simp [R14Shards.OpHandlersA.updW, hn216, hn152, hn144]
        have h216_p : memW post (globN s "ev" + 216) = 0 := by
          change memW s3 (globN s "ev" + 216) = 0
          rw [hs3_eq, R14Shards.OpHandlersA.memW_updW_same s2 (globN s "ev" + 216) 0#64]
          rfl
        have h144_p : memW post (globN s "ev" + 144) = globN s "evm_empty" := by
          change memW s3 (globN s "ev" + 144) = globN s "evm_empty"
          rw [hs3_eq,
              R14Shards.OpHandlersA.memW_updW_ne s2 (globN s "ev" + 216) (globN s "ev" + 144) 0#64 (by omega) (by omega) (by omega),
              hs2_eq,
              R14Shards.OpHandlersA.memW_updW_ne s1 (globN s "ev" + 152) (globN s "ev" + 144) 0#64 (by omega) (by omega) (by omega),
              hs1_eq,
              R14Shards.OpHandlersA.memW_updW_same s (globN s "ev" + 144) w_emp]
          exact hw_emp_nat
        obtain ⟨hInv_p, hch_p, hR_p⟩ :=
          evmInv_of_head_retdata_reset hInv hGp hglob_p hbe_p hmem_out h216_p h144_p
        have hWF_p : Group10.HeadMemChainWF post := by
          refine headMemChainWF_of_headSafe hInv hWF hch_p
            (congrFun (globN_congr hglob_p) "ev") (congrFun (globN_congr hglob_p) "frame_mem_ptr") ?_
          have hoff_safe : ∀ off ∈ ([144, 152, 216] : List Nat),
              off < 280 ∧ off ≠ 24 ∧ off ≠ 32 ∧ off ≠ 40 := by decide
          intro x hx
          apply hmem_out x
          intro off hoff rfl
          have hp := hoff_safe off hoff
          have htn : (BitVec.ofNat 64 (globN s "ev" + off)).toNat = globN s "ev" + off :=
            Nat.mod_eq_of_lt (by omega)
          exact hx (Or.inl ⟨off, htn, hp.1, hp.2.1, hp.2.2.1, hp.2.2.2⟩)
        exact ⟨fun _ _ => ⟨⟨hInv_p, hWF_p⟩, hch_p, le_of_eq hR_p, hglob_p, hR_p, hbe_p, hmem_out⟩,
          by rintro ⟨_, h⟩; cases h⟩

theorem HandlerRunA.seq_set_retdata_empty {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {P Q : PanSemStateFiniteExact 64 F → Prop} {charged : Bool}
    {p_exp : ExpHOL 64} {cont : ProgHOL 64}
    (hstep : ∀ t cpost : PanSemStateFiniteExact 64 F,
      EvmInv t → Group10.HeadMemChainWF t → P t →
      EvmInv cpost → Group10.HeadMemChainWF cpost →
      evmChain cpost = evmChain t →
      cpost.globals = t.globals →
      evmR cpost = evmR t →
      cpost.be = t.be →
      (∀ x : BitVec 64,
        (∀ off ∈ ([144, 152, 216] : List Nat), x ≠ BitVec.ofNat 64 (globN t "ev" + off)) →
        cpost.memory x = t.memory x) →
      Q { cpost with locals := t.locals })
    (hcont : HandlerRunA s0 Q charged cont) :
    HandlerRunA s0 P charged
      (.seq (.call (some (none, none)) (ofString "set_retdata") [p_exp, .const 0#64]) cont) := by
  refine HandlerRunA.seq_call epsA_set_retdata_empty ?_ ?_ hcont
  · intro t values body' callee ret' hc _ _ _ hargs hl
    rw [hc] at hl
    obtain ⟨_, _, w1, w2, hvals, _, hn_lk⟩ :=
      R14Shards.OpHandlersA.two_word_arg_lookup (by decide) lookup_set_retdata hl
    rw [evalListHOLFinite_eq_toExact] at hargs
    rcases hpv : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) p_exp with _ | pv
    · simp [evalListHOLExact, hpv] at hargs
    · simp [evalListHOLExact, hpv, evalHOLExact] at hargs
      have hw2 : w2 = 0#64 := by
        rw [← hargs] at hvals
        injection hvals with _ htl
        injection htl with hh2 _
        injection hh2 with hh2'
        injection hh2' with hh2''
        exact hh2''.symm
      subst hw2
      simpa [callEntryStateHOLFinite] using hn_lk
  · intro t _ _ callee _ _ cpost hi hw hp _ _ hi_cp hw_cp hch_cp ⟨hg_cp, hR_cp, hbe_cp, hmem_cp⟩
    have hc_ce := evm_congr (s := t) (t := callEntryStateHOLFinite t callee) rfl rfl
    have hch_ce : evmChain (callEntryStateHOLFinite t callee) = evmChain t := evmChain_congr rfl rfl
    exact hstep t cpost hi hw hp hi_cp hw_cp (hch_cp.trans hch_ce)
      hg_cp (hR_cp.trans hc_ce.2.1) hbe_cp hmem_cp

private theorem evaluate_call_trap_with_no_none_g10 {F : Type}
    (state : PanSemStateFiniteExact 64 F) (codeVal : BitVec 64)
    (hcode : state.code = originalRuntimeCode) :
    (evaluateHOLFiniteState state
      (.call (some (none, none)) (ofString "trap_with") [.const codeVal])).1 ≠ none := by
  rw [evaluateHOLFiniteState_call]
  have hargs : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [.const codeVal] =
      some [.val (.word codeVal)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact]
  have hlookup := pan_one_word_lookup state.code.lookup (ofString "trap_with") (ofString "code")
    (sourceFnBody Guest.Software.guestFn_trap_with) codeVal (by rw [hcode]; exact lookup_trap_with)
  rw [hargs]
  dsimp only
  rw [hlookup]
  dsimp only
  split
  · simp
  · have hout := evaluate_trap_with_body_outcomes
      (callEntryStateHOLFinite state (HolFiniteMapExact.empty.update (ofString "code", .val (.word codeVal))))
    rcases hbody : evaluateHOLFiniteState
      (callEntryStateHOLFinite state (HolFiniteMapExact.empty.update (ofString "code", .val (.word codeVal))))
      (sourceFnBody Guest.Software.guestFn_trap_with) with ⟨res, st⟩
    rw [hbody] at hout
    cases res with
    | none => exact absurd rfl hout.1
    | some r =>
      cases r with
      | returned v => exact absurd rfl (hout.2.1 v)
      | «break» | «continue» | error | timeOut | finalFfi _ | exception _ _ => simp

private theorem evaluate_call_trap_with_no_return_g10 {F : Type}
    (state : PanSemStateFiniteExact 64 F) (codeVal : BitVec 64) (w : ValueHOL 64)
    (hcode : state.code = originalRuntimeCode) :
    (evaluateHOLFiniteState state
      (.call (some (none, none)) (ofString "trap_with") [.const codeVal])).1 ≠ some (.returned w) := by
  rw [evaluateHOLFiniteState_call]
  have hargs : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [.const codeVal] =
      some [.val (.word codeVal)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact]
  have hlookup := pan_one_word_lookup state.code.lookup (ofString "trap_with") (ofString "code")
    (sourceFnBody Guest.Software.guestFn_trap_with) codeVal (by rw [hcode]; exact lookup_trap_with)
  rw [hargs]
  dsimp only
  rw [hlookup]
  dsimp only
  split
  · simp
  · have hout := evaluate_trap_with_body_outcomes
      (callEntryStateHOLFinite state (HolFiniteMapExact.empty.update (ofString "code", .val (.word codeVal))))
    rcases hbody : evaluateHOLFiniteState
      (callEntryStateHOLFinite state (HolFiniteMapExact.empty.update (ofString "code", .val (.word codeVal))))
      (sourceFnBody Guest.Software.guestFn_trap_with) with ⟨res, st⟩
    rw [hbody] at hout
    cases res with
    | none => exact absurd rfl hout.1
    | some r =>
      cases r with
      | returned v => exact absurd rfl (hout.2.1 v)
      | «break» | «continue» | error | timeOut | finalFfi _ | exception _ _ => simp

theorem lookup_memzero_g10 :
    originalRuntimeCode.lookup (ofString "memzero") =
      some ([(ofString "dst", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_memzero, .one) :=
  lookup_of_guestAst_getElem 17 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_memzero) rfl

private theorem bv_add_small_g10 (a b : BitVec 64) (h : a.toNat + b.toNat < 2 ^ 64) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt h

private theorem seq_none_or_err_bre_g10 {F : Type} {s : PanSemStateFiniteExact 64 F}
    {c1 c2 : ProgHOL 64} {Rl : List Ivl}
    {Q : PanSemStateFiniteExact 64 F → Prop}
    (hc1 : (∀ m, evaluateHOLFiniteState s c1 = (none, m) → ByteRegionEffect s m Rl) ∧
           (∀ r, r ≠ none → (evaluateHOLFiniteState s c1).1 = r → r = some .error))
    (hc2 : ∀ m, evaluateHOLFiniteState s c1 = (none, m) → ByteRegionEffect s m Rl →
           (∀ p, evaluateHOLFiniteState m c2 = (none, p) → Q p ∧ ByteRegionEffect m p Rl) ∧
           (∀ r, r ≠ none → (evaluateHOLFiniteState m c2).1 = r → r = some .error)) :
    (∀ p, evaluateHOLFiniteState s (.seq c1 c2) = (none, p) → Q p ∧ ByteRegionEffect s p Rl) ∧
    (∀ r, r ≠ none → (evaluateHOLFiniteState s (.seq c1 c2)).1 = r → r = some .error) := by
  rw [evaluateHOLFiniteState_seq_line780]
  rcases h1 : evaluateHOLFiniteState s c1 with ⟨r1, m⟩
  cases r1 with
  | none =>
    dsimp only
    have he1 := hc1.1 m h1
    obtain ⟨h2n, h2e⟩ := hc2 m h1 he1
    exact ⟨fun p hp => ⟨(h2n p hp).1, he1.trans (h2n p hp).2⟩, h2e⟩
  | some r =>
    dsimp only
    have herr : some r = some .error := hc1.2 (some r) (by simp) (by rw [h1])
    exact ⟨fun _ hp => by simp at hp, fun r' _ hr' => by rw [← hr', herr]⟩

private theorem memzero_word_store_step_g10 {F : Type}
    {st : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    {dst iv : BitVec 64} {addrExp : ExpHOL 64} {c : Nat}
    (hma : st.memaddrs = ordinaryDomain)
    (hsub : dst.toNat + iv.toNat + c + 8 ≤ 33806089704 →
      ∃ ivl ∈ Rl, ivl.1 ≤ dst.toNat + (iv.toNat + c) ∧ dst.toNat + (iv.toNat + c) + 8 ≤ ivl.1 + ivl.2)
    (haddr : @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a)) addrExp =
      some (.val (.word (dst + (iv + BitVec.ofNat 64 c)))))
    (hprev_dom : (iv.toNat + c > 0 → dst.toNat + iv.toNat + c ≤ 33806089704) ∧ iv.toNat + c < 2 ^ 64) :
    (∀ sm, evaluateHOLFiniteState st (.store addrExp (.const 0)) = (none, sm) →
      ByteRegionEffect st sm Rl ∧ sm.locals = st.locals ∧
      dst.toNat + iv.toNat + c + 8 ≤ 33806089704) ∧
    (∀ r, r ≠ none → (evaluateHOLFiniteState st (.store addrExp (.const 0))).1 = r → r = some .error) := by
  have hsum_ivc : (iv + BitVec.ofNat 64 c).toNat = iv.toNat + c := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    have hc_mod : c % 2 ^ 64 = c := Nat.mod_eq_of_lt (by omega)
    rw [hc_mod]
    exact Nat.mod_eq_of_lt hprev_dom.2
  have haddr_nat : (dst + (iv + BitVec.ofNat 64 c)).toNat = dst.toNat + (iv.toNat + c) := by
    by_cases hz : iv.toNat + c = 0
    · have h0 : iv + BitVec.ofNat 64 c = 0 := BitVec.eq_of_toNat_eq (by rw [hsum_ivc, hz]; rfl)
      have hd0 : dst + (0 : BitVec 64) = dst := BitVec.add_zero dst
      rw [h0, hd0, hz, Nat.add_zero]
    · have hle := hprev_dom.1 (by omega)
      rw [bv_add_small_g10 dst (iv + BitVec.ofNat 64 c) (by rw [hsum_ivc]; omega), hsum_ivc]
  refine ⟨fun sm hsm => ?_, ?_⟩
  · have hsm' := hsm
    rw [evaluateHOLFiniteState_store, haddr] at hsm'
    dsimp only [evalHOLExact, flattenHOL, panMemStoresHOL, panMemStoreHOL] at hsm'
    by_cases hdom : st.memaddrs (dst + (iv + BitVec.ofNat 64 c))
    · have hd := M11.word_dom_lt_heapEnd hma _ hdom
      rw [R11Shards.heapEnd_val, haddr_nat] at hd
      have hbnd8 : dst.toNat + iv.toNat + c + 8 ≤ 33806089704 := by omega
      obtain ⟨heff, hloc⟩ := ByteRegionEffect.of_store_word hma hsm
        (fun v hv => by
          simp only [evalHOLExact] at hv
          injection hv with hv'
          exact ⟨0, hv'.symm⟩)
        (fun addr ha _ => by
          rw [haddr] at ha; injection ha with h1; injection h1 with h2; injection h2 with h3; subst h3
          rw [haddr_nat]
          exact hsub hbnd8)
      exact ⟨heff, hloc, hbnd8⟩
    · unfold flattenHOL panMemStoresHOL panMemStoreHOL at hsm'
      simp [evalHOLExact, hdom] at hsm'
  · intro r hrne hreq
    rw [evaluateHOLFiniteState_store] at hreq
    split at hreq
    · split at hreq
      · split at hreq
        · simp at hreq; exact absurd hreq.symm hrne
        · exact hreq.symm
      · exact hreq.symm
    · exact hreq.symm

private theorem memzero_byte_store_step_g10 {F : Type}
    {st : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    {dst iv : BitVec 64} {addrExp : ExpHOL 64} {c : Nat}
    (hma : st.memaddrs = ordinaryDomain)
    (hsub : dst.toNat + iv.toNat + c + 1 ≤ 33806089704 →
      ∃ ivl ∈ Rl, ivl.1 ≤ dst.toNat + (iv.toNat + c) ∧ dst.toNat + (iv.toNat + c) < ivl.1 + ivl.2)
    (haddr : @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a)) addrExp =
      some (.val (.word (dst + (iv + BitVec.ofNat 64 c)))))
    (hprev_dom : (iv.toNat + c > 0 → dst.toNat + iv.toNat + c ≤ 33806089704) ∧ iv.toNat + c < 2 ^ 64) :
    (∀ sm, evaluateHOLFiniteState st (.storeByte addrExp (.const 0)) = (none, sm) →
      ByteRegionEffect st sm Rl ∧ sm.locals = st.locals ∧
      dst.toNat + iv.toNat + c + 1 ≤ 33806089704) ∧
    (∀ r, r ≠ none → (evaluateHOLFiniteState st (.storeByte addrExp (.const 0))).1 = r → r = some .error) := by
  have hsum_ivc : (iv + BitVec.ofNat 64 c).toNat = iv.toNat + c := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    have hc_mod : c % 2 ^ 64 = c := Nat.mod_eq_of_lt (by omega)
    rw [hc_mod]
    exact Nat.mod_eq_of_lt hprev_dom.2
  have haddr_nat : (dst + (iv + BitVec.ofNat 64 c)).toNat = dst.toNat + (iv.toNat + c) := by
    by_cases hz : iv.toNat + c = 0
    · have h0 : iv + BitVec.ofNat 64 c = 0 := BitVec.eq_of_toNat_eq (by rw [hsum_ivc, hz]; rfl)
      have hd0 : dst + (0 : BitVec 64) = dst := BitVec.add_zero dst
      rw [h0, hd0, hz, Nat.add_zero]
    · have hle := hprev_dom.1 (by omega)
      rw [bv_add_small_g10 dst (iv + BitVec.ofNat 64 c) (by rw [hsum_ivc]; omega), hsum_ivc]
  refine ⟨fun sm hsm => ?_, ?_⟩
  · have hsm' := hsm
    rw [evaluateHOLFiniteState_storeByte, haddr] at hsm'
    dsimp only [evalHOLExact] at hsm'
    split at hsm'
    · rename_i m' hst
      unfold panMemStoreByteWord8HOL at hst
      dsimp only at hst
      cases hm : st.memory (panByteAlignHOL (dst + (iv + BitVec.ofNat 64 c))) with
      | word cell =>
        by_cases hdom : st.memaddrs (panByteAlignHOL (dst + (iv + BitVec.ofNat 64 c)))
        · have hd := (M11.byteAlign_lt_heapEnd hma _ hdom).2
          rw [R11Shards.heapEnd_val, haddr_nat] at hd
          have hbnd1 : dst.toNat + iv.toNat + c + 1 ≤ 33806089704 := by omega
          obtain ⟨heff, hloc⟩ := ByteRegionEffect.of_storeByte hsm (Rl := Rl) (fun addr ha _ => by
            rw [haddr] at ha; injection ha with h1; injection h1 with h2; injection h2 with h3; subst h3
            rw [haddr_nat]
            exact hsub hbnd1)
          exact ⟨heff, hloc, hbnd1⟩
        · simp [hm, hdom] at hst
    · simp at hsm'
  · intro r hrne hreq
    rw [evaluateHOLFiniteState_storeByte] at hreq
    split at hreq
    · split at hreq
      · split at hreq
        · simp at hreq; exact absurd hreq.symm hrne
        · exact hreq.symm
      · exact hreq.symm
    · exact hreq.symm

private def MemzeroBreInvG10 {F : Type} (dst n : BitVec 64)
    (t : PanSemStateFiniteExact 64 F) : Prop :=
  t.memaddrs = ordinaryDomain ∧
  t.locals.lookup (ofString "dst") = some (.val (.word dst)) ∧
  t.locals.lookup (ofString "n") = some (.val (.word n)) ∧
  ∃ iv : BitVec 64,
    t.locals.lookup (ofString "i") = some (.val (.word iv)) ∧
    iv.toNat ≤ n.toNat ∧
    iv.toNat ≤ 33806089704 ∧
    (iv.toNat > 0 → dst.toNat + iv.toNat ≤ 33806089704)

private theorem memzero_loop_runner_g10 {F : Type}
    (Rl : List Ivl) (dst n : BitVec 64) (cond : ExpHOL 64) (body : ProgHOL 64)
    (hstep : ∀ (s : PanSemStateFiniteExact 64 F),
      MemzeroBreInvG10 dst n s →
      ∃ cv : BitVec 64,
        @evalHOLFinite 64 F _ s (fun a => Classical.propDecidable (s.memaddrs a)) cond =
          some (.val (.word cv)) ∧
        (cv ≠ 0 →
          (∀ sb, evaluateHOLFiniteState (decClockHOLFinite s) body = (none, sb) →
            MemzeroBreInvG10 dst n sb ∧
            ByteRegionEffect (decClockHOLFinite s) sb Rl) ∧
          (∀ r, r ≠ none → (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = r →
            r = some .error)))
    (s0 : PanSemStateFiniteExact 64 F)
    (hinv : MemzeroBreInvG10 dst n s0)
    (hnt : (evaluateHOLFiniteState s0 (.while cond body)).1 ≠ some .timeOut) :
    ((evaluateHOLFiniteState s0 (.while cond body)).1 = none →
      MemzeroBreInvG10 dst n (evaluateHOLFiniteState s0 (.while cond body)).2 ∧
      ByteRegionEffect s0 (evaluateHOLFiniteState s0 (.while cond body)).2 Rl) ∧
    ((evaluateHOLFiniteState s0 (.while cond body)).1 ≠ none →
      (evaluateHOLFiniteState s0 (.while cond body)).1 = some .error) := by
  suffices hmain : ∀ (k : Nat) (s : PanSemStateFiniteExact 64 F), s.clock = k →
      MemzeroBreInvG10 dst n s →
      (evaluateHOLFiniteState s (.while cond body)).1 ≠ some .timeOut →
      ((evaluateHOLFiniteState s (.while cond body)).1 = none →
        MemzeroBreInvG10 dst n (evaluateHOLFiniteState s (.while cond body)).2 ∧
        ByteRegionEffect s (evaluateHOLFiniteState s (.while cond body)).2 Rl) ∧
      ((evaluateHOLFiniteState s (.while cond body)).1 ≠ none →
        (evaluateHOLFiniteState s (.while cond body)).1 = some .error) by
    exact hmain s0.clock s0 rfl hinv hnt
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro s hclk hPs hnt_s
    obtain ⟨cv, hc, hbody_step⟩ := hstep s hPs
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at hnt_s ⊢
    simp only [hc] at hnt_s ⊢
    by_cases hcv : cv = 0
    · subst hcv
      have h00 : ¬ ((0 : BitVec 64) ≠ 0) := by decide
      rw [if_neg h00]
      exact ⟨fun _ => ⟨hPs, ByteRegionEffect.refl s Rl⟩, fun h => False.elim (h rfl)⟩
    · rw [if_pos hcv] at hnt_s ⊢
      by_cases hk0 : s.clock = 0
      · simp [hk0] at hnt_s
      · rw [if_neg hk0] at hnt_s ⊢
        obtain ⟨hb_none, hb_err⟩ := hbody_step hcv
        have heff_dec : ByteRegionEffect s (decClockHOLFinite s) Rl :=
          ByteRegionEffect.refl s Rl |>.with_locals_clock s.locals (s.clock - 1)
        have hb_clk := Flapjack.evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
        have hd_clk : (decClockHOLFinite s).clock < k := by
          simp [decClockHOLFinite, hclk]; omega
        rcases hbo : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨rb, sb⟩
        simp only [hbo] at hnt_s hb_clk ⊢
        cases rb with
        | none =>
          dsimp only at hnt_s hb_clk ⊢
          obtain ⟨hPsb, heff_b⟩ := hb_none sb hbo
          have jih := ih sb.clock (lt_of_le_of_lt hb_clk hd_clk) sb rfl hPsb hnt_s
          exact ⟨fun hn => ⟨(jih.1 hn).1, (heff_dec.trans heff_b).trans (jih.1 hn).2⟩, jih.2⟩
        | some r =>
          have herr := hb_err (some r) (by simp) (by rw [hbo])
          injection herr with hr; subst hr
          exact ⟨fun h => by simp at h, fun _ => rfl⟩

private theorem eval_add2_di_g10 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (d iv : BitVec 64)
    (hd : s.locals.lookup (ofString "dst") = some (.val (.word d)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iv))) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) =
      some (.val (.word (d + (iv + BitVec.ofNat 64 0)))) := by
  simp only [evalHOLExact, evalListHOLExact, hd, hi, wordOpHOL, wordOp, valueIsWord, valueWord,
    List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr]
  rfl

private theorem eval_add3_dic_g10 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (d iv : BitVec 64) (c : Nat)
    (hd : s.locals.lookup (ofString "dst") = some (.val (.word d)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iv))) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const (BitVec.ofNat 64 c)]) =
      some (.val (.word (d + (iv + BitVec.ofNat 64 c)))) := by
  simp only [evalHOLExact, evalListHOLExact, hd, hi, wordOpHOL, wordOp, valueIsWord, valueWord,
    List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr]
  congr 3
  have hz : BitVec.ofNat 64 c + (0 : BitVec 64) = BitVec.ofNat 64 c := BitVec.add_zero _
  exact congrArg (fun x => d + (iv + x)) hz

private theorem assign_i_memzero_step_g10 {F : Type} (st : PanSemStateFiniteExact 64 F)
    (dst iv n : BitVec 64) (step : Nat) (Rl : List Ivl)
    (hma : st.memaddrs = ordinaryDomain)
    (hdst : st.locals.lookup (ofString "dst") = some (.val (.word dst)))
    (hn : st.locals.lookup (ofString "n") = some (.val (.word n)))
    (hi : st.locals.lookup (ofString "i") = some (.val (.word iv)))
    (_hstep_pos : 0 < step)
    (hle : iv.toNat + step ≤ n.toNat)
    (hdom : dst.toNat + iv.toNat + step ≤ 33806089704) :
    (∀ p, evaluateHOLFiniteState st
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 step)])) = (none, p) →
      MemzeroBreInvG10 dst n p ∧ ByteRegionEffect st p Rl) ∧
    (∀ r, r ≠ none →
      (evaluateHOLFiniteState st
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 step)]))).1 = r →
      r = some .error) := by
  have hev : @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a))
      (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 step)]) =
      some (.val (.word (iv + BitVec.ofNat 64 step))) := by
    simp only [evalHOLExact, evalListHOLExact, hi, wordOpHOL, wordOp, valueIsWord, valueWord,
      List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr]
    congr 3
    have hz : BitVec.ofNat 64 step + (0 : BitVec 64) = BitVec.ofNat 64 step := BitVec.add_zero _
    exact congrArg (fun x => iv + x) hz
  have hvld : isValidValueHOLFinite st .local (ofString "i") (.val (.word (iv + BitVec.ofNat 64 step))) = true := by
    simp [isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLExact, hi, shapeOfHOLExact, shapeEqHOL]
  have hrun : evaluateHOLFiniteState st
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 step)])) =
      (none, setVarHOLFinite (ofString "i") (.val (.word (iv + BitVec.ofNat 64 step))) st) := by
    rw [evaluateHOLFiniteState_assign, hev]
    dsimp only; rw [if_pos hvld]; rfl
  have hiv_add : (iv + BitVec.ofNat 64 step).toNat = iv.toNat + step := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    have hs_mod : step % 2 ^ 64 = step := Nat.mod_eq_of_lt (by omega)
    rw [hs_mod]
    exact Nat.mod_eq_of_lt (by omega)
  rw [hrun]
  refine ⟨fun p hp => ?_, fun r hrne hr => absurd hr.symm hrne⟩
  injection hp with _ hp_eq; subst hp_eq
  refine ⟨⟨hma, ?_, ?_, iv + BitVec.ofNat 64 step, ?_, by omega, by omega, fun _ => by omega⟩,
    ByteRegionEffect.refl st Rl |>.with_locals_clock _ st.clock⟩
  · have hne : ofString "i" ≠ ofString "dst" := by decide
    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne, hdst]
  · have hne : ofString "i" ≠ ofString "n" := by decide
    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne, hn]
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]

private theorem eval_memzero_body_bre_g10 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (dst0 n0 : BitVec 64) (Rl : List Ivl)
    (hma : s.memaddrs = ordinaryDomain)
    (hdst : s.locals.lookup (ofString "dst") = some (.val (.word dst0)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n0)))
    (hsub : 0 < n0.toNat → ∃ ivl ∈ Rl, ivl.1 ≤ dst0.toNat ∧ dst0.toNat + n0.toNat ≤ ivl.1 + ivl.2)
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_memzero)).1 ≠ some .timeOut) :
    let out := evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_memzero)
    (Resumes out.1 → ByteRegionEffect s out.2 Rl) ∧
    (∀ rv, out.1 = some (.returned rv) → rv = .val (.word 0) ∧ ByteRegionEffect s out.2 Rl) ∧
    (∀ eid ev, out.1 ≠ some (.exception eid ev)) := by
  have hsub_w : ∀ off, off + 8 ≤ n0.toNat → dst0.toNat + off + 8 ≤ 33806089704 →
      ∃ ivl ∈ Rl, ivl.1 ≤ dst0.toNat + off ∧ dst0.toNat + off + 8 ≤ ivl.1 + ivl.2 := by
    intro off hoff _
    obtain ⟨ivl, hivl, h1, h2⟩ := hsub (by omega)
    exact ⟨ivl, hivl, by omega, by omega⟩
  have hsub_b : ∀ off, off < n0.toNat → dst0.toNat + off + 1 ≤ 33806089704 →
      ∃ ivl ∈ Rl, ivl.1 ≤ dst0.toNat + off ∧ dst0.toNat + off < ivl.1 + ivl.2 := by
    intro off hoff _
    obtain ⟨ivl, hivl, h1, h2⟩ := hsub (by omega)
    exact ⟨ivl, hivl, by omega, by omega⟩
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_memzero,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hnt ⊢
  rw [evaluateHOLFiniteState_dec_total] at hnt ⊢
  dsimp only at hnt ⊢
  have hev0 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.const (BitVec.ofNat 64 0)) = some (.val (.word 0)) := rfl
  have hsh0 : shapeEqHOL .one (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  rw [hev0] at hnt ⊢; dsimp only at hnt ⊢; rw [if_pos hsh0] at hnt ⊢
  set s1 := setVarHOLFinite (ofString "i") (.val (.word 0)) s
  have hs1_dst : s1.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
    have hne : ofString "i" ≠ ofString "dst" := by decide
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne, hdst]
  have hs1_n : s1.locals.lookup (ofString "n") = some (.val (.word n0)) := by
    have hne : ofString "i" ≠ ofString "n" := by decide
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne, hn]
  have hs1_i : s1.locals.lookup (ofString "i") = some (.val (.word 0)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hinv1 : MemzeroBreInvG10 dst0 n0 s1 :=
    ⟨hma, hs1_dst, hs1_n, 0, hs1_i, Nat.zero_le _, Nat.zero_le _, fun h => by simp at h⟩
  have heff_s_s1 : ByteRegionEffect s s1 Rl :=
    ByteRegionEffect.refl s Rl |>.with_locals_clock s1.locals s1.clock
  have hcond_nl : ∀ (t : PanSemStateFiniteExact 64 F) (iv : BitVec 64) (step : Nat),
      t.locals.lookup (ofString "n") = some (.val (.word n0)) →
      t.locals.lookup (ofString "i") = some (.val (.word iv)) →
      iv.toNat ≤ 33806089704 → step ≤ 32 →
      @evalHOLFinite 64 F _ t (fun a => Classical.propDecidable (t.memaddrs a))
        (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 step)])) =
        some (.val (.word (if iv.toNat + step ≤ n0.toNat then 1 else 0))) := by
    intro t iv step htn hti hiv_le hst_le
    rw [evalHOLFinite_eq_toExact]
    have hz_s : BitVec.ofNat 64 step + (0 : BitVec 64) = BitVec.ofNat 64 step := BitVec.add_zero _
    have hadd : (iv + (BitVec.ofNat 64 step + (0 : BitVec 64))).toNat = iv.toNat + step := by
      rw [hz_s, BitVec.toNat_add, BitVec.toNat_ofNat]
      have hs_mod : step % 2 ^ 64 = step := Nat.mod_eq_of_lt (by omega)
      rw [hs_mod]
      exact Nat.mod_eq_of_lt (by omega)
    simp only [evalHOLExact, evalListHOLExact, htn, hti, wordOpHOL, wordOp, valueIsWord, valueWord,
      List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, Bool.not_eq_true', decide_eq_false_iff_not]
    change some (ValueHOL.val (HolWordLab.word (if ¬n0.toNat < (iv + (BitVec.ofNat 64 step + (0 : BitVec 64))).toNat then 1 else 0))) = _
    rw [hadd]
    by_cases hle : iv.toNat + step ≤ n0.toNat
    · have hnl : ¬ (n0.toNat < iv.toNat + step) := by omega
      simp [hle, hnl]
    · have hlt : n0.toNat < iv.toNat + step := by omega
      simp [hle, hlt]
  let lp1 : ProgHOL 64 := .while (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 32)]))
    (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) (.const (BitVec.ofNat 64 0)))
      (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const (BitVec.ofNat 64 8)]) (.const (BitVec.ofNat 64 0)))
        (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const (BitVec.ofNat 64 16)]) (.const (BitVec.ofNat 64 0)))
          (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const (BitVec.ofNat 64 24)]) (.const (BitVec.ofNat 64 0)))
            (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 32)]))))))
  have hL1 : ∀ t0 : PanSemStateFiniteExact 64 F, MemzeroBreInvG10 dst0 n0 t0 →
      (evaluateHOLFiniteState t0 lp1).1 ≠ some .timeOut →
      ((evaluateHOLFiniteState t0 lp1).1 = none →
        MemzeroBreInvG10 dst0 n0 (evaluateHOLFiniteState t0 lp1).2 ∧
        ByteRegionEffect t0 (evaluateHOLFiniteState t0 lp1).2 Rl) ∧
      ((evaluateHOLFiniteState t0 lp1).1 ≠ none → (evaluateHOLFiniteState t0 lp1).1 = some .error) := by
    intro t0 hinv0 hnt1
    refine memzero_loop_runner_g10 Rl dst0 n0 _ _ (fun st ⟨st_ma, st_dst, st_n, iv, st_i, hiv_n, hiv_he, hdom_prev⟩ => ?_) t0 hinv0 hnt1
    refine ⟨if iv.toNat + 32 ≤ n0.toNat then 1 else 0, hcond_nl st iv 32 st_n st_i hiv_he (by omega), fun hcv => ?_⟩
    have hle32 : iv.toNat + 32 ≤ n0.toNat := by split_ifs at hcv with h; exact h; exact absurd rfl hcv
    let d0 := decClockHOLFinite st
    have w0 := memzero_word_store_step_g10 (st := d0) (Rl := Rl) (c := 0)
      st_ma (fun hb => hsub_w (iv.toNat + 0) (by omega) (by omega))
      (eval_add2_di_g10 d0 dst0 iv st_dst st_i)
      ⟨fun h => by have := hdom_prev (by omega); omega, by omega⟩
    apply seq_none_or_err_bre_g10 ⟨fun m hm => (w0.1 m hm).1, w0.2⟩
    intro m1 hm1 he1; obtain ⟨_, l1, dom1⟩ := w0.1 m1 hm1
    have ma1 : m1.memaddrs = ordinaryDomain := he1.memaddrs.trans st_ma
    have w8 := memzero_word_store_step_g10 (st := m1) (Rl := Rl) (c := 8)
      ma1 (fun hb => hsub_w (iv.toNat + 8) (by omega) (by omega))
      (eval_add3_dic_g10 m1 dst0 iv 8 (l1.symm ▸ st_dst) (l1.symm ▸ st_i)) ⟨fun _ => by omega, by omega⟩
    apply seq_none_or_err_bre_g10 ⟨fun m hm => (w8.1 m hm).1, w8.2⟩
    intro m2 hm2 he2; obtain ⟨_, l2, dom2⟩ := w8.1 m2 hm2
    have ma2 : m2.memaddrs = ordinaryDomain := he2.memaddrs.trans ma1
    have w16 := memzero_word_store_step_g10 (st := m2) (Rl := Rl) (c := 16)
      ma2 (fun hb => hsub_w (iv.toNat + 16) (by omega) (by omega))
      (eval_add3_dic_g10 m2 dst0 iv 16 (by rw [l2, l1]; exact st_dst) (by rw [l2, l1]; exact st_i)) ⟨fun _ => by omega, by omega⟩
    apply seq_none_or_err_bre_g10 ⟨fun m hm => (w16.1 m hm).1, w16.2⟩
    intro m3 hm3 he3; obtain ⟨_, l3, dom3⟩ := w16.1 m3 hm3
    have ma3 : m3.memaddrs = ordinaryDomain := he3.memaddrs.trans ma2
    have w24 := memzero_word_store_step_g10 (st := m3) (Rl := Rl) (c := 24)
      ma3 (fun hb => hsub_w (iv.toNat + 24) (by omega) (by omega))
      (eval_add3_dic_g10 m3 dst0 iv 24 (by rw [l3, l2, l1]; exact st_dst) (by rw [l3, l2, l1]; exact st_i)) ⟨fun _ => by omega, by omega⟩
    apply seq_none_or_err_bre_g10 ⟨fun m hm => (w24.1 m hm).1, w24.2⟩
    intro m4 hm4 he4; obtain ⟨_, l4, dom4⟩ := w24.1 m4 hm4
    exact assign_i_memzero_step_g10 m4 dst0 iv n0 32 Rl (he4.memaddrs.trans ma3)
      (by rw [l4, l3, l2, l1]; exact st_dst)
      (by rw [l4, l3, l2, l1]; exact st_n)
      (by rw [l4, l3, l2, l1]; exact st_i) (by omega) hle32 (by omega)
  let lp2 : ProgHOL 64 := .while (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 8)]))
    (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) (.const (BitVec.ofNat 64 0)))
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 8)])))
  have hL2 : ∀ t0 : PanSemStateFiniteExact 64 F, MemzeroBreInvG10 dst0 n0 t0 →
      (evaluateHOLFiniteState t0 lp2).1 ≠ some .timeOut →
      ((evaluateHOLFiniteState t0 lp2).1 = none →
        MemzeroBreInvG10 dst0 n0 (evaluateHOLFiniteState t0 lp2).2 ∧
        ByteRegionEffect t0 (evaluateHOLFiniteState t0 lp2).2 Rl) ∧
      ((evaluateHOLFiniteState t0 lp2).1 ≠ none → (evaluateHOLFiniteState t0 lp2).1 = some .error) := by
    intro t0 hinv0 hnt2
    refine memzero_loop_runner_g10 Rl dst0 n0 _ _ (fun st ⟨st_ma, st_dst, st_n, iv, st_i, hiv_n, hiv_he, hdom_prev⟩ => ?_) t0 hinv0 hnt2
    refine ⟨if iv.toNat + 8 ≤ n0.toNat then 1 else 0, hcond_nl st iv 8 st_n st_i hiv_he (by omega), fun hcv => ?_⟩
    have hle8 : iv.toNat + 8 ≤ n0.toNat := by split_ifs at hcv with h; exact h; exact absurd rfl hcv
    let d0 := decClockHOLFinite st
    have w0 := memzero_word_store_step_g10 (st := d0) (Rl := Rl) (c := 0)
      st_ma (fun hb => hsub_w (iv.toNat + 0) (by omega) (by omega))
      (eval_add2_di_g10 d0 dst0 iv st_dst st_i)
      ⟨fun h => by have := hdom_prev (by omega); omega, by omega⟩
    apply seq_none_or_err_bre_g10 ⟨fun m hm => (w0.1 m hm).1, w0.2⟩
    intro m1 hm1 he1; obtain ⟨_, l1, dom1⟩ := w0.1 m1 hm1
    exact assign_i_memzero_step_g10 m1 dst0 iv n0 8 Rl (he1.memaddrs.trans st_ma)
      (l1.symm ▸ st_dst) (l1.symm ▸ st_n) (l1.symm ▸ st_i) (by omega) hle8 (by omega)
  let lp3 : ProgHOL 64 := .while (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 8)]))
    (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) (.const (BitVec.ofNat 64 0)))
      (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const (BitVec.ofNat 64 1)]) (.const (BitVec.ofNat 64 0)))
        (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const (BitVec.ofNat 64 2)]) (.const (BitVec.ofNat 64 0)))
          (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const (BitVec.ofNat 64 3)]) (.const (BitVec.ofNat 64 0)))
            (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const (BitVec.ofNat 64 4)]) (.const (BitVec.ofNat 64 0)))
              (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const (BitVec.ofNat 64 5)]) (.const (BitVec.ofNat 64 0)))
                (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const (BitVec.ofNat 64 6)]) (.const (BitVec.ofNat 64 0)))
                  (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const (BitVec.ofNat 64 7)]) (.const (BitVec.ofNat 64 0)))
                    (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 8)]))))))))))
  have hL3 : ∀ t0 : PanSemStateFiniteExact 64 F, MemzeroBreInvG10 dst0 n0 t0 →
      (evaluateHOLFiniteState t0 lp3).1 ≠ some .timeOut →
      ((evaluateHOLFiniteState t0 lp3).1 = none →
        MemzeroBreInvG10 dst0 n0 (evaluateHOLFiniteState t0 lp3).2 ∧
        ByteRegionEffect t0 (evaluateHOLFiniteState t0 lp3).2 Rl) ∧
      ((evaluateHOLFiniteState t0 lp3).1 ≠ none → (evaluateHOLFiniteState t0 lp3).1 = some .error) := by
    intro t0 hinv0 hnt3
    refine memzero_loop_runner_g10 Rl dst0 n0 _ _ (fun st ⟨st_ma, st_dst, st_n, iv, st_i, hiv_n, hiv_he, hdom_prev⟩ => ?_) t0 hinv0 hnt3
    refine ⟨if iv.toNat + 8 ≤ n0.toNat then 1 else 0, hcond_nl st iv 8 st_n st_i hiv_he (by omega), fun hcv => ?_⟩
    have hle8 : iv.toNat + 8 ≤ n0.toNat := by split_ifs at hcv with h; exact h; exact absurd rfl hcv
    let d0 := decClockHOLFinite st
    have b0 := memzero_byte_store_step_g10 (st := d0) (Rl := Rl) (c := 0)
      st_ma (fun hb => hsub_b (iv.toNat + 0) (by omega) (by omega))
      (eval_add2_di_g10 d0 dst0 iv st_dst st_i) ⟨fun h => by have := hdom_prev (by omega); omega, by omega⟩
    apply seq_none_or_err_bre_g10 ⟨fun m hm => (b0.1 m hm).1, b0.2⟩
    intro m1 hm1 he1; obtain ⟨_, l1, dom1⟩ := b0.1 m1 hm1
    have ma1 : m1.memaddrs = ordinaryDomain := he1.memaddrs.trans st_ma
    have b1 := memzero_byte_store_step_g10 (st := m1) (Rl := Rl) (c := 1)
      ma1 (fun hb => hsub_b (iv.toNat + 1) (by omega) (by omega))
      (eval_add3_dic_g10 m1 dst0 iv 1 (l1.symm ▸ st_dst) (l1.symm ▸ st_i)) ⟨fun _ => by omega, by omega⟩
    apply seq_none_or_err_bre_g10 ⟨fun m hm => (b1.1 m hm).1, b1.2⟩
    intro m2 hm2 he2; obtain ⟨_, l2, dom2⟩ := b1.1 m2 hm2
    have ma2 : m2.memaddrs = ordinaryDomain := he2.memaddrs.trans ma1
    have b2 := memzero_byte_store_step_g10 (st := m2) (Rl := Rl) (c := 2)
      ma2 (fun hb => hsub_b (iv.toNat + 2) (by omega) (by omega))
      (eval_add3_dic_g10 m2 dst0 iv 2 (by rw [l2, l1]; exact st_dst) (by rw [l2, l1]; exact st_i)) ⟨fun _ => by omega, by omega⟩
    apply seq_none_or_err_bre_g10 ⟨fun m hm => (b2.1 m hm).1, b2.2⟩
    intro m3 hm3 he3; obtain ⟨_, l3, dom3⟩ := b2.1 m3 hm3
    have ma3 : m3.memaddrs = ordinaryDomain := he3.memaddrs.trans ma2
    have b3 := memzero_byte_store_step_g10 (st := m3) (Rl := Rl) (c := 3)
      ma3 (fun hb => hsub_b (iv.toNat + 3) (by omega) (by omega))
      (eval_add3_dic_g10 m3 dst0 iv 3 (by rw [l3, l2, l1]; exact st_dst) (by rw [l3, l2, l1]; exact st_i)) ⟨fun _ => by omega, by omega⟩
    apply seq_none_or_err_bre_g10 ⟨fun m hm => (b3.1 m hm).1, b3.2⟩
    intro m4 hm4 he4; obtain ⟨_, l4, dom4⟩ := b3.1 m4 hm4
    have ma4 : m4.memaddrs = ordinaryDomain := he4.memaddrs.trans ma3
    have b4 := memzero_byte_store_step_g10 (st := m4) (Rl := Rl) (c := 4)
      ma4 (fun hb => hsub_b (iv.toNat + 4) (by omega) (by omega))
      (eval_add3_dic_g10 m4 dst0 iv 4 (by rw [l4, l3, l2, l1]; exact st_dst) (by rw [l4, l3, l2, l1]; exact st_i)) ⟨fun _ => by omega, by omega⟩
    apply seq_none_or_err_bre_g10 ⟨fun m hm => (b4.1 m hm).1, b4.2⟩
    intro m5 hm5 he5; obtain ⟨_, l5, dom5⟩ := b4.1 m5 hm5
    have ma5 : m5.memaddrs = ordinaryDomain := he5.memaddrs.trans ma4
    have b5 := memzero_byte_store_step_g10 (st := m5) (Rl := Rl) (c := 5)
      ma5 (fun hb => hsub_b (iv.toNat + 5) (by omega) (by omega))
      (eval_add3_dic_g10 m5 dst0 iv 5 (by rw [l5, l4, l3, l2, l1]; exact st_dst) (by rw [l5, l4, l3, l2, l1]; exact st_i)) ⟨fun _ => by omega, by omega⟩
    apply seq_none_or_err_bre_g10 ⟨fun m hm => (b5.1 m hm).1, b5.2⟩
    intro m6 hm6 he6; obtain ⟨_, l6, dom6⟩ := b5.1 m6 hm6
    have ma6 : m6.memaddrs = ordinaryDomain := he6.memaddrs.trans ma5
    have b6 := memzero_byte_store_step_g10 (st := m6) (Rl := Rl) (c := 6)
      ma6 (fun hb => hsub_b (iv.toNat + 6) (by omega) (by omega))
      (eval_add3_dic_g10 m6 dst0 iv 6 (by rw [l6, l5, l4, l3, l2, l1]; exact st_dst) (by rw [l6, l5, l4, l3, l2, l1]; exact st_i)) ⟨fun _ => by omega, by omega⟩
    apply seq_none_or_err_bre_g10 ⟨fun m hm => (b6.1 m hm).1, b6.2⟩
    intro m7 hm7 he7; obtain ⟨_, l7, dom7⟩ := b6.1 m7 hm7
    have ma7 : m7.memaddrs = ordinaryDomain := he7.memaddrs.trans ma6
    have b7 := memzero_byte_store_step_g10 (st := m7) (Rl := Rl) (c := 7)
      ma7 (fun hb => hsub_b (iv.toNat + 7) (by omega) (by omega))
      (eval_add3_dic_g10 m7 dst0 iv 7 (by rw [l7, l6, l5, l4, l3, l2, l1]; exact st_dst) (by rw [l7, l6, l5, l4, l3, l2, l1]; exact st_i)) ⟨fun _ => by omega, by omega⟩
    apply seq_none_or_err_bre_g10 ⟨fun m hm => (b7.1 m hm).1, b7.2⟩
    intro m8 hm8 he8; obtain ⟨_, l8, dom8⟩ := b7.1 m8 hm8
    exact assign_i_memzero_step_g10 m8 dst0 iv n0 8 Rl (he8.memaddrs.trans ma7)
      (by rw [l8, l7, l6, l5, l4, l3, l2, l1]; exact st_dst)
      (by rw [l8, l7, l6, l5, l4, l3, l2, l1]; exact st_n)
      (by rw [l8, l7, l6, l5, l4, l3, l2, l1]; exact st_i)
      (by omega) hle8 (by omega)
  let lp4 : ProgHOL 64 := .while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n")))
    (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) (.const (BitVec.ofNat 64 0)))
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 1)])))
  have hL4 : ∀ t0 : PanSemStateFiniteExact 64 F, MemzeroBreInvG10 dst0 n0 t0 →
      (evaluateHOLFiniteState t0 lp4).1 ≠ some .timeOut →
      ((evaluateHOLFiniteState t0 lp4).1 = none →
        MemzeroBreInvG10 dst0 n0 (evaluateHOLFiniteState t0 lp4).2 ∧
        ByteRegionEffect t0 (evaluateHOLFiniteState t0 lp4).2 Rl) ∧
      ((evaluateHOLFiniteState t0 lp4).1 ≠ none → (evaluateHOLFiniteState t0 lp4).1 = some .error) := by
    intro t0 hinv0 hnt4
    refine memzero_loop_runner_g10 Rl dst0 n0 _ _ (fun st ⟨st_ma, st_dst, st_n, iv, st_i, hiv_n, hiv_he, hdom_prev⟩ => ?_) t0 hinv0 hnt4
    have hc4 : @evalHOLFinite 64 F _ st (fun a => Classical.propDecidable (st.memaddrs a))
        (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) =
        some (.val (.word (if iv.toNat < n0.toNat then 1 else 0))) := by
      rw [evalHOLFinite_eq_toExact]
      simp [evalHOLExact, st_i, st_n, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def]
    refine ⟨if iv.toNat < n0.toNat then 1 else 0, hc4, fun hcv => ?_⟩
    have hlt1 : iv.toNat < n0.toNat := by split_ifs at hcv with h; exact h; exact absurd rfl hcv
    let d0 := decClockHOLFinite st
    have b0 := memzero_byte_store_step_g10 (st := d0) (Rl := Rl) (c := 0)
      st_ma (fun hb => hsub_b (iv.toNat + 0) (by omega) (by omega))
      (eval_add2_di_g10 d0 dst0 iv st_dst st_i) ⟨fun h => by have := hdom_prev (by omega); omega, by omega⟩
    apply seq_none_or_err_bre_g10 ⟨fun m hm => (b0.1 m hm).1, b0.2⟩
    intro m1 hm1 he1; obtain ⟨_, l1, dom1⟩ := b0.1 m1 hm1
    exact assign_i_memzero_step_g10 m1 dst0 iv n0 1 Rl (he1.memaddrs.trans st_ma)
      (l1.symm ▸ st_dst) (l1.symm ▸ st_n) (l1.symm ▸ st_i)
      (by omega) (by omega) (by omega)
  let iteP : ProgHOL 64 := .ite
    (.cmp .equal (.op .and [.var .local (ofString "dst"), .const (BitVec.ofNat 64 7)]) (.const (BitVec.ofNat 64 0)))
    (.seq lp1 lp2)
    .skip
  have hite_spec : ∀ t0 : PanSemStateFiniteExact 64 F,
      MemzeroBreInvG10 dst0 n0 t0 →
      (evaluateHOLFiniteState t0 iteP).1 ≠ some .timeOut →
      ((evaluateHOLFiniteState t0 iteP).1 = none →
        MemzeroBreInvG10 dst0 n0 (evaluateHOLFiniteState t0 iteP).2 ∧
        ByteRegionEffect t0 (evaluateHOLFiniteState t0 iteP).2 Rl) ∧
      ((evaluateHOLFiniteState t0 iteP).1 ≠ none → (evaluateHOLFiniteState t0 iteP).1 = some .error) := by
    intro t0 hinv0 hnt_i
    dsimp only [iteP] at hnt_i ⊢
    rw [evaluateHOLFiniteState_ite] at hnt_i ⊢
    rcases hcond_ev : @evalHOLExact 64 F _ t0.toExact (fun a => Classical.propDecidable (t0.memaddrs a))
        (.cmp .equal (.op .and [.var .local (ofString "dst"), .const (BitVec.ofNat 64 7)]) (.const (BitVec.ofNat 64 0))) with _ | cv
    · simp only [hcond_ev] at hnt_i ⊢
      exact ⟨fun h => by simp at h, fun _ => by simp⟩
    · have hcv_w : ∃ cw : BitVec 64, cv = .val (.word cw) := by
        simp [evalHOLExact, evalListHOLExact, hinv0.2.1, wordOpHOL, wordOp, valueIsWord, valueWord,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hcond_ev
        exact ⟨_, hcond_ev.symm⟩
      obtain ⟨cw, rfl⟩ := hcv_w
      simp only [hcond_ev] at hnt_i ⊢
      by_cases hcw0 : cw = 0
      · rw [if_pos hcw0, evaluateHOLFiniteState_skip]
        exact ⟨fun _ => ⟨hinv0, ByteRegionEffect.refl t0 Rl⟩, fun h => False.elim (h rfl)⟩
      · rw [if_neg hcw0] at hnt_i ⊢
        rw [evaluateHOLFiniteState_seq_line780] at hnt_i ⊢
        rcases hr1 : evaluateHOLFiniteState t0 lp1 with ⟨r1, m1⟩
        have hnt1 : r1 ≠ some .timeOut := by rintro rfl; rw [hr1] at hnt_i; exact hnt_i rfl
        have hs1_res := hL1 t0 hinv0 (by rw [hr1]; exact hnt1)
        rw [hr1] at hs1_res
        simp only [hr1] at hnt_i ⊢
        cases r1 with
        | some r => exact ⟨fun h => by simp at h, hs1_res.2⟩
        | none =>
          dsimp only at hnt_i ⊢
          obtain ⟨hm1_inv, he1⟩ := hs1_res.1 rfl
          have hs2_res := hL2 m1 hm1_inv hnt_i
          exact ⟨fun hn => ⟨(hs2_res.1 hn).1, he1.trans (hs2_res.1 hn).2⟩, hs2_res.2⟩
  change (let out := (let res := evaluateHOLFiniteState s1 (.seq iteP (.seq lp3 (.seq lp4 (.return (.const (BitVec.ofNat 64 0))))))
    (res.1, { res.2 with locals := HolFiniteMapExact.resVarEq res.2.locals (ofString "i", s.locals.lookup (ofString "i")) }))
    (Resumes out.1 → ByteRegionEffect s out.2 Rl) ∧
    (∀ rv, out.1 = some (.returned rv) → rv = .val (.word 0) ∧ ByteRegionEffect s out.2 Rl) ∧
    (∀ eid ev, out.1 ≠ some (.exception eid ev)))
  have hnt' : (evaluateHOLFiniteState s1 (.seq iteP (.seq lp3 (.seq lp4 (.return (.const (BitVec.ofNat 64 0))))))).1 ≠
      some .timeOut := hnt
  clear hnt
  rw [evaluateHOLFiniteState_seq_line780] at hnt' ⊢
  rcases h_ite : evaluateHOLFiniteState s1 iteP with ⟨r_ite, s2⟩
  simp only [h_ite] at hnt' ⊢
  have hnt_ite : r_ite ≠ some .timeOut := by rintro rfl; exact hnt' rfl
  have hs_ite := hite_spec s1 hinv1 (by rw [h_ite]; exact hnt_ite)
  rw [h_ite] at hs_ite
  cases r_ite with
  | some r =>
    dsimp only at hnt' ⊢
    have herr := hs_ite.2 (by simp)
    injection herr with hr_eq; subst hr_eq
    exact ⟨fun hr => False.elim (M11.not_resumes_error hr), fun _ h => by simp at h, fun _ _ h => by simp at h⟩
  | none =>
    dsimp only at hnt' ⊢
    obtain ⟨hinv2, heff2⟩ := hs_ite.1 rfl
    rw [evaluateHOLFiniteState_seq_line780] at hnt' ⊢
    rcases h_l3 : evaluateHOLFiniteState s2 lp3 with ⟨rl3, s3⟩
    simp only [h_l3] at hnt' ⊢
    have hnt_l3 : rl3 ≠ some .timeOut := by rintro rfl; exact hnt' rfl
    have hs_l3 := hL3 s2 hinv2 (by rw [h_l3]; exact hnt_l3)
    rw [h_l3] at hs_l3
    cases rl3 with
    | some r =>
      dsimp only at hnt' ⊢
      have herr := hs_l3.2 (by simp)
      injection herr with hr_eq; subst hr_eq
      exact ⟨fun hr => False.elim (M11.not_resumes_error hr), fun _ h => by simp at h, fun _ _ h => by simp at h⟩
    | none =>
      dsimp only at hnt' ⊢
      obtain ⟨hinv3, heff3⟩ := hs_l3.1 rfl
      rw [evaluateHOLFiniteState_seq_line780] at hnt' ⊢
      rcases h_l4 : evaluateHOLFiniteState s3 lp4 with ⟨rl4, s4⟩
      simp only [h_l4] at hnt' ⊢
      have hnt_l4 : rl4 ≠ some .timeOut := by rintro rfl; exact hnt' rfl
      have hs_l4 := hL4 s3 hinv3 (by rw [h_l4]; exact hnt_l4)
      rw [h_l4] at hs_l4
      cases rl4 with
      | some r =>
        dsimp only at hnt' ⊢
        have herr := hs_l4.2 (by simp)
        injection herr with hr_eq; subst hr_eq
        exact ⟨fun hr => False.elim (M11.not_resumes_error hr), fun _ h => by simp at h, fun _ _ h => by simp at h⟩
      | none =>
        dsimp only at hnt' ⊢
        obtain ⟨_, heff4⟩ := hs_l4.1 rfl
        rw [evaluateHOLFiniteState_return]
        have hev_r0 : @evalHOLExact 64 F _ s4.toExact
            (fun a => Classical.propDecidable (s4.memaddrs a)) (.const (BitVec.ofNat 64 0)) =
            some (.val (.word 0)) := rfl
        have hsz : sizeOfShapeWithContextHOL s4.structs (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) ≤ 32 := by
          simp [shapeOfHOLExact]
        rw [hev_r0]; dsimp only; rw [if_pos hsz]; dsimp only
        have heff_all : ByteRegionEffect s (emptyLocalsHOLFinite s4) Rl :=
          (((heff_s_s1.trans heff2).trans heff3).trans heff4).with_locals_clock _ _
        refine ⟨fun _ => heff_all.with_locals_clock _ _, fun rv hrv => ?_, fun _ _ h => by simp at h⟩
        injection hrv with hrv'; injection hrv' with hrv''
        exact ⟨hrv''.symm, heff_all.with_locals_clock _ _⟩

private theorem eval_call_memzero_bre_g10 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (dstExp nExp : ExpHOL 64)
    (dst0 n0 : BitVec 64) (Rl : List Ivl)
    (hcode : s.code = originalRuntimeCode)
    (hma : s.memaddrs = ordinaryDomain)
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
      some (.val (.word dst0)))
    (hn : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nExp =
      some (.val (.word n0)))
    (hsub : 0 < n0.toNat → ∃ ivl ∈ Rl, ivl.1 ≤ dst0.toNat ∧ dst0.toNat + n0.toNat ≤ ivl.1 + ivl.2)
    (hnt : (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "memzero") [dstExp, nExp])).1 ≠ some .timeOut) :
    let out := evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "memzero") [dstExp, nExp])
    (out.1 = none → ByteRegionEffect s out.2 Rl ∧ out.2.locals = s.locals) ∧
    (out.1 ≠ none → ¬ Resumes out.1) := by
  dsimp only
  rw [evaluateHOLFiniteState_call] at hnt ⊢
  have hargs : evalListHOLFinite s
      (h := fun a => Classical.propDecidable (s.memaddrs a)) [dstExp, nExp] =
      some [.val (.word dst0), .val (.word n0)] := by
    simp [evalListHOLFinite, evalListHOLExact, hdst, hn]
  have hlook := pan_two_word_lookup s.code.lookup (ofString "memzero")
    (ofString "dst") (ofString "n")
    (sourceFnBody Guest.Software.guestFn_memzero) dst0 n0
    (by decide)
    (by rw [hcode]; exact lookup_memzero_g10)
  rw [hargs] at hnt ⊢; dsimp only at hnt ⊢
  rw [hlook] at hnt ⊢; dsimp only at hnt ⊢
  by_cases hclk0 : s.clock = 0
  · rw [if_pos hclk0] at hnt; exact absurd rfl hnt
  · rw [if_neg hclk0] at hnt ⊢
    let cmap : HolFiniteMapExact MlS (ValueHOL 64) :=
      (HolFiniteMapExact.empty.update (ofString "dst", ValueHOL.val (.word dst0))).update
        (ofString "n", ValueHOL.val (.word n0))
    let entry := callEntryStateHOLFinite s cmap
    have hent_dst : entry.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
      have h1 : ofString "n" ≠ ofString "dst" := by decide
      simp [entry, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, h1, Ne.symm h1]
    have hent_n : entry.locals.lookup (ofString "n") = some (.val (.word n0)) := by
      simp [entry, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    rcases hb : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_memzero) with ⟨br, bs⟩
    have hnt_b : br ≠ some .timeOut := by
      rintro rfl
      have hb' : evaluateHOLFiniteState (callEntryStateHOLFinite s cmap)
        (sourceFnBody Guest.Software.guestFn_memzero) = (some .timeOut, bs) := hb
      rw [hb'] at hnt; exact hnt rfl
    obtain ⟨_, hret, hexn⟩ := eval_memzero_body_bre_g10 entry dst0 n0 Rl hma
      hent_dst hent_n hsub (by rw [hb]; exact hnt_b)
    rw [hb] at hret hexn
    dsimp only at hret hexn
    cases br with
    | none =>
      exact ⟨fun h => by simp at h, fun _ hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩
    | some r =>
      cases r with
      | timeOut => exact absurd rfl hnt_b
      | exception eid ev => exact absurd rfl (hexn eid ev)
      | returned rv =>
        obtain ⟨rfl, heff_b⟩ := hret rv rfl
        dsimp only
        have hsh : shapeEqHOL (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) .one = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        rw [if_pos hsh]
        have heff_s_ent : ByteRegionEffect s entry Rl :=
          ByteRegionEffect.refl s Rl |>.with_locals_clock entry.locals entry.clock
        exact ⟨fun _ => ⟨(heff_s_ent.trans heff_b).with_locals_clock s.locals bs.clock, rfl⟩,
          fun h => False.elim (h rfl)⟩
      | _ =>
        exact ⟨fun h => by simp at h, fun _ hr => by rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h⟩

theorem lookup_frame_mem_alloc_g10 :
    originalRuntimeCode.lookup (ofString "frame_mem_alloc") =
      some ([(ofString "n", .one)], sourceFnBody Guest.Software.guestFn_frame_mem_alloc, .one) :=
  lookup_of_guestAst_getElem 10 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_frame_mem_alloc) rfl

private theorem frame_mem_alloc_body_no_evmErr_g10 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hcode : s.code = originalRuntimeCode) :
    ¬ IsEvmErr (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_frame_mem_alloc)).1 := by
  have hbody_eq : sourceFnBody Guest.Software.guestFn_frame_mem_alloc =
      .dec (ofString "p") .one (.var .global (ofString "frame_mem_ptr"))
        (.seq
          (.ite (.cmp .lower (.op .sub [.var .global (ofString "scratch_ptr"), .var .local (ofString "p")])
              (.var .local (ofString "n")))
            (.call (some (none, none)) (ofString "trap_with") [.const 6])
            .skip)
          (.dec (ofString "q") .one
            (.op .and [.op .add [.var .local (ofString "p"), .var .local (ofString "n"), .const 7],
              .op .sub [.const 0, .const 8]])
            (.seq
              (.ite (.cmp .lower (.var .global (ofString "scratch_ptr")) (.var .local (ofString "q")))
                (.call (some (none, none)) (ofString "trap_with") [.const 6])
                .skip)
              (.seq
                (.assign .global (ofString "frame_mem_ptr") (.var .local (ofString "q")))
                (.return (.var .local (ofString "p"))))))) := rfl
  have htrap : ∀ (t : PanSemStateFiniteExact 64 F), t.code = originalRuntimeCode →
      let out := evaluateHOLFiniteState t (.call (some (none, none)) (ofString "trap_with") [.const 6])
      out.1 ≠ none ∧ ¬ IsEvmErr out.1 := by
    intro t htc; dsimp only
    rw [evaluateHOLFiniteState_call]
    rcases hargs : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) [.const 6] with _ | vals
    · exact ⟨by simp, by rintro ⟨_, h⟩; cases h⟩
    · dsimp only
      rcases hl : lookupCodeHOLFinite t.code.lookup (ofString "trap_with") vals with _ | ⟨body', callee, rs⟩
      · exact ⟨by simp, by rintro ⟨_, h⟩; cases h⟩
      · dsimp only
        have hbody_tr : body' = sourceFnBody Guest.Software.guestFn_trap_with :=
          lookupCodeHOLFinite_installed_body t.code.lookup (ofString "trap_with") _ _ _ _ _ vals callee
            (by rw [htc]; exact lookup_trap_with) hl
        subst hbody_tr
        split
        · exact ⟨by simp, by rintro ⟨_, h⟩; cases h⟩
        · have hout := evaluate_trap_with_body_outcomes (callEntryStateHOLFinite t callee)
          rcases hr : evaluateHOLFiniteState (callEntryStateHOLFinite t callee)
              (sourceFnBody Guest.Software.guestFn_trap_with) with ⟨res, st⟩
          rw [hr] at hout; dsimp only at hout ⊢
          cases res with
          | none => exact absurd rfl hout.1
          | some r0 =>
            cases r0 with
            | returned v => exact absurd rfl (hout.2.1 v)
            | exception eid v =>
              refine ⟨by simp, ?_⟩
              rintro ⟨_, h⟩; injection h with h'; injection h' with he hw
              subst he hw
              exact hout.2.2 (ofString "EvmErr") v (by decide) rfl
            | _ => exact ⟨by simp, by rintro ⟨_, h⟩; cases h⟩
  rw [hbody_eq, evaluateHOLFiniteState_dec_total]; dsimp only
  split
  · rintro ⟨_, h⟩; cases h
  · rename_i vp _
    split
    · dsimp only
      set s1 := setVarHOLFinite (ofString "p") vp s
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
      split
      · split
        · simp only [evaluateHOLFiniteState_skip]
          rw [evaluateHOLFiniteState_dec_total]; dsimp only
          split
          · rintro ⟨_, h⟩; cases h
          · rename_i vq _
            split
            · dsimp only
              set s2 := setVarHOLFinite (ofString "q") vq s1
              rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
              split
              · split
                · simp only [evaluateHOLFiniteState_skip]
                  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
                  split
                  · rintro ⟨_, h⟩; cases h
                  · split
                    · dsimp only; rw [evaluateHOLFiniteState_return]
                      split
                      · rintro ⟨_, h⟩; cases h
                      · split <;> (rintro ⟨_, h⟩; cases h)
                    · rintro ⟨_, h⟩; cases h
                · have ht2 := htrap s2 hcode
                  rcases htr2 : evaluateHOLFiniteState s2 (.call (some (none, none)) (ofString "trap_with") [.const 6]) with ⟨r2, t2⟩
                  rw [htr2] at ht2
                  cases r2 with
                  | none => exact absurd rfl ht2.1
                  | some _ => exact ht2.2
              · rintro ⟨_, h⟩; cases h
            · rintro ⟨_, h⟩; cases h
        · have ht1 := htrap s1 hcode
          rcases htr1 : evaluateHOLFiniteState s1 (.call (some (none, none)) (ofString "trap_with") [.const 6]) with ⟨r1, t1⟩
          rw [htr1] at ht1
          cases r1 with
          | none => exact absurd rfl ht1.1
          | some _ => exact ht1.2
      · rintro ⟨_, h⟩; cases h
    · rintro ⟨_, h⟩; cases h

private theorem frame_mem_alloc_body_run_g10 {F : Type}
    (state : PanSemStateFiniteExact 64 F) (p sp n : BitVec 64)
    (hcode : state.code = originalRuntimeCode)
    (hp_lookup : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word p)))
    (hsp_lookup : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word sp)))
    (hn : state.locals.lookup (ofString "n") = some (.val (.word n))) :
    let out := evaluateHOLFiniteState state (sourceFnBody Guest.Software.guestFn_frame_mem_alloc)
    let q := (p + (n + 7)) &&& ((0 : BitVec 64) - 8)
    ∀ retVal : ValueHOL 64, out.1 = some (.returned retVal) →
      retVal = .val (.word p) ∧ ¬ ((sp - p).toNat < n.toNat) ∧ ¬ (sp.toNat < q.toNat) ∧
      out.2 = { state with
        globals := (state.globals.update (ofString "frame_mem_ptr", .val (.word q)))
        locals := out.2.locals
        clock := out.2.clock } := by
  dsimp only
  have hbody_eq : sourceFnBody Guest.Software.guestFn_frame_mem_alloc =
      .dec (ofString "p") .one (.var .global (ofString "frame_mem_ptr"))
        (.seq
          (.ite (.cmp .lower (.op .sub [.var .global (ofString "scratch_ptr"), .var .local (ofString "p")])
              (.var .local (ofString "n")))
            (.call (some (none, none)) (ofString "trap_with") [.const 6])
            .skip)
          (.dec (ofString "q") .one
            (.op .and [.op .add [.var .local (ofString "p"), .var .local (ofString "n"), .const 7],
              .op .sub [.const 0, .const 8]])
            (.seq
              (.ite (.cmp .lower (.var .global (ofString "scratch_ptr")) (.var .local (ofString "q")))
                (.call (some (none, none)) (ofString "trap_with") [.const 6])
                .skip)
              (.seq
                (.assign .global (ofString "frame_mem_ptr") (.var .local (ofString "q")))
                (.return (.var .local (ofString "p"))))))) := rfl
  rw [hbody_eq, evaluateHOLFiniteState_dec_total]
  have hp_eval : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a))
      (.var .global (ofString "frame_mem_ptr")) = some (.val (.word p)) := hp_lookup
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
  have hsp_p : pState.globals.lookup (ofString "scratch_ptr") = some (.val (.word sp)) := hsp_lookup
  have hcode_p : pState.code = originalRuntimeCode := hcode
  rw [evaluateHOLFiniteState_seq_line780]
  have hev1 : @evalHOLExact 64 F _ pState.toExact
      (fun a => Classical.propDecidable (pState.memaddrs a))
      (.cmp .lower (.op .sub [.var .global (ofString "scratch_ptr"), .var .local (ofString "p")])
        (.var .local (ofString "n"))) =
      some (.val (.word (if (sp - p).toNat < n.toNat then 1 else 0))) := by
    simp only [evalHOLExact, evalListHOLExact, hsp_p, hp_loc, hn_loc,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, decide_eq_true_eq]
    rfl
  by_cases hcmp1 : (sp - p).toNat < n.toNat
  · have hite1 : evaluateHOLFiniteState pState
        (.ite (.cmp .lower (.op .sub [.var .global (ofString "scratch_ptr"), .var .local (ofString "p")])
            (.var .local (ofString "n")))
          (.call (some (none, none)) (ofString "trap_with") [.const 6])
          .skip) =
        evaluateHOLFiniteState pState (.call (some (none, none)) (ofString "trap_with") [.const 6]) := by
      rw [evaluateHOLFiniteState_ite, hev1, if_pos hcmp1]; simp
    rw [hite1]
    have hno_none := evaluate_call_trap_with_no_none_g10 pState 6 hcode_p
    have hno_ret := fun w => evaluate_call_trap_with_no_return_g10 pState 6 w hcode_p
    rcases htr : evaluateHOLFiniteState pState (.call (some (none, none)) (ofString "trap_with") [.const 6]) with ⟨r1, s1⟩
    rw [htr] at hno_none hno_ret
    cases r1 with
    | none => exact absurd rfl hno_none
    | some r1' =>
      intro retVal hret
      exact False.elim (hno_ret retVal hret)
  · have hite1 : evaluateHOLFiniteState pState
        (.ite (.cmp .lower (.op .sub [.var .global (ofString "scratch_ptr"), .var .local (ofString "p")])
            (.var .local (ofString "n")))
          (.call (some (none, none)) (ofString "trap_with") [.const 6])
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
      exact congrArg (fun w => some (ValueHOL.val (HolWordLab.word w)))
        (InitECandidate.Solver.HeapPotential.alloc_q_word_eq p n)
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
    have hsp_q : qState.globals.lookup (ofString "scratch_ptr") = some (.val (.word sp)) := hsp_lookup
    have hcode_q : qState.code = originalRuntimeCode := hcode
    rw [evaluateHOLFiniteState_seq_line780]
    have hev2 : @evalHOLExact 64 F _ qState.toExact
        (fun a => Classical.propDecidable (qState.memaddrs a))
        (.cmp .lower (.var .global (ofString "scratch_ptr")) (.var .local (ofString "q"))) =
        some (.val (.word (if sp.toNat < q.toNat then 1 else 0))) := by
      simp only [evalHOLExact, hsp_q, hq_loc, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, decide_eq_true_eq]
    by_cases hcmp2 : sp.toNat < q.toNat
    · have hite2 : evaluateHOLFiniteState qState
          (.ite (.cmp .lower (.var .global (ofString "scratch_ptr")) (.var .local (ofString "q")))
            (.call (some (none, none)) (ofString "trap_with") [.const 6])
            .skip) =
          evaluateHOLFiniteState qState (.call (some (none, none)) (ofString "trap_with") [.const 6]) := by
        rw [evaluateHOLFiniteState_ite, hev2, if_pos hcmp2]; simp
      rw [hite2]
      have hno_none := evaluate_call_trap_with_no_none_g10 qState 6 hcode_q
      have hno_ret := fun w => evaluate_call_trap_with_no_return_g10 qState 6 w hcode_q
      rcases htr : evaluateHOLFiniteState qState (.call (some (none, none)) (ofString "trap_with") [.const 6]) with ⟨r2, s2⟩
      rw [htr] at hno_none hno_ret
      cases r2 with
      | none => exact absurd rfl hno_none
      | some r2' =>
        intro retVal hret
        exact False.elim (hno_ret retVal hret)
    · have hite2 : evaluateHOLFiniteState qState
          (.ite (.cmp .lower (.var .global (ofString "scratch_ptr")) (.var .local (ofString "q")))
            (.call (some (none, none)) (ofString "trap_with") [.const 6])
            .skip) = (none, qState) := by
        rw [evaluateHOLFiniteState_ite, hev2, if_neg hcmp2]; simp [evaluateHOLFiniteState_skip]
      rw [hite2]
      dsimp only
      have hp_g : qState.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word p)) := hp_lookup
      have heval_end : evaluateHOLFiniteState qState
          (.seq (.assign .global (ofString "frame_mem_ptr") (.var .local (ofString "q")))
            (.return (.var .local (ofString "p")))) =
          (some (.returned (.val (.word p))),
            emptyLocalsHOLFinite (setGlobalHOLFinite (ofString "frame_mem_ptr") (.val (.word q)) qState)) := by
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
        simp [evalHOLExact, hq_loc, hp_loc_q, isValidValueHOLExact, lookupKvarHOLExact, hp_g,
          shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite, setGlobalHOLFinite,
          evaluateHOLFiniteState_return, sizeOfShapeWithContextHOL]
      rw [heval_end]
      intro retVal hret
      injection hret with hr
      injection hr with hr'
      exact ⟨hr'.symm, hcmp1, hcmp2, rfl⟩

private theorem frame_mem_alloc_arith_g10 (p sp n : BitVec 64)
    (hp_le_sp : p.toNat ≤ sp.toNat)
    (hsp_le : sp.toNat ≤ scratchEnd)
    (hp_al : p.toNat % 8 = 0)
    (hcmp1 : ¬ ((sp - p).toNat < n.toNat))
    (hcmp2 : ¬ (sp.toNat < ((p + (n + 7)) &&& ((0 : BitVec 64) - 8)).toNat)) :
    let q := (p + (n + 7)) &&& ((0 : BitVec 64) - 8)
    q.toNat = p.toNat + (n.toNat + 7) / 8 * 8 ∧
    q.toNat ≤ sp.toNat ∧ q.toNat % 8 = 0 ∧ p.toNat ≤ q.toNat := by
  intro q
  have hse : scratchEnd < 2 ^ 64 - 8 := by rw [R11Shards.scratchEnd_val]; decide
  have hsub : (sp - p).toNat = sp.toNat - p.toNat := by
    rw [BitVec.toNat_sub]; omega
  have hn_le : n.toNat ≤ sp.toNat - p.toNat := by omega
  have h7 : (7 : BitVec 64).toNat = 7 := rfl
  have hn7 : (n + 7).toNat = n.toNat + 7 := by
    rw [BitVec.toNat_add, h7]; omega
  have hsum : (p + (n + 7)).toNat = p.toNat + n.toNat + 7 := by
    rw [BitVec.toNat_add, hn7]; omega
  have hq_nat : q.toNat = (p + (n + 7)).toNat / 8 * 8 :=
    and_neg8_toNat (p + (n + 7))
  rw [hsum] at hq_nat
  have hq_le : q.toNat ≤ sp.toNat := Nat.le_of_not_lt hcmp2
  exact ⟨by omega, hq_le, by omega, by omega⟩

private structure FrameMemByteEffG10 {F : Type} (s post : PanSemStateFiniteExact 64 F) (Rl : List Ivl) : Prop where
  code       : post.code = s.code
  memaddrs   : post.memaddrs = s.memaddrs
  shMemaddrs : post.shMemaddrs = s.shMemaddrs
  baseAddr   : post.baseAddr = s.baseAddr
  be         : post.be = s.be
  glob_other : ∀ g : String, ofString g ≠ ofString "frame_mem_ptr" → post.globals.lookup (ofString g) = s.globals.lookup (ofString g)
  out_dom    : ∀ a : BitVec 64, ¬ s.memaddrs a → post.memory a = s.memory a
  cell_frame : ∀ a : BitVec 64, (∀ i ∈ Rl, ¬ CellHits a.toNat i) → post.memory a = s.memory a
  byte_frame : ∀ b : Nat, b < 2 ^ 64 → (∀ i ∈ Rl, ¬ InIvl b i) → memB post b = memB s b

private theorem FrameMemByteEffG10.trans {F : Type} {a b c : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (h1 : FrameMemByteEffG10 a b Rl) (h2 : FrameMemByteEffG10 b c Rl) :
    FrameMemByteEffG10 a c Rl := by
  refine ⟨h2.code.trans h1.code, h2.memaddrs.trans h1.memaddrs,
    h2.shMemaddrs.trans h1.shMemaddrs, h2.baseAddr.trans h1.baseAddr,
    h2.be.trans h1.be, fun g hg => (h2.glob_other g hg).trans (h1.glob_other g hg), ?_, ?_, ?_⟩
  · intro x hx
    have hxb : ¬ b.memaddrs x := by rw [h1.memaddrs]; exact hx
    rw [h2.out_dom x hxb, h1.out_dom x hx]
  · intro x hx; rw [h2.cell_frame x hx, h1.cell_frame x hx]
  · intro x hx hno; rw [h2.byte_frame x hx hno, h1.byte_frame x hx hno]

private theorem FrameMemByteEffG10.mono {F : Type} {s post : PanSemStateFiniteExact 64 F} {R1 R2 : List Ivl}
    (h : FrameMemByteEffG10 s post R1)
    (hsub : ∀ i ∈ R1, ∃ j ∈ R2, j.1 ≤ i.1 ∧ i.1 + i.2 ≤ j.1 + j.2) :
    FrameMemByteEffG10 s post R2 := by
  refine ⟨h.code, h.memaddrs, h.shMemaddrs, h.baseAddr, h.be, h.glob_other, h.out_dom, ?_, ?_⟩
  · intro a ha; apply h.cell_frame a; intro i hi ⟨hc1, hc2⟩
    obtain ⟨j, hj, h1, h2⟩ := hsub i hi
    exact ha j hj ⟨by omega, by omega⟩
  · intro b hb hno; apply h.byte_frame b hb; intro i hi ⟨hb1, hb2⟩
    obtain ⟨j, hj, h1, h2⟩ := hsub i hi
    exact hno j hj ⟨by omega, by omega⟩

private theorem evmInv_of_head_mem_extend_g10 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {freshIvl : Ivl}
    (hInv : EvmInv s) (hHMWF : Group10.HeadMemChainWF s)
    (hApost : ArenaReady post)
    (hfm_le : globN s "frame_mem_ptr" ≤ globN post "frame_mem_ptr")
    (heff : FrameMemByteEffG10 s post [freshIvl, (globN s "ev", 280), (memW s (globN s "ev" + 24), memW s (globN s "ev" + 40))])
    (hfresh : freshIvl = (0, 0) ∨
      (freshIvl.1 % 8 = 0 ∧ freshIvl.2 % 8 = 0 ∧
        Inside freshIvl (globN s "frame_mem_ptr") (globN post "frame_mem_ptr")))
    (he0_other : ∀ off, off + 8 ≤ 280 → off % 8 = 0 → off ≠ 32 → off ≠ 40 →
      memW post (globN s "ev" + off) = memW s (globN s "ev" + off))
    (hnew_mem :
      (freshIvl.2 = 0 ∧ memW post (globN s "ev" + 40) = memW s (globN s "ev" + 40) ∧
        globN post "frame_mem_ptr" = globN s "frame_mem_ptr") ∨
      (freshIvl.2 ≠ 0 ∧
        memW s (globN s "ev" + 24) + memW s (globN s "ev" + 40) = freshIvl.1 ∧
        memW post (globN s "ev" + 40) = memW s (globN s "ev" + 40) + freshIvl.2 ∧
        globN post "frame_mem_ptr" = freshIvl.1 + freshIvl.2))
    (hlen_le_cap : memW post (globN s "ev" + 32) ≤ memW post (globN s "ev" + 40))
    (hlen_al32 : memW post (globN s "ev" + 32) % 32 = 0) :
    EvmInv post ∧ Group10.HeadMemChainWF post ∧ evmChain post = evmChain s ∧ evmR post = evmR s := by
  obtain ⟨hAs, S, hW, hch_ne, hch_len, hch_last, hFW_all, hFR_all, hRW, hFO_pw, hFO_disj, hAT, hMarks, hRoles, hGas⟩ := hInv
  obtain ⟨Nd_at, hTr_at, hAT_at⟩ := hAT
  have hWT : WorldTypedWith s S Nd_at := ⟨hW.1, hW.2.1, hW.2.2.1, hTr_at⟩
  set e0 := globN s "ev"
  set c0 := globN s "cur_cont"
  set oldMem : Ivl := (memW s (e0 + 24), memW s (e0 + 40))
  have hch_cons : ∃ tl, evmChain s = (e0, c0) :: tl := ⟨_, rfl⟩
  obtain ⟨chTail, hch_eq⟩ := hch_cons
  have hhead_mem : (e0, c0) ∈ evmChain s := by rw [hch_eq]; exact List.mem_cons_self
  have hhead_FW := hFW_all _ hhead_mem
  obtain ⟨hb1, _, _, _⟩ := frameWF_bounds hAs.2 hhead_FW
  dsimp only at hb1
  have he0_8 : e0 % 8 = 0 := (hhead_FW.1 (e0, 280) (by simp)).2.1
  have holdMem_8 : oldMem.1 % 8 = 0 := hhead_FW.2.2.1.1
  have holdMem_sz8 : oldMem.2 % 8 = 0 := hhead_FW.2.2.1.2.1
  have hRl_list : ∀ x ∈ ([freshIvl, (e0, 280), oldMem] : List Ivl), x.1 % 8 = 0 := by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rcases hfresh with rfl | ⟨h8, _⟩
      · rfl
      · exact h8
    · exact he0_8
    · exact holdMem_8
  have hdom_eq : post.memaddrs = s.memaddrs := heff.memaddrs
  have hglob_eq : ∀ g, ofString g ≠ ofString "frame_mem_ptr" → globN post g = globN s g :=
    fun g hg => OpHandlers.globN_eq_of_lookup_eq (heff.glob_other g hg)
  have hh : globN s "heap_ptr" ≤ globN post "heap_ptr" := by rw [hglob_eq "heap_ptr" (by decide)]
  have hsc_le : globN post "scratch_ptr" ≤ globN s "scratch_ptr" := by rw [hglob_eq "scratch_ptr" (by decide)]
  have hfo_disj_wti : ∀ o ∈ frameObjects s (e0, c0), ∀ i ∈ worldTypedIvls s S Nd_at, i.2 = 0 ∨ Disj o i := by
    intro o ho i hi
    unfold worldTypedIvls at hi; simp only [List.mem_append] at hi
    rcases hi with ((((h1 | h2) | h3) | h4) | h5) | h6
    · obtain ⟨t, ht, hfp⟩ := List.mem_flatMap.1 h1
      exact Or.inr ((hFO_disj _ hhead_mem o ho).1 t ht i hfp)
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 h2
      exact Or.inr ((hFO_disj _ hhead_mem o ho).2 _ (typedRec_in_fixedObjects s hr))
    · simp only [List.mem_singleton] at h3; subst h3
      have hfix_j : (if globN s "journal_cap" = 0 then 0 else globN s "journal", 32 * globN s "journal_cap") ∈ fixedObjects s := by
        unfold fixedObjects; exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (by simp)))
      exact Or.inr ((hFO_disj _ hhead_mem o ho).2 _ hfix_j)
    · exact Or.inr ((hFO_disj _ hhead_mem o ho).2 _ (blockOut_in_fixedObjects h4))
    · exact Or.inr ((hFO_disj _ hhead_mem o ho).2 _ (bal_in_fixedObjects h5))
    · exact Or.inr (hAT_at o (List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨_, hhead_mem, rfl⟩, ho⟩) i h6)
  have hfresh_disj_alloc : ∀ i : Ivl, Allocated s i → Disj freshIvl i := by
    intro i hal
    rcases hfresh with rfl | ⟨_, _, hfin⟩
    · exact Or.inl rfl
    · obtain ⟨hfin1, hfin2⟩ := hfin
      have h1 := hAs.2.2.1; have h2 := hAs.2.2.2.1
      have h3 := hApost.2.2.2.2.1
      rw [hglob_eq "scratch_ptr" (by decide)] at h3
      rw [R11Shards.heapLimit_val] at h1; rw [R11Shards.scratchStart_val] at h2
      rcases hal with hheap | hscr
      · obtain ⟨_, hhi2⟩ := hheap
        exact Or.inr (Or.inr (Or.inr (by omega)))
      · obtain ⟨hlo1, _⟩ := hscr
        exact Or.inr (Or.inr (Or.inl (by omega)))
  have hwrite_disj_wti : ∀ x ∈ ([freshIvl, (e0, 280), oldMem] : List Ivl),
      ∀ i ∈ worldTypedIvls s S Nd_at, i.2 = 0 ∨ Disj x i := by
    intro x hx i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rcases worldTypedIvls_allocated hWT hi with hi0 | hal
      · exact Or.inl hi0
      · exact Or.inr (hfresh_disj_alloc i hal)
    · exact hfo_disj_wti (e0, 280) (by simp [frameObjects]) i hi
    · exact hfo_disj_wti oldMem (by simp [frameObjects, oldMem]) i hi
  have hbre_dummy : ByteRegionEffect s { post with globals := s.globals } [freshIvl, (e0, 280), oldMem] :=
    ⟨heff.code, heff.memaddrs, heff.shMemaddrs, heff.baseAddr, heff.be, rfl,
     heff.out_dom, heff.cell_frame, heff.byte_frame⟩
  have hcellG : SameTypedCells s { post with globals := s.globals } S Nd_at :=
    ByteRegionEffect.sameTypedCells (Rl := []) (extra := [freshIvl, (e0, 280), oldMem])
      hAs.1.memaddrs hWT (fun _ h => by simp at h) hwrite_disj_wti hbre_dummy
  have hcell : SameTypedCells s post S Nd_at := hcellG
  have hfeq : fixedObjects post = fixedObjects s := by
    unfold fixedObjects
    rw [blockOutObjects_eq hAs.2 hWT.2.2.1 hcell (hglob_eq "bo" (by decide)),
        balObjects_eq hAs.2 hWT.1 hWT.2.2.1 hcell (hglob_eq "bal_accounts" (by decide)),
        hglob_eq "journal" (by decide),
        hglob_eq "journal_cap" (by decide)]
    congr 3
    apply List.map_congr_left
    intro gn hgn
    have hne : ofString gn.1 ≠ ofString "frame_mem_ptr" := by clear * - hgn; revert gn hgn; decide
    rw [hglob_eq gn.1 hne]
  have hFT_post := fixedTyped_of_eq hApost hWT.2.2.1 hh hsc_le hfeq
  have hcg : ∀ g ∈ coreWorldGlobals, globN post g = globN s g := by
    intro g hg
    have hne : ofString g ≠ ofString "frame_mem_ptr" := by clear * - hg; revert g hg; decide
    exact hglob_eq g hne
  obtain ⟨hWT_post, _⟩ := worldTypedWith_congr_w1 hAs hApost hh hsc_le hcg hcell hWT
    ⟨hFT_post, fun o ho => Or.inl (by rw [← hfeq]; exact ho)⟩
  have hW_post : WorldTyped post S :=
    ⟨hWT_post.1, hWT_post.2.1, hWT_post.2.2.1, Nd_at, hWT_post.2.2.2⟩
  have hmemW_disj : ∀ {base sz k : Nat}, base + sz ≤ 2 ^ 64 → base % 8 = 0 → k % 8 = 0 → k + 8 ≤ sz →
      (∀ x ∈ ([freshIvl, (e0, 280), oldMem] : List Ivl), Disj x (base, sz)) →
      memW post (base + k) = memW s (base + k) := by
    intro base sz k hbnd hb8 hk8 hk hdj
    unfold memW
    have ha : base + k < 2 ^ 64 := by omega
    have hbk8 : (base + k) % 8 = 0 := by omega
    have hbit : (BitVec.ofNat 64 (base + k)).toNat = base + k := Nat.mod_eq_of_lt ha
    rw [heff.cell_frame (BitVec.ofNat 64 (base + k))]
    intro x hx; rw [hbit]
    exact not_cellHits_of_disj_aligned (i := (base, sz)) hbk8 (hRl_list x hx)
      (Nat.le_add_right base k) (Nat.add_le_add_left hk base) (R11Shards.Disj.symm (hdj x hx))
  have hpw_head_tail :
      (frameObjects s (e0, c0)).Pairwise Disj ∧
      (∀ o1 ∈ frameObjects s (e0, c0),
        ∀ ec ∈ chTail, ∀ o2 ∈ frameObjects s ec, Disj o1 o2) := by
    have hpw := hFO_pw
    rw [hch_eq, List.map_cons, List.flatten_cons, List.pairwise_append] at hpw
    refine ⟨hpw.1, fun o1 ho1 ec hec o2 ho2 => hpw.2.2 o1 ho1 o2 ?_⟩
    exact List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨ec, hec, rfl⟩, ho2⟩
  have hfresh_disj_fo : ∀ ec ∈ evmChain s, ∀ o ∈ frameObjects s ec, Disj freshIvl o := by
    intro ec hec o ho
    rcases hfresh with rfl | ⟨_, _, hfin⟩
    · exact Or.inl rfl
    · obtain ⟨hfin1, hfin2⟩ := hfin
      have hFW := hFW_all ec hec
      have h1 := hAs.2.2.1; have h2 := hAs.2.2.2.1
      have h3 := hApost.2.2.2.2.1
      rw [hglob_eq "scratch_ptr" (by decide)] at h3
      rw [R11Shards.heapLimit_val] at h1; rw [R11Shards.scratchStart_val] at h2
      unfold frameObjects at ho
      rcases List.mem_append.1 ho with ho7 | holog
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at ho7
        rcases ho7 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · obtain ⟨hin1, _⟩ := (hFW.1 (ec.1, 280) (by simp)).1
          exact Or.inr (Or.inr (Or.inl (by dsimp only at hin1 ⊢; omega)))
        · obtain ⟨hin1, _⟩ := (hFW.1 (ec.2, 104) (by simp)).1
          exact Or.inr (Or.inr (Or.inl (by dsimp only at hin1 ⊢; omega)))
        · obtain ⟨hin1, _⟩ := (hFW.1 (memW s (ec.1 + 8), 32 * memW s (ec.1 + 232)) (by simp)).1
          exact Or.inr (Or.inr (Or.inl (by dsimp only at hin1 ⊢; omega)))
        · obtain ⟨_, hin2⟩ := hFW.2.1
          exact Or.inr (Or.inr (Or.inr (by dsimp only at hin2 ⊢; omega)))
        · obtain ⟨hin1, _⟩ := (hFW.1 (memW s (ec.1 + 88), 24) (by simp)).1
          exact Or.inr (Or.inr (Or.inl (by dsimp only at hin1 ⊢; omega)))
        · rcases hFW.2.2.2.2.2.2.2.2.2.2.2.2.1 with ⟨_, hin2⟩ | ⟨hin1, _⟩
          · exact Or.inr (Or.inr (Or.inr (by omega)))
          · exact Or.inr (Or.inr (Or.inl (by omega)))
        · rcases hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with ⟨hz, _⟩ | ⟨⟨_, hin2⟩, _⟩
          · unfold frameRet; simp [hz]; exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (Or.inr (by omega)))
      · unfold frameLogObjects at holog; dsimp only at holog
        obtain ⟨idx, hidx_mem, ho_own⟩ := List.mem_flatMap.1 holog
        rw [List.mem_range] at hidx_mem
        rcases hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with hz | ⟨_, _, _, _, hent⟩
        · obtain ⟨hin1, _⟩ := (hFW.1 (memW s (ec.1 + 88), 24) (by simp)).1
          dsimp only at hin1; omega
        · have hle := (hent idx hidx_mem).2
          have ho_rec := (List.mem_filter.1 ho_own).1
          simp only [logRecordIvls, List.mem_cons, List.not_mem_nil, or_false] at ho_rec
          rcases ho_rec with rfl | rfl | rfl | rfl
          · obtain ⟨_, hin2⟩ := hle.2.1; exact Or.inr (Or.inr (Or.inr (by dsimp only at hin2 ⊢; omega)))
          · obtain ⟨_, hin2⟩ := hle.2.2.2.2.1; exact Or.inr (Or.inr (Or.inr (by dsimp only at hin2 ⊢; omega)))
          · obtain ⟨_, hin2⟩ := hle.2.2.2.2.2.1; exact Or.inr (Or.inr (Or.inr (by dsimp only at hin2 ⊢; omega)))
          · obtain ⟨_, hin2⟩ := hle.2.2.2.2.2.2; exact Or.inr (Or.inr (Or.inr (by dsimp only at hin2 ⊢; omega)))
  have hdisj_old_fresh : ∀ o : Ivl, Disj oldMem o → Disj freshIvl o →
      Disj (memW post (e0 + 24), memW post (e0 + 40)) o := by
    intro o hd_old hd_fr
    have he24_eq := he0_other 24 (by omega) (by omega) (by omega) (by omega)
    rw [he24_eq]
    rcases hnew_mem with ⟨_, h40_eq, _⟩ | ⟨hnz, hcontig, h40_eq, _⟩
    · rw [h40_eq]; exact hd_old
    · rw [h40_eq]
      rcases hd_fr with hz | hz | hlt | hgt
      · exact absurd hz hnz
      · exact Or.inr (Or.inl hz)
      · exact Or.inr (Or.inr (Or.inl (by dsimp only [oldMem] at hcontig hlt ⊢; omega)))
      · rcases hd_old with hoz | hoz | holt | hogt
        · dsimp only [oldMem] at hoz
          rw [hoz] at hcontig ⊢
          simp only [Nat.add_zero, Nat.zero_add] at hcontig ⊢
          rw [hcontig]
          exact Or.inr (Or.inr (Or.inr hgt))
        · exact Or.inr (Or.inl hoz)
        · by_cases hoz0 : o.2 = 0
          · exact Or.inr (Or.inl hoz0)
          · have hle_f : freshIvl.1 ≤ o.1 := by rw [← hcontig]; exact holt
            exact False.elim (by omega)
        · exact Or.inr (Or.inr (Or.inr hogt))
  have hhead_pw := hpw_head_tail.1
  unfold frameObjects at hhead_pw
  have hp0 := List.pairwise_cons.1 hhead_pw
  have hp1 := List.pairwise_cons.1 hp0.2
  have hp2 := List.pairwise_cons.1 hp1.2
  have hp3 := List.pairwise_cons.1 hp2.2
  have hdisj_write_nonmem : ∀ ec ∈ evmChain s,
      (∀ x ∈ ([freshIvl, (e0, 280), oldMem] : List Ivl), Disj x (ec.2, 104)) ∧
      (∀ x ∈ ([freshIvl, (e0, 280), oldMem] : List Ivl), Disj x (memW s (ec.1 + 88), 24)) ∧
      (∀ x ∈ ([freshIvl, (e0, 280), oldMem] : List Ivl), Disj x (frameLogs s ec)) ∧
      (∀ i < memW s (memW s (ec.1 + 88) + 8),
        ∀ x ∈ ([freshIvl, (e0, 280), oldMem] : List Ivl),
          Disj x (memW s (memW s (memW s (ec.1 + 88)) + 8 * i), 40)) := by
    intro ec hec
    have hlog_in : ∀ i < memW s (memW s (ec.1 + 88) + 8),
        (memW s (memW s (memW s (ec.1 + 88)) + 8 * i), 40) ∈ frameLogObjects s ec := by
      intro i hi; unfold frameLogObjects; dsimp only
      exact List.mem_flatMap.2 ⟨i, List.mem_range.2 hi,
        by unfold logOwnedIvls logRecordIvls; exact List.mem_filter.2 ⟨by simp, by simp⟩⟩
    rw [hch_eq, List.mem_cons] at hec
    rcases hec with rfl | htail
    · have hmem_head : (e0, c0) ∈ evmChain s := hhead_mem
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl
        · exact hfresh_disj_fo _ hmem_head _ (by simp [frameObjects])
        · exact hp0.1 _ (by simp)
        · exact R11Shards.Disj.symm (hp1.1 _ (by simp [oldMem]))
      · intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl
        · exact hfresh_disj_fo _ hmem_head _ (by simp [frameObjects])
        · exact hp0.1 _ (by simp)
        · exact hp3.1 _ (by simp)
      · intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl
        · exact hfresh_disj_fo _ hmem_head _ (by simp [frameObjects])
        · exact hp0.1 _ (by simp)
        · exact hp3.1 _ (by simp)
      · intro i hi x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        have hli := hlog_in i hi
        rcases hx with rfl | rfl | rfl
        · exact hfresh_disj_fo _ hmem_head _ (by unfold frameObjects; exact List.mem_append_right _ hli)
        · exact hp0.1 _ (by simp [hli])
        · exact hp3.1 _ (by simp [hli])
    · have hmem_ec : ec ∈ evmChain s := by rw [hch_eq]; exact List.mem_cons_of_mem _ htail
      have hall : ∀ o2 ∈ frameObjects s ec, ∀ x ∈ ([freshIvl, (e0, 280), oldMem] : List Ivl), Disj x o2 := by
        intro o2 ho2 x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl
        · exact hfresh_disj_fo ec hmem_ec o2 ho2
        · exact hpw_head_tail.2 _ (by simp [frameObjects]) ec htail o2 ho2
        · exact hpw_head_tail.2 _ (by simp [frameObjects, oldMem]) ec htail o2 ho2
      exact ⟨hall _ (by simp [frameObjects]),
             hall _ (by simp [frameObjects]),
             hall _ (by simp [frameObjects]),
             fun i hi => hall _ (by unfold frameObjects; exact List.mem_append_right _ (hlog_in i hi))⟩
  have htail_rec_eq : ∀ ec ∈ chTail, ∀ k, k + 8 ≤ 280 → k % 8 = 0 → memW post (ec.1 + k) = memW s (ec.1 + k) := by
    intro ec htail k hk hk8
    have hec : ec ∈ evmChain s := by rw [hch_eq]; exact List.mem_cons_of_mem _ htail
    have hFW := hFW_all ec hec
    obtain ⟨hb_e, _, _, _⟩ := frameWF_bounds hAs.2 hFW
    have he8 : ec.1 % 8 = 0 := (hFW.1 (ec.1, 280) (by simp)).2.1
    apply hmemW_disj hb_e he8 hk8 hk
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact hfresh_disj_fo ec hec (ec.1, 280) (by simp [frameObjects])
    · exact hpw_head_tail.2 _ (by simp [frameObjects]) ec htail _ (by simp [frameObjects])
    · exact hpw_head_tail.2 _ (by simp [frameObjects, oldMem]) ec htail _ (by simp [frameObjects])
  have hrec_eq : ∀ ec ∈ evmChain s,
      (∀ k, k + 8 ≤ 280 → k % 8 = 0 → k ≠ 32 → k ≠ 40 → memW post (ec.1 + k) = memW s (ec.1 + k)) ∧
      (∀ k, k + 8 ≤ 104 → k % 8 = 0 → memW post (ec.2 + k) = memW s (ec.2 + k)) ∧
      (∀ k, k + 8 ≤ 24 → k % 8 = 0 → memW post (memW s (ec.1 + 88) + k) = memW s (memW s (ec.1 + 88) + k)) := by
    intro ec hec
    have hFW := hFW_all ec hec
    obtain ⟨_, hb_c, hb_88, _⟩ := frameWF_bounds hAs.2 hFW
    have hc8 : ec.2 % 8 = 0 := (hFW.1 (ec.2, 104) (by simp)).2.1
    have h88_8 : (memW s (ec.1 + 88)) % 8 = 0 := (hFW.1 (memW s (ec.1 + 88), 24) (by simp)).2.1
    obtain ⟨hd_c, hd_88, _, _⟩ := hdisj_write_nonmem ec hec
    refine ⟨?_,
      fun k hk hk8 => hmemW_disj hb_c hc8 hk8 hk hd_c,
      fun k hk hk8 => hmemW_disj hb_88 h88_8 hk8 hk hd_88⟩
    intro k hk hk8 hk_32 hk_40
    rw [hch_eq, List.mem_cons] at hec
    rcases hec with rfl | htail
    · exact he0_other k hk hk8 hk_32 hk_40
    · exact htail_rec_eq ec htail k hk hk8
  have hchain_aux : ∀ (fuel e c : Nat),
      (∀ ec ∈ evmChainFrom s fuel e c, ec ∈ evmChain s) →
      evmChainFrom post fuel e c = evmChainFrom s fuel e c := by
    intro fuel; induction fuel with
    | zero => intros; rfl
    | succ fuel ih =>
      intro e c hsub
      have hec : (e, c) ∈ evmChain s := hsub (e, c) (by simp [evmChainFrom])
      obtain ⟨_, hc_eq, _⟩ := hrec_eq (e, c) hec
      have hc16 := hc_eq 16 (by omega) (by omega)
      have hc0 : memW post c = memW s c := by simpa using hc_eq 0 (by omega) (by omega)
      have hc8 := hc_eq 8 (by omega) (by omega)
      simp only [evmChainFrom, hc16, hc0, hc8]
      split
      · rfl
      · rename_i hne16
        rw [ih]; intro ec' hec'; exact hsub ec' (by simp [evmChainFrom, hne16, hec'])
  have hchain_eq : evmChain post = evmChain s := by
    unfold evmChain
    rw [hglob_eq "ev" (by decide), hglob_eq "cur_cont" (by decide)]
    exact hchain_aux _ _ _ (fun _ h => h)
  have hframeLogs_eq : ∀ ec ∈ evmChain s, frameLogs post ec = frameLogs s ec := by
    intro ec hec
    obtain ⟨he_eq, _, h88_eq⟩ := hrec_eq ec hec
    unfold frameLogs
    rw [he_eq 88 (by omega) (by omega) (by omega) (by omega),
        show memW post (memW s (ec.1 + 88)) = memW s (memW s (ec.1 + 88)) by simpa using h88_eq 0 (by omega) (by omega),
        h88_eq 16 (by omega) (by omega)]
  have hframeRet_eq : ∀ ec ∈ evmChain s, frameRet post ec = frameRet s ec := by
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    unfold frameRet
    rw [he_eq 216 (by omega) (by omega) (by omega) (by omega),
        he_eq 144 (by omega) (by omega) (by omega) (by omega)]
  have hlogs_congr : ∀ ec ∈ evmChain s,
      frameLogObjects post ec = frameLogObjects s ec ∧ LogsListOK post (memW post (ec.1 + 88)) := by
    intro ec hec
    have hFW := hFW_all ec hec
    obtain ⟨_, _, _, hfob⟩ := frameWF_bounds hAs.2 hFW
    obtain ⟨he_eq, _, h88_eq⟩ := hrec_eq ec hec
    obtain ⟨_, _, hd_fl, hd_lr⟩ := hdisj_write_nonmem ec hec
    have hl0 : memW post (memW s (ec.1 + 88)) = memW s (memW s (ec.1 + 88)) := by
      simpa using h88_eq 0 (by omega) (by omega)
    have hl8 := h88_eq 8 (by omega) (by omega)
    have hl16 := h88_eq 16 (by omega) (by omega)
    have harr_eq : ∀ i, i < memW s (memW s (ec.1 + 88) + 8) →
        memW post ((memW s (memW s (ec.1 + 88))) + 8 * i) = memW s ((memW s (memW s (ec.1 + 88))) + 8 * i) := by
      intro i hi
      have hfl_in : frameLogs s ec ∈ frameObjects s ec := by simp [frameObjects]
      have hlen_le : memW s (memW s (ec.1 + 88) + 8) ≤ memW s (memW s (ec.1 + 88) + 16) :=
        hFW.2.2.2.2.2.2.2.2.2.2.2.1
      have hfl_b : (frameLogs s ec).1 + (frameLogs s ec).2 ≤ 2 ^ 64 := by
        rcases hfob _ hfl_in with h0 | hb
        · unfold frameLogs at h0; dsimp only at h0; omega
        · exact hb
      have hfl_8 : (memW s (memW s (ec.1 + 88))) % 8 = 0 := hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
      exact hmemW_disj hfl_b hfl_8 (by omega) (by unfold frameLogs; dsimp only; omega) hd_fl
    have hlr_eq : ∀ i (_hi : i < memW s (memW s (ec.1 + 88) + 8)) off, off + 8 ≤ 40 → off % 8 = 0 →
        memW post ((memW s (memW s (memW s (ec.1 + 88)) + 8 * i)) + off) =
          memW s ((memW s (memW s (memW s (ec.1 + 88)) + 8 * i)) + off) := by
      intro i hi off hoff hoff8
      have hlr_in : (memW s (memW s (memW s (ec.1 + 88)) + 8 * i), 40) ∈ frameObjects s ec := by
        unfold frameObjects; apply List.mem_append_right
        unfold frameLogObjects; dsimp only
        exact List.mem_flatMap.2 ⟨i, List.mem_range.2 hi,
          by unfold logOwnedIvls logRecordIvls; exact List.mem_filter.2 ⟨by simp, by simp⟩⟩
      have hlr_b : memW s (memW s (memW s (ec.1 + 88)) + 8 * i) + 40 ≤ 2 ^ 64 := by
        rcases hfob _ hlr_in with h0 | hb
        · dsimp only at h0; omega
        · exact hb
      have hlr_8 : (memW s (memW s (memW s (ec.1 + 88)) + 8 * i)) % 8 = 0 := by
        rcases hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with hz | ⟨_, _, _, _, hent⟩
        · obtain ⟨he88_in, _⟩ := (hFW.1 (memW s (ec.1 + 88), 24) (by simp)).1
          have h1 := hAs.2.2.2.1; have h2 := hAs.2.2.2.2.1
          rw [R11Shards.scratchStart_val] at h1; dsimp only at he88_in; omega
        · exact (hent i hi).2.1.1
      exact hmemW_disj hlr_b hlr_8 hoff8 hoff (hd_lr i hi)
    refine ⟨?_, ?_⟩
    · unfold frameLogObjects; dsimp only
      rw [he_eq 88 (by omega) (by omega) (by omega) (by omega), hl8]
      apply List.flatMap_congr; intro i hi; rw [List.mem_range] at hi
      rw [hl0, harr_eq i hi]
      have r0 := hlr_eq i hi 0 (by omega) (by omega)
      have r8 := hlr_eq i hi 8 (by omega) (by omega)
      have r16 := hlr_eq i hi 16 (by omega) (by omega)
      have r24 := hlr_eq i hi 24 (by omega) (by omega)
      have r32 := hlr_eq i hi 32 (by omega) (by omega)
      simp only [Nat.add_zero] at r0
      unfold logOwnedIvls logRecordIvls
      rw [r0, r8, r16, r24, r32, hglob_eq "vm_system_address" (by decide)]
    · rw [he_eq 88 (by omega) (by omega) (by omega) (by omega)]
      rcases hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with hz | ⟨hw_l, hal_l, hlt28, hle_cap, hent⟩
      · exact Or.inl hz
      · right
        refine ⟨(wordsOK_congr_dom hdom_eq).2 hw_l, allocated_mono_scr hh hsc_le hal_l,
          by rw [hl8]; exact hlt28, by rw [hl8, hl16]; exact hle_cap, fun i hi => ?_⟩
        rw [hl8] at hi; rw [hl0]
        obtain ⟨hwa, hle⟩ := hent i hi
        refine ⟨(wordAt_congr_dom hdom_eq).2 hwa, ?_⟩
        rw [harr_eq i hi]
        have r0 := hlr_eq i hi 0 (by omega) (by omega)
        have r8 := hlr_eq i hi 8 (by omega) (by omega)
        have r16 := hlr_eq i hi 16 (by omega) (by omega)
        have r24 := hlr_eq i hi 24 (by omega) (by omega)
        have r32 := hlr_eq i hi 32 (by omega) (by omega)
        simp only [Nat.add_zero] at r0
        unfold LogEntryOK at hle ⊢
        rw [r0, r8, r16, r24, r32, hglob_eq "heap_ptr" (by decide)]
        exact ⟨(wordsOK_congr_dom hdom_eq).2 hle.1, hle.2⟩
  have htail_fo_eq : ∀ ec ∈ chTail, frameObjects post ec = frameObjects s ec := by
    intro ec htail
    have hec : ec ∈ evmChain s := by rw [hch_eq]; exact List.mem_cons_of_mem _ htail
    unfold frameObjects
    rw [htail_rec_eq ec htail 8 (by omega) (by omega),
        htail_rec_eq ec htail 232 (by omega) (by omega),
        htail_rec_eq ec htail 24 (by omega) (by omega),
        htail_rec_eq ec htail 40 (by omega) (by omega),
        htail_rec_eq ec htail 88 (by omega) (by omega),
        hframeLogs_eq ec hec, hframeRet_eq ec hec, (hlogs_congr ec hec).1]
  have hfs_eq : ∀ ec ∈ evmChain s, frameScratch post ec = frameScratch s ec := by
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    unfold frameScratch
    rw [he_eq 8 (by omega) (by omega) (by omega) (by omega),
        he_eq 232 (by omega) (by omega) (by omega) (by omega),
        he_eq 88 (by omega) (by omega) (by omega) (by omega)]
  have hfo_post_cases : ∀ ec ∈ evmChain s, ∀ o ∈ frameObjects post ec,
      o ∈ frameObjects s ec ∨ (ec = (e0, c0) ∧ o = (memW post (e0 + 24), memW post (e0 + 40))) := by
    intro ec hec o ho
    rw [hch_eq, List.mem_cons] at hec
    rcases hec with rfl | htail
    · unfold frameObjects at ho
      rw [he0_other 8 (by omega) (by omega) (by omega) (by omega),
          he0_other 232 (by omega) (by omega) (by omega) (by omega),
          he0_other 88 (by omega) (by omega) (by omega) (by omega),
          hframeLogs_eq _ hhead_mem, hframeRet_eq _ hhead_mem, (hlogs_congr _ hhead_mem).1] at ho
      rcases List.mem_append.1 ho with ho7 | holog
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at ho7
        rcases ho7 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact Or.inl (by simp [frameObjects])
        · exact Or.inl (by simp [frameObjects])
        · exact Or.inl (by simp [frameObjects])
        · exact Or.inr ⟨rfl, rfl⟩
        · exact Or.inl (by simp [frameObjects])
        · exact Or.inl (by simp [frameObjects])
        · exact Or.inl (by simp [frameObjects])
      · exact Or.inl (by unfold frameObjects; exact List.mem_append_right _ holog)
    · left; rwa [htail_fo_eq ec htail] at ho
  have hframeRoleSlots_eq : frameRoleSlots post (evmChain s) = frameRoleSlots s (evmChain s) := by
    unfold frameRoleSlots; apply List.flatMap_congr; intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    rw [he_eq 136 (by omega) (by omega) (by omega) (by omega),
        he_eq 168 (by omega) (by omega) (by omega) (by omega),
        he_eq 176 (by omega) (by omega) (by omega) (by omega)]
  have hfp_eq_all : ∀ t ∈ S, htabFootprint post t = htabFootprint s t :=
    fun t ht => htabFootprint_eq hcell ht (hWT.1.2.1 t ht).1
  have hR_eq : evmR post = evmR s :=
    evmR_eq_of_chain_and_words hchain_eq (fun ec hec =>
      ⟨(hrec_eq ec hec).1 64 (by omega) (by omega) (by omega) (by omega),
       (hrec_eq ec hec).1 192 (by omega) (by omega) (by omega) (by omega)⟩)
  have hcap_post_8 : memW post (e0 + 40) % 8 = 0 := by
    rcases hnew_mem with ⟨_, h40_eq, _⟩ | ⟨hnz, _, h40_eq, _⟩
    · rw [h40_eq]; exact holdMem_sz8
    · rcases hfresh with rfl | ⟨_, hf8, _⟩
      · exact absurd rfl hnz
      · rw [h40_eq]; dsimp only [oldMem] at holdMem_sz8; omega
  have hHMWF_post : Group10.HeadMemChainWF post := by
    refine Group10.headMemChainWF_extend hHMWF hchain_eq ?_
      (fun ec hec => (hrec_eq ec hec).2.1 56 (by omega) (by omega))
      (hglob_eq "ev" (by decide))
      (he0_other 24 (by omega) (by omega) (by omega) (by omega))
      hlen_al32 hcap_post_8 ?_
    · intro ec htail
      rw [hch_eq, List.tail_cons] at htail
      exact ⟨htail_rec_eq ec htail 24 (by omega) (by omega),
             htail_rec_eq ec htail 32 (by omega) (by omega),
             htail_rec_eq ec htail 40 (by omega) (by omega)⟩
    · rcases hnew_mem with ⟨_, h40_eq, hfp_eq⟩ | ⟨_, hcontig, h40_eq, hfp_eq⟩
      · rw [h40_eq, hfp_eq]; exact hHMWF.2.1
      · dsimp only [e0] at hcontig h40_eq
        rw [h40_eq, hfp_eq]; omega
  refine ⟨⟨hApost, S, hW_post, ?_⟩, hHMWF_post, hchain_eq, hR_eq⟩
  dsimp only; rw [hchain_eq]
  refine ⟨hch_ne, hch_len, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨ec, hec, hk0⟩ := hch_last
    have hec_mem := List.mem_of_mem_getLast? hec
    exact ⟨ec, hec, by rw [(hrec_eq ec hec_mem).2.1 16 (by omega) (by omega)]; exact hk0⟩
  · intro ec hec
    obtain ⟨he_eq, _, h88_eq⟩ := hrec_eq ec hec
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, _, c17⟩ := hFW_all ec hec
    have hlo_ok := (hlogs_congr ec hec).2
    have hmsg_ok : MsgOwned post S (memW post (ec.1 + 112)) := by
      rw [he_eq 112 (by omega) (by omega) (by omega) (by omega)]
      obtain ⟨hal_m, hw_m, hdt, hdf, hdfo, Nd_m, hTr_m, hdj_m⟩ := c17
      obtain ⟨hTr_int, hsub_int⟩ := R11Shards.triesTypedWith_inter hTr_at hTr_m
      set Ndi := Nd_at.filter (fun n => decide (n ∈ Nd_m))
      have hcell_i : SameTypedCells s post S Ndi := by
        have hwti_sub : ∀ i ∈ worldTypedIvls s S Ndi, i ∈ worldTypedIvls s S Nd_at := by
          intro i hi; unfold worldTypedIvls at hi ⊢
          rcases List.mem_append.1 hi with hpre | hne
          · exact List.mem_append_left _ hpre
          · apply List.mem_append_right; unfold nodeExtents at hne ⊢
            obtain ⟨n, hn, hnx⟩ := List.mem_flatMap.1 hne
            exact List.mem_flatMap.2 ⟨n, (List.mem_filter.1 hn).1, hnx⟩
        refine ⟨hcell.1, hcell.2.1, hcell.2.2.1, hcell.2.2.2.1,
          fun a ha ha8 ⟨i, hi, h1, h2⟩ => hcell.2.2.2.2.1 a ha ha8 ⟨i, hwti_sub i hi, h1, h2⟩,
          fun b hb ⟨i, hi, h1, h2⟩ => hcell.2.2.2.2.2 b hb ⟨i, hwti_sub i hi, h1, h2⟩⟩
      obtain ⟨hWT_i_post, _⟩ := worldTypedWith_congr_w1 hAs hApost hh hsc_le hcg hcell_i
        ⟨hWT.1, hWT.2.1, hWT.2.2.1, hTr_int⟩
        ⟨hFT_post, fun o ho => Or.inl (by rw [← hfeq]; exact ho)⟩
      refine ⟨allocated_mono_scr hh hsc_le hal_m, (wordsOK_congr_dom hdom_eq).2 hw_m,
        fun t ht i hi => by rw [hfp_eq_all t ht] at hi; exact hdt t ht i hi,
        by rw [hfeq]; exact hdf,
        ?_,
        Ndi, hWT_i_post.2.2.2, fun o ho j hj => ?_⟩
      · rw [hchain_eq]; intro ec' hec' o ho
        rcases hfo_post_cases ec' hec' o ho with ho_old | ⟨_, rfl⟩
        · exact hdfo ec' hec' o ho_old
        · exact R11Shards.Disj.symm (hdisj_old_fresh (memW s (ec.1 + 112), 176)
            (R11Shards.Disj.symm (hdfo _ hhead_mem oldMem (by simp [frameObjects, oldMem])))
            (hfresh_disj_alloc (memW s (ec.1 + 112), 176) hal_m))
      · rw [nodeExtents_eq hTr_int.1 hcell_i] at hj
        exact hdj_m o ho j (hsub_int j hj).2
    unfold FrameWF; dsimp only
    rw [he_eq 8 (by omega) (by omega) (by omega) (by omega),
        he_eq 16 (by omega) (by omega) (by omega) (by omega),
        he_eq 232 (by omega) (by omega) (by omega) (by omega),
        he_eq 88 (by omega) (by omega) (by omega) (by omega),
        he_eq 24 (by omega) (by omega) (by omega) (by omega),
        he_eq 136 (by omega) (by omega) (by omega) (by omega),
        he_eq 168 (by omega) (by omega) (by omega) (by omega),
        he_eq 176 (by omega) (by omega) (by omega) (by omega),
        h88_eq 16 (by omega) (by omega), h88_eq 8 (by omega) (by omega),
        hframeLogs_eq ec hec,
        he_eq 216 (by omega) (by omega) (by omega) (by omega),
        he_eq 144 (by omega) (by omega) (by omega) (by omega),
        hframeRet_eq ec hec,
        hglob_eq "scratch_ptr" (by decide),
        hglob_eq "heap_ptr" (by decide),
        hglob_eq "evm_empty" (by decide)]
    rw [he_eq 88 (by omega) (by omega) (by omega) (by omega)] at hlo_ok
    have hret_in_post : (memW s (ec.1 + 216) = 0 ∧ memW s (ec.1 + 144) = globN s "evm_empty") ∨
        Inside (frameRet s ec) sourceBase (globN s "heap_ptr") ∧ WordsOK post (frameRet s ec) := by
      rcases c15 with h0 | ⟨hin, hw⟩
      · exact Or.inl h0
      · exact Or.inr ⟨hin, (wordsOK_congr_dom hdom_eq).2 hw⟩
    rw [hch_eq, List.mem_cons] at hec
    rcases hec with rfl | htail
    · have hc2_post : Inside (memW s (e0 + 24), memW post (e0 + 40)) scratchStart (globN post "frame_mem_ptr") ∧
          WordsOK post (memW s (e0 + 24), memW post (e0 + 40)) := by
        rcases hnew_mem with ⟨_, h40_eq, _⟩ | ⟨hnz, hcontig, h40_eq, _⟩
        · rw [h40_eq]
          exact ⟨⟨c2.1, le_trans c2.2 hfm_le⟩, (wordsOK_congr_dom hdom_eq).2 c3⟩
        · rcases hfresh with rfl | ⟨_, hfsz8, hfin1, hfin2⟩
          · exact absurd rfl hnz
          · rw [h40_eq]
            have hin_new : Inside (memW s (e0 + 24), memW s (e0 + 40) + freshIvl.2) scratchStart (globN post "frame_mem_ptr") :=
              ⟨c2.1, by dsimp only at hcontig hfin2 ⊢; omega⟩
            have hsb_le_ss : sourceBase ≤ scratchStart := by decide
            have hse_le_he : scratchEnd ≤ heapEnd := by decide
            have hfp_le_se : globN post "frame_mem_ptr" ≤ scratchEnd :=
              le_trans hApost.2.2.2.2.1 hApost.2.2.2.2.2.1
            have hw_new : WordsOK post (memW s (e0 + 24), memW s (e0 + 40) + freshIvl.2) :=
              Wave8Contracts.M26.wordsOK_of_guestInv post hApost.1
                (memW s (e0 + 24)) (memW s (e0 + 40) + freshIvl.2)
                holdMem_8 (by dsimp only [oldMem] at holdMem_sz8; omega)
                (le_trans hsb_le_ss c2.1) (le_trans hin_new.2 (le_trans hfp_le_se hse_le_he))
            exact ⟨hin_new, hw_new⟩
      exact ⟨fun i hi => ⟨(c1 i hi).1, (wordsOK_congr_dom hdom_eq).2 (c1 i hi).2⟩,
        hc2_post.1, hc2_post.2, c4, c5, c6, hlen_le_cap, c8, c9, c10, c11, c12,
        c13, (wordsOK_congr_dom hdom_eq).2 c14, hret_in_post, hlo_ok, hmsg_ok⟩
    · rw [htail_rec_eq ec htail 32 (by omega) (by omega),
          htail_rec_eq ec htail 40 (by omega) (by omega)]
      exact ⟨fun i hi => ⟨(c1 i hi).1, (wordsOK_congr_dom hdom_eq).2 (c1 i hi).2⟩,
        ⟨c2.1, le_trans c2.2 hfm_le⟩, (wordsOK_congr_dom hdom_eq).2 c3, c4, c5, c6, c7, c8, c9, c10, c11, c12,
        c13, (wordsOK_congr_dom hdom_eq).2 c14, hret_in_post, hlo_ok, hmsg_ok⟩
  · intro ec hec
    have htail : ec ∈ chTail := by rw [hch_eq, List.tail_cons] at hec; exact hec
    unfold FrameRoom
    rw [htail_rec_eq ec htail 16 (by omega) (by omega),
        htail_rec_eq ec htail 232 (by omega) (by omega)]
    exact hFR_all ec hec
  · intro i hi
    have hi0 : (evmChain s)[i]'(by omega) ∈ evmChain s := List.getElem_mem _
    have hi1_tail : (evmChain s)[i + 1] ∈ chTail := by simp [hch_eq]
    rw [(hrec_eq _ hi0).2.1 80 (by omega) (by omega),
        (hrec_eq _ hi0).2.1 72 (by omega) (by omega),
        htail_rec_eq _ hi1_tail 40 (by omega) (by omega)]
    exact hRW i hi
  · have htail_map_eq : chTail.map (frameObjects post) = chTail.map (frameObjects s) :=
      List.map_congr_left htail_fo_eq
    rw [hch_eq, List.map_cons, List.flatten_cons, htail_map_eq, List.pairwise_append]
    have hFO_pw' := hFO_pw
    rw [hch_eq, List.map_cons, List.flatten_cons, List.pairwise_append] at hFO_pw'
    refine ⟨?_, hFO_pw'.2.1, ?_⟩
    · unfold frameObjects
      rw [he0_other 8 (by omega) (by omega) (by omega) (by omega),
          he0_other 232 (by omega) (by omega) (by omega) (by omega),
          he0_other 88 (by omega) (by omega) (by omega) (by omega),
          hframeLogs_eq _ hhead_mem, hframeRet_eq _ hhead_mem, (hlogs_congr _ hhead_mem).1]
      change ((e0, 280) :: (c0, 104) :: (memW s (e0 + 8), 32 * memW s (e0 + 232)) ::
        (memW post (e0 + 24), memW post (e0 + 40)) :: (memW s (e0 + 88), 24) ::
        frameLogs s (e0, c0) :: frameRet s (e0, c0) :: frameLogObjects s (e0, c0)).Pairwise Disj
      refine List.pairwise_cons.2 ⟨?_, List.pairwise_cons.2 ⟨?_, List.pairwise_cons.2 ⟨?_, List.pairwise_cons.2 ⟨?_, hp3.2⟩⟩⟩⟩
      · intro o ho; simp only [List.mem_cons] at ho
        rcases ho with rfl | rfl | rfl | ho_rest
        · exact hp0.1 _ (by simp)
        · exact hp0.1 _ (by simp)
        · exact R11Shards.Disj.symm (hdisj_old_fresh (e0, 280)
            (R11Shards.Disj.symm (hp0.1 oldMem (by simp [oldMem])))
            (hfresh_disj_fo _ hhead_mem (e0, 280) (by simp [frameObjects])))
        · exact hp0.1 _ (by simp [ho_rest])
      · intro o ho; simp only [List.mem_cons] at ho
        rcases ho with rfl | rfl | ho_rest
        · exact hp1.1 _ (by simp)
        · exact R11Shards.Disj.symm (hdisj_old_fresh (c0, 104)
            (R11Shards.Disj.symm (hp1.1 oldMem (by simp [oldMem])))
            (hfresh_disj_fo _ hhead_mem (c0, 104) (by simp [frameObjects])))
        · exact hp1.1 _ (by simp [ho_rest])
      · intro o ho; simp only [List.mem_cons] at ho
        rcases ho with rfl | ho_rest
        · exact R11Shards.Disj.symm (hdisj_old_fresh (memW s (e0 + 8), 32 * memW s (e0 + 232))
            (R11Shards.Disj.symm (hp2.1 oldMem (by simp [oldMem])))
            (hfresh_disj_fo _ hhead_mem _ (by simp [frameObjects])))
        · exact hp2.1 _ (by simp [ho_rest])
      · intro o ho
        have ho_in : o ∈ frameObjects s (e0, c0) := by
          unfold frameObjects
          simp only [List.mem_cons] at ho
          rcases ho with rfl | rfl | rfl | ho_log
          · simp
          · simp
          · simp
          · exact List.mem_append_right _ ho_log
        exact hdisj_old_fresh o (hp3.1 o ho) (hfresh_disj_fo _ hhead_mem o ho_in)
    · intro o1 ho1 o2 ho2
      obtain ⟨l2, hl2, ho2_in⟩ := List.mem_flatten.1 ho2
      obtain ⟨ec2, hec2, rfl⟩ := List.mem_map.1 hl2
      have hec2_mem : ec2 ∈ evmChain s := by rw [hch_eq]; exact List.mem_cons_of_mem _ hec2
      rcases hfo_post_cases _ hhead_mem o1 ho1 with ho1_old | ⟨_, rfl⟩
      · exact hFO_pw'.2.2 o1 ho1_old o2 ho2
      · exact hdisj_old_fresh o2
          (hFO_pw'.2.2 oldMem (by simp [frameObjects, oldMem]) o2 ho2)
          (hfresh_disj_fo ec2 hec2_mem o2 ho2_in)
  · intro ec hec o ho
    rw [hfeq]
    rcases hfo_post_cases ec hec o ho with ho_old | ⟨_, rfl⟩
    · exact ⟨fun t ht i hi => by rw [hfp_eq_all t ht] at hi; exact (hFO_disj ec hec o ho_old).1 t ht i hi,
        (hFO_disj ec hec o ho_old).2⟩
    · refine ⟨fun t ht i hi => ?_, fun j hj => ?_⟩
      · rw [hfp_eq_all t ht] at hi
        exact hdisj_old_fresh i
          ((hFO_disj _ hhead_mem oldMem (by simp [frameObjects, oldMem])).1 t ht i hi)
          (hfresh_disj_alloc i ((hWT.1.2.1 t ht).2 i hi).1)
      · rcases hWT.2.2.1.1 j hj with hj0 | ⟨hal_j, _⟩
        · exact Or.inr (Or.inl hj0)
        · exact hdisj_old_fresh j
            ((hFO_disj _ hhead_mem oldMem (by simp [frameObjects, oldMem])).2 j hj)
            (hfresh_disj_alloc j hal_j)
  · refine ⟨Nd_at, hWT_post.2.2.2, fun o ho j hj => ?_⟩
    rw [nodeExtents_eq hTr_at.1 hcell] at hj
    obtain ⟨fo, hfo_map, ho_in⟩ := List.mem_flatten.1 ho
    obtain ⟨ec, hec, rfl⟩ := List.mem_map.1 hfo_map
    rcases hfo_post_cases ec hec o ho_in with ho_old | ⟨_, rfl⟩
    · exact hAT_at o (List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨ec, hec, rfl⟩, ho_old⟩) j hj
    · rcases worldTypedIvls_allocated hWT (mem_worldTypedIvls_nodeExtents hj) with hj0 | hal_j
      · exact Or.inr (Or.inl hj0)
      · exact hdisj_old_fresh j
          (hAT_at oldMem (List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨_, hhead_mem, rfl⟩, by simp [frameObjects, oldMem]⟩) j hj)
          (hfresh_disj_alloc j hal_j)
  · have hworldRefs_eq : worldTableRefs post S = worldTableRefs s S := by
      unfold worldTableRefs recordSlots
      rw [hglob_eq "ws" (by decide), hglob_eq "bs" (by decide), hglob_eq "ts" (by decide),
          show globalTableRoots.map (globN post) = globalTableRoots.map (globN s) by
            simp only [globalTableRoots, List.map,
              hglob_eq "bal_accounts" (by decide),
              hglob_eq "bal_idx_accts" (by decide),
              hglob_eq "bal_idx_stor" (by decide)],
          balRecords_eq hWT.1 hcell (hglob_eq "bal_accounts" (by decide)),
          hglob_eq "journal_n" (by decide), hglob_eq "journal" (by decide)]
      have hws_sl : (if globN s "ws" = 0 then [] else wsTableSlots.map fun k => memW post (globN s "ws" + k)) =
          (if globN s "ws" = 0 then [] else wsTableSlots.map fun k => memW s (globN s "ws" + k)) := by
        split; · rfl
        rename_i hnz; apply List.map_congr_left; intro k hk
        exact memW_typedRec_eq hAs.2 hWT.2.2.1 hcell (sz := 40) (by decide) hnz
          (by simp only [wsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk; rcases hk with rfl | rfl <;> omega)
      have hbs_sl : (if globN s "bs" = 0 then [] else bsTableSlots.map fun k => memW post (globN s "bs" + k)) =
          (if globN s "bs" = 0 then [] else bsTableSlots.map fun k => memW s (globN s "bs" + k)) := by
        split; · rfl
        rename_i hnz; apply List.map_congr_left; intro k hk
        exact memW_typedRec_eq hAs.2 hWT.2.2.1 hcell (sz := 80) (by decide) hnz
          (by simp only [bsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk; rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
      have hts_sl : (if globN s "ts" = 0 then [] else tsTableSlots.map fun k => memW post (globN s "ts" + k)) =
          (if globN s "ts" = 0 then [] else tsTableSlots.map fun k => memW s (globN s "ts" + k)) := by
        split; · rfl
        rename_i hnz; apply List.map_congr_left; intro k hk
        exact memW_typedRec_eq hAs.2 hWT.2.2.1 hcell (sz := 72) (by decide) hnz
          (by simp only [tsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk; rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
      have hnest_bs : (if globN s "bs" ≠ 0 ∧ memW post (globN s "bs" + 32) ∈ S then htabValues post (memW post (globN s "bs" + 32)) else []) =
          (if globN s "bs" ≠ 0 ∧ memW s (globN s "bs" + 32) ∈ S then htabValues s (memW s (globN s "bs" + 32)) else []) := by
        by_cases hnz : globN s "bs" = 0
        · simp [hnz]
        · rw [memW_typedRec_eq hAs.2 hWT.2.2.1 hcell (sz := 80) (by decide) hnz (by omega)]
          by_cases hmS : memW s (globN s "bs" + 32) ∈ S
          · simp [hnz, hmS, htabValues_eq hcell hmS (hWT.1.2.1 _ hmS).1]
          · simp [hnz, hmS]
      have hnest_ts : (if globN s "ts" ≠ 0 ∧ memW post (globN s "ts" + 32) ∈ S then htabValues post (memW post (globN s "ts" + 32)) else []) =
          (if globN s "ts" ≠ 0 ∧ memW s (globN s "ts" + 32) ∈ S then htabValues s (memW s (globN s "ts" + 32)) else []) := by
        by_cases hnz : globN s "ts" = 0
        · simp [hnz]
        · rw [memW_typedRec_eq hAs.2 hWT.2.2.1 hcell (sz := 72) (by decide) hnz (by omega)]
          by_cases hmS : memW s (globN s "ts" + 32) ∈ S
          · simp [hnz, hmS, htabValues_eq hcell hmS (hWT.1.2.1 _ hmS).1]
          · simp [hnz, hmS]
      have hbal_fl : (balRecords s).flatMap (fun ad => [memW post ad, memW post (ad + 8)]) =
          (balRecords s).flatMap (fun ad => [memW s ad, memW s (ad + 8)]) := by
        apply List.flatMap_congr; intro ad had
        have had_mem := balRecord_ivl_mem had
        rcases fixedObject_le_2pow64 hAs.2 hWT.2.2.1 (bal_in_fixedObjects had_mem) with h0 | had_bnd
        · dsimp only at h0; omega
        · dsimp only at had_bnd
          have hwti_ad := mem_worldTypedIvls_bal (S := S) (Nd := Nd_at) had_mem
          rw [memW_eq_of_cellHits hcell (by omega) hwti_ad ⟨by dsimp only; omega, by dsimp only; omega⟩,
              memW_eq_of_cellHits hcell (by omega) hwti_ad ⟨by dsimp only; omega, by dsimp only; omega⟩]
      have hjrn_mp : (List.range (globN s "journal_n")).map (fun k => memW post (globN s "journal" + 32 * k)) =
          (List.range (globN s "journal_n")).map (fun k => memW s (globN s "journal" + 32 * k)) := by
        apply List.map_congr_left; intro k hk; rw [List.mem_range] at hk
        have hjc_le := hWT.2.1.1
        have hjc_ne : globN s "journal_cap" ≠ 0 := by omega
        rcases hWT.2.1.2.2.1 with h0 | ⟨hal, _⟩
        · exact absurd h0 hjc_ne
        · have hbnd := allocated_le_2pow64 hAs.2 hal; dsimp only at hbnd
          have hkle : 32 * k + 8 ≤ 32 * globN s "journal_cap" := by omega
          exact memW_eq_of_cellHits hcell (by omega) (mem_worldTypedIvls_journal (S := S) (Nd := Nd_at) hjc_ne)
            ⟨by dsimp only; omega, by dsimp only; omega⟩
      dsimp only
      rw [hglob_eq "bs" (by decide), hglob_eq "ts" (by decide),
          hws_sl, hbs_sl, hts_sl, hnest_bs, hnest_ts, hbal_fl, hjrn_mp]
    have hdelEx_iff : ∀ i t, DelExclusive post S (evmChain s) i t ↔ DelExclusive s S (evmChain s) i t := by
      intro i t; unfold DelExclusive; rw [hworldRefs_eq]
      refine and_congr Iff.rfl (forall_congr' fun j => forall_congr' fun hj =>
        forall_congr' fun k => imp_congr_right fun hk => ?_)
      have hj_mem : (evmChain s)[j] ∈ evmChain s := List.getElem_mem _
      have hk_ok : k + 8 ≤ 280 ∧ k % 8 = 0 ∧ k ≠ 32 ∧ k ≠ 40 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl <;> exact ⟨by omega, by omega, by omega, by omega⟩
      rw [(hrec_eq _ hj_mem).1 k hk_ok.1 hk_ok.2.1 hk_ok.2.2.1 hk_ok.2.2.2]
    intro i hi
    have hi_mem : (evmChain s)[i]'(by omega) ∈ evmChain s := List.getElem_mem _
    have hm_eq := (hrec_eq _ hi_mem).2.1 48 (by omega) (by omega)
    have hmm_eq := (hrec_eq _ hi_mem).2.1 56 (by omega) (by omega)
    have he24_eq := (hrec_eq _ hi_mem).1 24 (by omega) (by omega) (by omega) (by omega)
    have htake_eq : ((evmChain s).take (i + 1)).map (fun ec => memW post (ec.1 + 136)) =
        ((evmChain s).take (i + 1)).map (fun ec => memW s (ec.1 + 136)) := by
      apply List.map_congr_left; intro ec hec
      exact (hrec_eq ec (List.mem_of_mem_take hec)).1 136 (by omega) (by omega) (by omega) (by omega)
    have hM := hMarks i hi; dsimp only at hM ⊢
    rw [hm_eq, hmm_eq, he24_eq, hfeq, htake_eq]
    obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9⟩ := hM
    refine ⟨m1, m2, m3, m4, ?_, ?_, m7, ?_, m9⟩
    · intro j hj hij
      have hj_tail : (evmChain s)[j] ∈ chTail := by
        rcases j with _ | j'
        · omega
        · simp [hch_eq]
      have hj_mem : (evmChain s)[j] ∈ evmChain s := List.getElem_mem _
      rw [hfs_eq _ hj_mem, htail_fo_eq _ hj_tail, hframeLogs_eq _ hj_mem,
          (hrec_eq _ hj_mem).1 112 (by omega) (by omega) (by omega) (by omega)]
      exact m5 j hj hij
    · rw [hfs_eq _ hi_mem]; exact m6
    · intro t ht
      rw [hfp_eq_all t ht, hdelEx_iff i t]; exact m8 t ht
  · rw [worldRoleSlots_eq hAs.2 hWT.1 hWT.2.2.1 hcell hcg,
        hframeRoleSlots_eq,
        journalRoleSlots_eq hAs.2 hWT.2.1 hWT.2.2.1 hcell hcg]
    unfold RolesOK at hRoles ⊢
    refine ⟨fun a ha => ?_, hRoles.2⟩
    obtain ⟨haS, hkl⟩ := hRoles.1 a ha
    have htb := ((hWT.1.2.1 a.1 haS).1.1 (a.1, 88) (by simp [htabFootprint])).1
    rw [htab_hdr_eq hcell haS htb 0 (by omega)]; exact ⟨haS, hkl⟩
  · have hsum_eq : ((evmChain s).map fun ec => memW post (ec.1 + 64) + memW post (ec.1 + 192)).sum =
        ((evmChain s).map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)).sum := by
      unfold R11Shards.OpDispatchSpec.evmR at hR_eq; rw [hchain_eq] at hR_eq; exact hR_eq
    rw [hsum_eq]; exact hGas

theorem epsA_extend_memory :
    EvmPreservingSpecA Group10.ExtendMemoryPre
      (fun s _ post => ∀ g : String, ofString g ≠ ofString "frame_mem_ptr" → globN post g = globN s g)
      (ofString "extend_memory") := by
  refine ⟨_, _, _, Group10.lookup_extend_memory, ?_⟩
  intro F s hcode hInv hHMWF ⟨ebw, heb_loc, heb_cond⟩ _ hnt
  have herr_triv : ∀ {P1 P2 : Prop},
      (∀ v, (some PanSemResultExact.error : Option (PanSemResultExact 64)) = some (.returned v) → P1) ∧
      (IsEvmErr (some PanSemResultExact.error) → P2) := by
    intro _ _; constructor
    · intro _ h; cases h
    · rintro ⟨_, h⟩; cases h
  have hhead_mem : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by simp [evmChain, evmChainFrom]
  have hFW0 := hInv.2.choose_spec.2.2.2.2.1 _ hhead_mem
  have hb_ev := (frameWF_bounds hInv.1.2 hFW0).1
  dsimp only at hb_ev
  have hev_pos : 0 < globN s "ev" := by
    obtain ⟨hin1, _⟩ := (hFW0.1 (globN s "ev", 280) (by simp)).1
    have h1 := hInv.1.2.2.2.1; have h2 := hInv.1.2.2.2.2.1
    rw [R11Shards.scratchStart_val] at h1; dsimp only at hin1; omega
  obtain ⟨evw, hevw, hevw_nat⟩ := global_word_of_pos s "ev" hev_pos
  obtain ⟨hp_w, fp_w, sp_g_w, hhp_lk, hhp_nat, hfp_lk, hfp_nat, hsp_g_lk, hsp_g_nat⟩ :=
    Wave8Contracts.M26.arenaOK_globals s hInv.1.2
  let growBranch : ProgHOL 64 :=
    .dec (ofString "ncap") .one (.panop .mul [.var .local (ofString "cap"), .const 2#64])
      (.seq
        (.ite (.cmp .lower (.var .local (ofString "ncap")) (.var .local (ofString "nlen")))
          (.assign .local (ofString "ncap") (.op .add [.var .local (ofString "nlen"), .const 1024#64]))
          .skip)
        (.seq
          (.call (some (none, none)) (ofString "frame_mem_alloc")
            [.op .sub [.var .local (ofString "ncap"), .var .local (ofString "cap")]])
          (.seq
            (.call (some (none, none)) (ofString "memzero")
              [.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]), .var .local (ofString "cap")],
               .op .sub [.var .local (ofString "ncap"), .var .local (ofString "cap")]])
            (.store (.op .add [.var .global (ofString "ev"), .const 40#64]) (.var .local (ofString "ncap"))))))
  let tailProg : ProgHOL 64 :=
    .seq
      (.call (some (none, none)) (ofString "memzero")
        [.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]), .var .local (ofString "len")],
         .var .local (ofString "expand_by")])
      (.seq
        (.store (.op .add [.var .global (ofString "ev"), .const 32#64]) (.var .local (ofString "nlen")))
        (.return (.const 0#64)))
  have hbody : sourceFnBody Guest.Software.guestFn_extend_memory =
      .seq
        (.ite (.cmp .equal (.var .local (ofString "expand_by")) (.const 0#64))
          (.return (.const 0#64))
          .skip)
        (.dec (ofString "len") .one (.load .one (.op .add [.var .global (ofString "ev"), .const 32#64]))
          (.dec (ofString "cap") .one (.load .one (.op .add [.var .global (ofString "ev"), .const 40#64]))
            (.dec (ofString "nlen") .one (.op .add [.var .local (ofString "len"), .var .local (ofString "expand_by")])
              (.seq
                (.ite (.cmp .lower (.var .local (ofString "cap")) (.var .local (ofString "nlen")))
                  growBranch
                  .skip)
                tailProg)))) := rfl
  dsimp only
  rw [hbody] at hnt ⊢
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt ⊢
  have hcmp_eb0 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .equal (.var .local (ofString "expand_by")) (.const 0#64)) =
      some (.val (.word (if ebw = 0#64 then 1 else 0))) := by
    simp [evalHOLExact, heb_loc, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  rw [hcmp_eb0] at hnt ⊢; dsimp only at hnt ⊢
  have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
  by_cases heb0 : ebw = 0#64
  · simp only [heb0, ↓reduceIte, h10] at hnt ⊢
    rw [evaluateHOLFiniteState_return]
    have hc0 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) (.const 0#64) =
        some (.val (.word 0#64)) := rfl
    rw [hc0]; dsimp only
    have hsz0 : sizeOfShapeWithContextHOL s.structs
        (shapeOfHOLExact (.val (.word 0#64))) ≤ 32 := by
      simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
    rw [if_pos hsz0]; dsimp only
    have hInv_el : EvmInv s.emptyLocalsHOLFinite := localsFree_evmInv s _ s.clock hInv
    have hHMWF_el : Group10.HeadMemChainWF s.emptyLocalsHOLFinite :=
      Group10.headMemChainWF_locals s _ s.clock hHMWF
    have hc_el := evm_congr (s := s) (t := s.emptyLocalsHOLFinite) rfl rfl
    have hch_el : evmChain s.emptyLocalsHOLFinite = evmChain s := evmChain_congr rfl rfl
    exact ⟨fun _ _ => ⟨⟨hInv_el, hHMWF_el⟩, hch_el, le_of_eq hc_el.2.1, fun _ _ => rfl⟩,
           by rintro ⟨_, h⟩; cases h⟩
  · rcases heb_cond with rfl | ⟨hnlen_bound, hnlen_al32, hmem_end_fp⟩
    · exact absurd rfl heb0
    have hnlen_al8 : (memW s (globN s "ev" + 32) + ebw.toNat) % 8 = 0 := by omega
    have heb_pos : 0 < ebw.toNat := by
      by_contra hz
      apply heb0
      apply BitVec.eq_of_toNat_eq
      have : (0#64 : BitVec 64).toNat = 0 := rfl
      omega
    simp only [heb0, ↓reduceIte, evaluateHOLFiniteState_skip] at hnt ⊢
    rw [evaluateHOLFiniteState_dec_total] at hnt ⊢; dsimp only at hnt ⊢
    rcases hload_len : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.load .one (.op .add [.var .global (ofString "ev"), .const 32#64])) with _ | vlen
    · exact herr_triv
    · simp only [hload_len] at hnt ⊢
      obtain ⟨lenw, rfl, hlenw_eq⟩ := evalAt_loadG_word s "ev" 32#64 vlen hload_len
      have h32_n : (32#64 : BitVec 64).toNat = 32 := rfl
      rw [h32_n] at hlenw_eq
      have hsh_len : shapeEqHOL .one (shapeOfHOLExact (.val (.word lenw))) = true := by
        simp [shapeEqHOL, shapeOfHOLExact]
      rw [if_pos hsh_len] at hnt ⊢; dsimp only at hnt ⊢
      set s1 := setVarHOLFinite (ofString "len") (.val (.word lenw)) s with hs1
      rw [evaluateHOLFiniteState_dec_total] at hnt ⊢; dsimp only at hnt ⊢
      rcases hload_cap : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
          (.load .one (.op .add [.var .global (ofString "ev"), .const 40#64])) with _ | vcap
      · exact herr_triv
      · simp only [hload_cap] at hnt ⊢
        obtain ⟨capw, rfl, hcapw_eq⟩ := evalAt_loadG_word s1 "ev" 40#64 vcap hload_cap
        have h40_n : (40#64 : BitVec 64).toNat = 40 := rfl
        have hs1_gm : memW s1 (globN s1 "ev" + 40) = memW s (globN s "ev" + 40) := rfl
        rw [h40_n, hs1_gm] at hcapw_eq
        have hsh_cap : shapeEqHOL .one (shapeOfHOLExact (.val (.word capw))) = true := by
          simp [shapeEqHOL, shapeOfHOLExact]
        rw [if_pos hsh_cap] at hnt ⊢; dsimp only at hnt ⊢
        set s2 := setVarHOLFinite (ofString "cap") (.val (.word capw)) s1 with hs2
        have hs2_len : s2.locals.lookup (ofString "len") = some (.val (.word lenw)) := by
          simp [hs2, hs1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "cap" ≠ ofString "len" by decide]
        have hs2_cap : s2.locals.lookup (ofString "cap") = some (.val (.word capw)) := by
          simp [hs2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have hs2_eb : s2.locals.lookup (ofString "expand_by") = some (.val (.word ebw)) := by
          simp [hs2, hs1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, heb_loc,
            show ofString "cap" ≠ ofString "expand_by" by decide,
            show ofString "len" ≠ ofString "expand_by" by decide]
        rw [evaluateHOLFiniteState_dec_total] at hnt ⊢; dsimp only at hnt ⊢
        have hnlen_ev : @evalHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a))
            (.op .add [.var .local (ofString "len"), .var .local (ofString "expand_by")]) =
            some (.val (.word (lenw + ebw))) := by
          simp [evalHOLExact, evalListHOLExact, hs2_len, hs2_eb, wordOpHOL, wordOp, valueIsWord, valueWord]
        rw [hnlen_ev] at hnt ⊢; dsimp only at hnt ⊢
        set nlenw := lenw + ebw
        have hnlenw_nat : nlenw.toNat = lenw.toNat + ebw.toNat := by
          rw [BitVec.toNat_add, hlenw_eq, Nat.mod_eq_of_lt (by omega)]
        have hnlenw_al32 : nlenw.toNat % 32 = 0 := by
          rw [hnlenw_nat, hlenw_eq]; exact hnlen_al32
        have hsh_nlen : shapeEqHOL .one (shapeOfHOLExact (.val (.word nlenw))) = true := by
          simp [shapeEqHOL, shapeOfHOLExact]
        rw [if_pos hsh_nlen] at hnt ⊢; dsimp only at hnt ⊢
        set s3 := setVarHOLFinite (ofString "nlen") (.val (.word nlenw)) s2 with hs3
        have hs3_nlen : s3.locals.lookup (ofString "nlen") = some (.val (.word nlenw)) := by
          simp [hs3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have hs3_len : s3.locals.lookup (ofString "len") = some (.val (.word lenw)) := by
          simp [hs3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs2_len,
            show ofString "nlen" ≠ ofString "len" by decide]
        have hs3_cap : s3.locals.lookup (ofString "cap") = some (.val (.word capw)) := by
          simp [hs3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs2_cap,
            show ofString "nlen" ≠ ofString "cap" by decide]
        have hs3_eb : s3.locals.lookup (ofString "expand_by") = some (.val (.word ebw)) := by
          simp [hs3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs2_eb,
            show ofString "nlen" ≠ ofString "expand_by" by decide]
        have hmem_in : Inside (memW s (globN s "ev" + 24), memW s (globN s "ev" + 40)) scratchStart (globN s "frame_mem_ptr") :=
          hFW0.2.1
        have hmem_wok := hFW0.2.2.1
        have hmem24_8 : memW s (globN s "ev" + 24) % 8 = 0 := hmem_wok.1
        have hmem40_8 : memW s (globN s "ev" + 40) % 8 = 0 := hmem_wok.2.1
        have hfp_le_se : globN s "frame_mem_ptr" ≤ scratchEnd :=
          le_trans hInv.1.2.2.2.2.1 hInv.1.2.2.2.2.2.1
        have hse_val := R11Shards.scratchEnd_val
        have hss_val := R11Shards.scratchStart_val
        have hcap_lt : capw.toNat < 2 ^ 30 := by
          dsimp only [Inside] at hmem_in; omega
        have hlen_le_cap0 : lenw.toNat ≤ capw.toNat := by
          rw [hlenw_eq, hcapw_eq]; exact hFW0.2.2.2.2.2.2.1
        have run_tail : ∀ (m : PanSemStateFiniteExact 64 F) (freshIvl : Ivl),
            ArenaReady m →
            globN s "frame_mem_ptr" ≤ globN m "frame_mem_ptr" →
            (∀ g : String, ofString g ≠ ofString "frame_mem_ptr" → m.globals.lookup (ofString g) = s.globals.lookup (ofString g)) →
            FrameMemByteEffG10 s m [freshIvl, (globN s "ev", 280), (memW s (globN s "ev" + 24), memW s (globN s "ev" + 40))] →
            (freshIvl = (0, 0) ∨
              (freshIvl.1 % 8 = 0 ∧ freshIvl.2 % 8 = 0 ∧
                Inside freshIvl (globN s "frame_mem_ptr") (globN m "frame_mem_ptr"))) →
            (∀ off, off + 8 ≤ 280 → off % 8 = 0 → off ≠ 32 → off ≠ 40 →
              memW m (globN s "ev" + off) = memW s (globN s "ev" + off)) →
            ((freshIvl.2 = 0 ∧ memW m (globN s "ev" + 40) = memW s (globN s "ev" + 40) ∧
                globN m "frame_mem_ptr" = globN s "frame_mem_ptr") ∨
              (freshIvl.2 ≠ 0 ∧
                memW s (globN s "ev" + 24) + memW s (globN s "ev" + 40) = freshIvl.1 ∧
                memW m (globN s "ev" + 40) = memW s (globN s "ev" + 40) + freshIvl.2 ∧
                globN m "frame_mem_ptr" = freshIvl.1 + freshIvl.2)) →
            nlenw.toNat ≤ memW m (globN s "ev" + 40) →
            m.locals.lookup (ofString "len") = some (.val (.word lenw)) →
            m.locals.lookup (ofString "nlen") = some (.val (.word nlenw)) →
            m.locals.lookup (ofString "expand_by") = some (.val (.word ebw)) →
            (evaluateHOLFiniteState m tailProg).1 ≠ some .timeOut →
            let out := evaluateHOLFiniteState m tailProg
            let post := { out.2 with
              locals := ((out.2.locals.resVarEq (ofString "nlen", s2.locals.lookup (ofString "nlen"))).resVarEq
                (ofString "cap", s1.locals.lookup (ofString "cap"))).resVarEq
                (ofString "len", s.locals.lookup (ofString "len")) }
            (∀ v, out.1 = some (.returned v) →
              (EvmInv post ∧ Group10.HeadMemChainWF post) ∧ evmChain post = evmChain s ∧ evmR post ≤ evmR s ∧
              (∀ g : String, ofString g ≠ ofString "frame_mem_ptr" → globN post g = globN s g)) ∧
            (IsEvmErr out.1 →
              (EvmInv post ∧ Group10.HeadMemChainWF post) ∧ evmChain post = evmChain s ∧ evmR post ≤ evmR s) := by
          intro m freshIvl hAm hfm_m hm_glob_other heff_m hfresh_m he0_m hnew_m hnlen_le_mcap hm_len hm_nlen hm_eb hnt_t
          dsimp only [tailProg] at hnt_t ⊢
          have hm_ev : m.globals.lookup (ofString "ev") = some (.val (.word evw)) := by
            rw [hm_glob_other "ev" (by decide)]; exact hevw
          have hm_code : m.code = originalRuntimeCode := heff_m.code.trans hcode
          have hm_ma : m.memaddrs = ordinaryDomain := hAm.1.memaddrs
          have hm_dom24 : m.memaddrs (evw + 24#64) := by
            rw [hm_ma, ← hInv.1.1.memaddrs]
            have hev24_eq : evw + 24#64 = BitVec.ofNat 64 (globN s "ev" + 24) := by
              apply BitVec.eq_of_toNat_eq
              have : (24#64 : BitVec 64).toNat = 24 := rfl
              rw [BitVec.toNat_add, hevw_nat, this, BitVec.toNat_ofNat]
            rw [hev24_eq]
            exact ((hFW0.1 (globN s "ev", 280) (by simp)).2.2.2 3 (by omega)).choose_spec.1
          rcases hm_m24 : m.memory (evw + 24#64) with ⟨memPtrW⟩
          have hmemPtrW_nat : memPtrW.toNat = memW s (globN s "ev" + 24) := by
            have hev24_eq : evw + 24#64 = BitVec.ofNat 64 (globN s "ev" + 24) := by
              apply BitVec.eq_of_toNat_eq
              have : (24#64 : BitVec 64).toNat = 24 := rfl
              rw [BitVec.toNat_add, hevw_nat, this, BitVec.toNat_ofNat]
            have hm24_eq := he0_m 24 (by omega) (by omega) (by omega) (by omega)
            have hm24_lhs : memW m (globN s "ev" + 24) = memPtrW.toNat := by
              unfold memW; rw [← hev24_eq, hm_m24]
            rw [← hm24_lhs, hm24_eq]
          let mzDstExp : ExpHOL 64 :=
            .op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]), .var .local (ofString "len")]
          have hev_mz_dst : @evalHOLExact 64 F _ m.toExact (fun a => Classical.propDecidable (m.memaddrs a)) mzDstExp =
              some (.val (.word (memPtrW + lenw))) := by
            simp [mzDstExp, evalHOLExact, evalListHOLExact, hm_ev, hm_len, wordOpHOL, wordOp,
              valueIsWord, valueWord, memLoadHOLExact, hm_dom24, hm_m24]
          have hev_mz_n : @evalHOLExact 64 F _ m.toExact (fun a => Classical.propDecidable (m.memaddrs a))
              (.var .local (ofString "expand_by")) = some (.val (.word ebw)) := hm_eb
          have hmcap_bound : memW s (globN s "ev" + 24) + memW m (globN s "ev" + 40) ≤ scratchEnd := by
            rcases hnew_m with ⟨_, h40_eq, _⟩ | ⟨hnz, hfr1, h40_eq, _⟩
            · rw [h40_eq]; dsimp only [Inside] at hmem_in; omega
            · rcases hfresh_m with rfl | ⟨_, _, _, hfin2⟩
              · exact absurd rfl hnz
              · have hm_fp_se : globN m "frame_mem_ptr" ≤ scratchEnd :=
                  le_trans hAm.2.2.2.2.1 hAm.2.2.2.2.2.1
                omega
          have hdst_nat : (memPtrW + lenw).toNat = memW s (globN s "ev" + 24) + lenw.toNat := by
            rw [BitVec.toNat_add, hmemPtrW_nat, Nat.mod_eq_of_lt (by omega)]
          let combinedMem : Ivl := (memW s (globN s "ev" + 24), memW m (globN s "ev" + 40))
          let mzTailCall : ProgHOL 64 := .call (some (none, none)) (ofString "memzero") [mzDstExp, .var .local (ofString "expand_by")]
          rw [evaluateHOLFiniteState_seq_line780] at hnt_t ⊢
          have hnt_mz : (evaluateHOLFiniteState m mzTailCall).1 ≠ some .timeOut := by
            intro hto
            rcases hmz_to : evaluateHOLFiniteState m
                (.call (some (none, none)) (ofString "memzero") [mzDstExp, .var .local (ofString "expand_by")]) with ⟨rmz_to, smz_to⟩
            have hto' : rmz_to = some .timeOut := by
              dsimp only [mzTailCall] at hto; rw [hmz_to] at hto; exact hto
            subst hto'
            have hmz_to_raw : evaluateHOLFiniteState m
                (.call (some (none, none)) (ofString "memzero")
                  [.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]), .var .local (ofString "len")],
                   .var .local (ofString "expand_by")]) = (some .timeOut, smz_to) := hmz_to
            simp only [hmz_to_raw] at hnt_t
            exact hnt_t rfl
          have hmz := eval_call_memzero_bre_g10 m mzDstExp (.var .local (ofString "expand_by"))
            (memPtrW + lenw) ebw [combinedMem] hm_code hm_ma hev_mz_dst hev_mz_n
            (fun _ => ⟨combinedMem, by simp, by rw [hdst_nat]; dsimp only [combinedMem]; omega,
              by rw [hdst_nat]; dsimp only [combinedMem]; omega⟩) hnt_mz
          dsimp only at hmz
          rcases hmz_run : evaluateHOLFiniteState m mzTailCall with ⟨rmz, m1⟩
          rw [hmz_run] at hmz
          have hmz_run_raw : evaluateHOLFiniteState m
              (.call (some (none, none)) (ofString "memzero")
                [.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]), .var .local (ofString "len")],
                 .var .local (ofString "expand_by")]) = (rmz, m1) := hmz_run
          simp only [hmz_run_raw] at hnt_t ⊢
          cases rmz with
          | some rmz0 =>
            dsimp only at hnt_t ⊢
            have hnr := hmz.2 (by simp)
            refine ⟨fun v hv => absurd (Or.inl ⟨v, hv⟩) hnr, ?_⟩
            rintro ⟨ev, hv⟩
            injection hv with hv'; subst hv'
            exact absurd (Or.inr ⟨ofString "EvmErr", ev, rfl, by decide⟩) hnr
          | none =>
            dsimp only at hnt_t ⊢
            obtain ⟨heff_mz_comb, hm1_loc⟩ := hmz.1 rfl
            have heff_mz : FrameMemByteEffG10 m m1
                [freshIvl, (globN s "ev", 280), (memW s (globN s "ev" + 24), memW s (globN s "ev" + 40))] := by
              refine ⟨heff_mz_comb.code, heff_mz_comb.memaddrs, heff_mz_comb.shMemaddrs,
                heff_mz_comb.baseAddr, heff_mz_comb.be, fun _ _ => by rw [heff_mz_comb.globals],
                heff_mz_comb.out_dom, ?_, ?_⟩
              · intro a ha
                apply heff_mz_comb.cell_frame a
                intro i hi hch
                simp at hi; subst hi
                obtain ⟨hc1, hc2⟩ := hch
                dsimp only [combinedMem] at hc1 hc2
                rcases hnew_m with ⟨_, h40_eq, _⟩ | ⟨hnz, hfr1, h40_eq, _⟩
                · rw [h40_eq] at hc2
                  exact ha (memW s (globN s "ev" + 24), memW s (globN s "ev" + 40)) (by simp) ⟨hc1, hc2⟩
                · by_cases hsplit : a.toNat < memW s (globN s "ev" + 24) + memW s (globN s "ev" + 40)
                  · exact ha (memW s (globN s "ev" + 24), memW s (globN s "ev" + 40)) (by simp) ⟨hc1, hsplit⟩
                  · exact ha freshIvl (by simp) ⟨by omega, by omega⟩
              · intro b hb hno
                apply heff_mz_comb.byte_frame b hb
                intro i hi hin
                simp at hi; subst hi
                obtain ⟨hb1, hb2⟩ := hin
                dsimp only [combinedMem] at hb1 hb2
                rcases hnew_m with ⟨_, h40_eq, _⟩ | ⟨hnz, hfr1, h40_eq, _⟩
                · rw [h40_eq] at hb2
                  exact hno (memW s (globN s "ev" + 24), memW s (globN s "ev" + 40)) (by simp) ⟨hb1, hb2⟩
                · by_cases hsplit : b < memW s (globN s "ev" + 24) + memW s (globN s "ev" + 40)
                  · exact hno (memW s (globN s "ev" + 24), memW s (globN s "ev" + 40)) (by simp) ⟨hb1, hsplit⟩
                  · exact hno freshIvl (by simp) ⟨by omega, by omega⟩
            have hm1_e0_eq : ∀ off, off + 8 ≤ 280 → off % 8 = 0 →
                memW m1 (globN s "ev" + off) = memW m (globN s "ev" + off) := by
              intro off hoff hoff8
              unfold memW
              rw [heff_mz_comb.cell_frame (BitVec.ofNat 64 (globN s "ev" + off))]
              intro x hx
              simp at hx; subst hx
              have htn : (BitVec.ofNat 64 (globN s "ev" + off)).toNat = globN s "ev" + off :=
                Nat.mod_eq_of_lt (by omega)
              rw [htn]
              have he0_8 : (globN s "ev") % 8 = 0 := (hFW0.1 (globN s "ev", 280) (by simp)).2.1
              have ha8 : (globN s "ev" + off) % 8 = 0 := by omega
              rcases hnew_m with ⟨_, h40_eq, _⟩ | ⟨hnz, hfr1, h40_eq, _⟩
              · dsimp only [combinedMem]; rw [h40_eq]
                have hpw_fo := hInv.2.choose_spec.2.2.2.2.2.2.2.1
                have hch_s : ∃ tl, evmChain s = (globN s "ev", globN s "cur_cont") :: tl := ⟨_, rfl⟩
                obtain ⟨tl_s, hch_s_eq⟩ := hch_s
                rw [hch_s_eq, List.map_cons, List.flatten_cons, List.pairwise_append] at hpw_fo
                have hd_mem : Disj (globN s "ev", 280) (memW s (globN s "ev" + 24), memW s (globN s "ev" + 40)) := by
                  have hp0 := hpw_fo.1; unfold frameObjects at hp0
                  exact (List.pairwise_cons.1 hp0).1 _ (by simp)
                exact not_cellHits_of_disj_aligned (i := (globN s "ev", 280)) ha8 hmem24_8
                  (Nat.le_add_right _ off) (Nat.add_le_add_left hoff _) hd_mem
              · rcases hfresh_m with rfl | ⟨_, _, _, hfin2⟩
                · exact absurd rfl hnz
                · obtain ⟨he0_scr, _⟩ := (hFW0.1 (globN s "ev", 280) (by simp)).1
                  have hfp_le_scr : globN m "frame_mem_ptr" ≤ globN s "scratch_ptr" := by
                    have hle_m := hAm.2.2.2.2.1
                    have hsp_eq := OpHandlers.globN_eq_of_lookup_eq (hm_glob_other "scratch_ptr" (by decide))
                    omega
                  exact not_cellHits_of_disj_aligned (i := (globN s "ev", 280)) ha8 hmem24_8
                    (Nat.le_add_right _ off) (Nat.add_le_add_left hoff _)
                    (Or.inr (Or.inr (Or.inr (by dsimp only [combinedMem, Inside] at he0_scr hfin2 ⊢; omega))))
            rw [evaluateHOLFiniteState_seq_line780] at hnt_t ⊢
            rcases hst32 : evaluateHOLFiniteState m1
                (.store (.op .add [.var .global (ofString "ev"), .const 32#64]) (.var .local (ofString "nlen"))) with ⟨rst32, m2⟩
            simp only [hst32] at hnt_t ⊢
            cases rst32 with
            | some res32 =>
              have herr := store_some_eq_error_g10 hst32; subst herr; dsimp only; exact herr_triv
            | none =>
              dsimp only at hnt_t ⊢
              have hm1_ev : m1.globals.lookup (ofString "ev") = some (.val (.word evw)) := by
                rw [heff_mz_comb.globals]; exact hm_ev
              have hm1_nlen : m1.locals.lookup (ofString "nlen") = some (.val (.word nlenw)) := by
                rw [hm1_loc]; exact hm_nlen
              obtain ⟨w_nl', hw_nl_ev, hm2_eq⟩ := R14Shards.OpHandlersA.store_global_off_word (t := m1) (post := m2)
                (gname := "ev") (gbase := globN s "ev") (off := 32) hm1_ev hevw_nat (by omega)
                (fun v hv => by
                  change m1.locals.lookup (ofString "nlen") = some v at hv
                  rw [hm1_nlen] at hv; injection hv with hv'; exact ⟨nlenw, hv'.symm⟩) hst32
              have hw_nl_val : nlenw = w_nl' := by
                change m1.locals.lookup (ofString "nlen") = some (.val (.word w_nl')) at hw_nl_ev
                rw [hm1_nlen] at hw_nl_ev
                injection hw_nl_ev with h1; injection h1 with h2; injection h2 with h3
              subst w_nl'
              have heff_st32 := (ByteRegionEffect.of_store_word (Rl := [(globN s "ev", 280)])
                (heff_mz_comb.memaddrs.trans hm_ma) hst32
                (fun v hv => by
                  change m1.locals.lookup (ofString "nlen") = some v at hv
                  rw [hm1_nlen] at hv; injection hv with hv'; exact ⟨nlenw, hv'.symm⟩)
                (fun addr hdst _ => by
                  simp [evalHOLExact, evalListHOLExact, hm1_ev, wordOpHOL, wordOp, valueIsWord, valueWord] at hdst
                  have h32_eq : (evw + 32#64).toNat = globN s "ev" + 32 := by
                    have : (32#64 : BitVec 64).toNat = 32 := rfl
                    rw [BitVec.toNat_add, hevw_nat, this, Nat.mod_eq_of_lt (by omega)]
                  exact ⟨(globN s "ev", 280), by simp, by rw [← hdst, h32_eq]; dsimp only; omega,
                    by rw [← hdst, h32_eq]; dsimp only; omega⟩)).1
              have heff_st32_fm0 : FrameMemByteEffG10 m1 m2 [(globN s "ev", 280)] :=
                ⟨heff_st32.code, heff_st32.memaddrs, heff_st32.shMemaddrs, heff_st32.baseAddr,
                 heff_st32.be, fun _ _ => by rw [heff_st32.globals],
                 heff_st32.out_dom, heff_st32.cell_frame, heff_st32.byte_frame⟩
              have heff_st32_fm : FrameMemByteEffG10 m1 m2
                  [freshIvl, (globN s "ev", 280), (memW s (globN s "ev" + 24), memW s (globN s "ev" + 40))] :=
                heff_st32_fm0.mono (fun x hx => by
                  simp at hx; subst hx; exact ⟨(globN s "ev", 280), by simp, le_refl _, le_refl _⟩)
              rw [evaluateHOLFiniteState_return]
              have hc0_m2 : @evalHOLExact 64 F _ m2.toExact (fun a => Classical.propDecidable (m2.memaddrs a)) (.const (0 : BitVec 64)) =
                  some (.val (.word 0)) := rfl
              have hc0_m2' : @evalHOLExact 64 F _ m2.toExact (fun a => Classical.propDecidable (m2.memaddrs a)) (.const 0#64) =
                  some (.val (.word 0#64)) := rfl
              simp only [hc0_m2, hc0_m2']
              have hsz0 : sizeOfShapeWithContextHOL m2.structs
                  (shapeOfHOLExact (.val (.word (0 : BitVec 64)))) ≤ 32 := by
                simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
              have hsz0' : sizeOfShapeWithContextHOL m2.structs
                  (shapeOfHOLExact (.val (.word 0#64))) ≤ 32 := by
                simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
              simp only [hsz0, hsz0', ↓reduceIte]
              let post := { m2.emptyLocalsHOLFinite with
                locals := ((m2.emptyLocalsHOLFinite.locals.resVarEq (ofString "nlen", s2.locals.lookup (ofString "nlen"))).resVarEq
                  (ofString "cap", s1.locals.lookup (ofString "cap"))).resVarEq
                  (ofString "len", s.locals.lookup (ofString "len")) }
              have heff_total0 := (heff_m.trans heff_mz).trans heff_st32_fm
              have heff_total : FrameMemByteEffG10 s post
                  [freshIvl, (globN s "ev", 280), (memW s (globN s "ev" + 24), memW s (globN s "ev" + 40))] :=
                ⟨heff_total0.code, heff_total0.memaddrs, heff_total0.shMemaddrs, heff_total0.baseAddr,
                 heff_total0.be, heff_total0.glob_other, heff_total0.out_dom, heff_total0.cell_frame, heff_total0.byte_frame⟩
              have hm1_glob_m : m1.globals = m.globals := heff_mz_comb.globals
              have hm1_code_m : m1.code = m.code := heff_mz_comb.code
              have hm1_ma_m : m1.memaddrs = m.memaddrs := heff_mz_comb.memaddrs
              have hm1_sh_m : m1.shMemaddrs = m.shMemaddrs := heff_mz_comb.shMemaddrs
              have hm1_ba_m : m1.baseAddr = m.baseAddr := heff_mz_comb.baseAddr
              have hpost_glob_m : post.globals = m.globals := by
                simp [post, emptyLocalsHOLFinite, hm2_eq, hm1_glob_m]
              have hApost : ArenaReady post :=
                ⟨guestInv_congr (s := m) (by simp [post, emptyLocalsHOLFinite, hm2_eq, hm1_code_m])
                  (by simp [post, emptyLocalsHOLFinite, hm2_eq, hm1_ma_m])
                  (by simp [post, emptyLocalsHOLFinite, hm2_eq, hm1_sh_m])
                  (by simp [post, emptyLocalsHOLFinite, hm2_eq, hm1_ba_m]) hAm.1,
                 arenaOK_congr hpost_glob_m hAm.2⟩
              have hfm_post : globN s "frame_mem_ptr" ≤ globN post "frame_mem_ptr" := by
                unfold globN; rw [hpost_glob_m]; exact hfm_m
              have hfresh_post : freshIvl = (0, 0) ∨
                  (freshIvl.1 % 8 = 0 ∧ freshIvl.2 % 8 = 0 ∧
                    Inside freshIvl (globN s "frame_mem_ptr") (globN post "frame_mem_ptr")) := by
                unfold globN; rw [hpost_glob_m]; exact hfresh_m
              have hm2_memW_ne32 : ∀ off, off + 8 ≤ 280 → off % 8 = 0 → off ≠ 32 →
                  memW post (globN s "ev" + off) = memW m (globN s "ev" + off) := by
                intro off hoff hoff8 hne32
                change memW m2 (globN s "ev" + off) = memW m (globN s "ev" + off)
                rw [hm2_eq, R14Shards.OpHandlersA.memW_updW_ne m1 (globN s "ev" + 32) (globN s "ev" + off) _ (by omega) (by omega) (by omega),
                    hm1_e0_eq off hoff hoff8]
              have hm2_memW_32 : memW post (globN s "ev" + 32) = nlenw.toNat := by
                change memW m2 (globN s "ev" + 32) = nlenw.toNat
                rw [hm2_eq, R14Shards.OpHandlersA.memW_updW_same m1 (globN s "ev" + 32) nlenw]
              have he0_post : ∀ off, off + 8 ≤ 280 → off % 8 = 0 → off ≠ 32 → off ≠ 40 →
                  memW post (globN s "ev" + off) = memW s (globN s "ev" + off) := by
                intro off hoff hoff8 h32 h40
                rw [hm2_memW_ne32 off hoff hoff8 h32, he0_m off hoff hoff8 h32 h40]
              have hfp_post_eq_m : globN post "frame_mem_ptr" = globN m "frame_mem_ptr" := by
                unfold globN; rw [hpost_glob_m]
              have hnew_post :
                  (freshIvl.2 = 0 ∧ memW post (globN s "ev" + 40) = memW s (globN s "ev" + 40) ∧
                    globN post "frame_mem_ptr" = globN s "frame_mem_ptr") ∨
                  (freshIvl.2 ≠ 0 ∧
                    memW s (globN s "ev" + 24) + memW s (globN s "ev" + 40) = freshIvl.1 ∧
                    memW post (globN s "ev" + 40) = memW s (globN s "ev" + 40) + freshIvl.2 ∧
                    globN post "frame_mem_ptr" = freshIvl.1 + freshIvl.2) := by
                rw [hm2_memW_ne32 40 (by omega) (by omega) (by omega), hfp_post_eq_m]
                exact hnew_m
              have hlen_le_cap_post : memW post (globN s "ev" + 32) ≤ memW post (globN s "ev" + 40) := by
                rw [hm2_memW_32, hm2_memW_ne32 40 (by omega) (by omega) (by omega)]
                exact hnlen_le_mcap
              have hlen_al32_post : memW post (globN s "ev" + 32) % 32 = 0 := by
                rw [hm2_memW_32]; exact hnlenw_al32
              obtain ⟨hInv_p, hHMWF_p, hch_p, hR_p⟩ := evmInv_of_head_mem_extend_g10 hInv hHMWF hApost hfm_post
                heff_total hfresh_post he0_post hnew_post hlen_le_cap_post hlen_al32_post
              constructor
              · intro _ _
                refine ⟨⟨hInv_p, hHMWF_p⟩, hch_p, le_of_eq hR_p, fun g hg => ?_⟩
                unfold globN; rw [hpost_glob_m]
                exact OpHandlers.globN_eq_of_lookup_eq (hm_glob_other g hg)
              · rintro ⟨_, h⟩; cases h
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt ⊢
        have hcmp_grow : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
            (.cmp .lower (.var .local (ofString "cap")) (.var .local (ofString "nlen"))) =
            some (.val (.word (if capw < nlenw then 1 else 0))) := by
          simp [evalHOLExact, hs3_cap, hs3_nlen, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
        rw [hcmp_grow] at hnt ⊢; dsimp only at hnt ⊢
        by_cases hgrow : capw < nlenw
        · have hcap_lt_nlen : capw.toNat < nlenw.toNat := BitVec.lt_def.1 hgrow
          simp only [hgrow, ↓reduceIte, h10] at hnt ⊢
          dsimp only [growBranch] at hnt ⊢
          rw [evaluateHOLFiniteState_dec_total] at hnt ⊢; dsimp only at hnt ⊢
          have hmul2 : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
              (.panop .mul [.var .local (ofString "cap"), .const 2#64]) =
              some (.val (.word (capw * 2#64))) := by
            simp [evalHOLExact, evalListHOLExact, hs3_cap, panOpHOL, valueIsWord, valueWord]
          rw [hmul2] at hnt ⊢; dsimp only at hnt ⊢
          have hsh_ncap : shapeEqHOL .one (shapeOfHOLExact (.val (.word (capw * 2#64)))) = true := by
            simp [shapeEqHOL, shapeOfHOLExact]
          rw [if_pos hsh_ncap] at hnt ⊢; dsimp only at hnt ⊢
          set s4 := setVarHOLFinite (ofString "ncap") (.val (.word (capw * 2#64))) s3 with hs4
          have hncap0_nat : (capw * 2#64).toNat = 2 * capw.toNat := by
            have : (2#64 : BitVec 64).toNat = 2 := rfl
            rw [BitVec.toNat_mul, this, Nat.mod_eq_of_lt (by omega)]; omega
          have hite_ncap : ∃ (s5 : PanSemStateFiniteExact 64 F) (ncapw : BitVec 64),
              evaluateHOLFiniteState s4
                (.ite (.cmp .lower (.var .local (ofString "ncap")) (.var .local (ofString "nlen")))
                  (.assign .local (ofString "ncap") (.op .add [.var .local (ofString "nlen"), .const 1024#64]))
                  .skip) = (none, s5) ∧
              s5 = { s with locals := s5.locals, clock := s.clock } ∧
              s5.locals.lookup (ofString "ncap") = some (.val (.word ncapw)) ∧
              s5.locals.lookup (ofString "cap") = some (.val (.word capw)) ∧
              s5.locals.lookup (ofString "len") = some (.val (.word lenw)) ∧
              s5.locals.lookup (ofString "nlen") = some (.val (.word nlenw)) ∧
              s5.locals.lookup (ofString "expand_by") = some (.val (.word ebw)) ∧
              nlenw.toNat ≤ ncapw.toNat ∧ capw.toNat < ncapw.toNat ∧
              ncapw.toNat < 2 ^ 38 ∧ ncapw.toNat % 8 = 0 := by
            have hnlenw_al8 : nlenw.toNat % 8 = 0 := by
              rw [hnlenw_nat, hlenw_eq]; exact hnlen_al8
            have hcapw_al8 : capw.toNat % 8 = 0 := by
              rw [hcapw_eq]; exact hmem40_8
            have hs4_ncap : s4.locals.lookup (ofString "ncap") = some (.val (.word (capw * 2#64))) := by
              simp [hs4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
            have hs4_nlen : s4.locals.lookup (ofString "nlen") = some (.val (.word nlenw)) := by
              simp [hs4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_nlen,
                show ofString "ncap" ≠ ofString "nlen" by decide]
            rw [evaluateHOLFiniteState_ite]
            have hcmp_nc : @evalHOLExact 64 F _ s4.toExact (fun a => Classical.propDecidable (s4.memaddrs a))
                (.cmp .lower (.var .local (ofString "ncap")) (.var .local (ofString "nlen"))) =
                some (.val (.word (if capw * 2#64 < nlenw then 1 else 0))) := by
              simp [evalHOLExact, hs4_ncap, hs4_nlen, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
            rw [hcmp_nc]; dsimp only
            by_cases hlt_nl : capw * 2#64 < nlenw
            · simp only [hlt_nl, ↓reduceIte, h10, evaluateHOLFiniteState_assign]
              have hev_add1024 : @evalHOLExact 64 F _ s4.toExact (fun a => Classical.propDecidable (s4.memaddrs a))
                  (.op .add [.var .local (ofString "nlen"), .const 1024#64]) =
                  some (.val (.word (nlenw + 1024#64))) := by
                simp [evalHOLExact, evalListHOLExact, hs4_nlen, wordOpHOL, wordOp, valueIsWord, valueWord]
              have hval_nc : s4.isValidValueHOLFinite .local (ofString "ncap") (.val (.word (nlenw + 1024#64))) = true := by
                simp [isValidValueHOLFinite, lookupKvarHOLFinite, hs4_ncap, shapeOfHOLExact, shapeEqHOL]
              rw [hev_add1024]; dsimp only; rw [if_pos hval_nc]
              let s5 := setKvarHOLFinite .local (ofString "ncap") (.val (.word (nlenw + 1024#64))) s4
              have h1024_n : (1024#64 : BitVec 64).toNat = 1024 := rfl
              have hnl1024_nat : (nlenw + 1024#64).toNat = nlenw.toNat + 1024 := by
                rw [BitVec.toNat_add, h1024_n, Nat.mod_eq_of_lt (by omega)]
              refine ⟨s5, nlenw + 1024#64, rfl, by cases s; rfl, ?_, ?_, ?_, ?_, ?_, by omega, by omega, by omega, by omega⟩
              · simp [s5, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
              · simp [s5, hs4, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_cap,
                  show ofString "ncap" ≠ ofString "cap" by decide]
              · simp [s5, hs4, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_len,
                  show ofString "ncap" ≠ ofString "len" by decide]
              · simp [s5, hs4, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_nlen,
                  show ofString "ncap" ≠ ofString "nlen" by decide]
              · simp [s5, hs4, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_eb,
                  show ofString "ncap" ≠ ofString "expand_by" by decide]
            · simp only [hlt_nl, ↓reduceIte, evaluateHOLFiniteState_skip]
              have hge_nl : nlenw.toNat ≤ (capw * 2#64).toNat := by
                rw [BitVec.lt_def] at hlt_nl; omega
              refine ⟨s4, capw * 2#64, rfl, by cases s; rfl, hs4_ncap, ?_, ?_, hs4_nlen, ?_, hge_nl, by omega, by omega, by omega⟩
              · simp [hs4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_cap,
                  show ofString "ncap" ≠ ofString "cap" by decide]
              · simp [hs4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_len,
                  show ofString "ncap" ≠ ofString "len" by decide]
              · simp [hs4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_eb,
                  show ofString "ncap" ≠ ofString "expand_by" by decide]
          obtain ⟨s5, ncapw, hs5_run, hs5_eq, hs5_ncap, hs5_cap, hs5_len, hs5_nlen, hs5_eb,
            hnlen_le_ncap, hcap_lt_ncap, hncap_lt, hncap_al8⟩ := hite_ncap
          rw [evaluateHOLFiniteState_seq_line780, hs5_run] at hnt ⊢; dsimp only at hnt ⊢
          set diffw := ncapw - capw
          have hdiff_nat : diffw.toNat = ncapw.toNat - capw.toNat :=
            BitVec.toNat_sub_of_le (BitVec.le_def.2 (Nat.le_of_lt hcap_lt_ncap))
          rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_call] at hnt ⊢
          have hs5_code : s5.code = originalRuntimeCode := by rw [hs5_eq]; exact hcode
          have hargs_fma : evalListHOLFinite s5 (h := fun a => Classical.propDecidable (s5.memaddrs a))
              [.op .sub [.var .local (ofString "ncap"), .var .local (ofString "cap")]] =
              some [.val (.word diffw)] := by
            simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hs5_ncap, hs5_cap,
              wordOpHOL, wordOp, valueIsWord, valueWord, diffw]
          have hlk_fma := pan_one_word_lookup s5.code.lookup (ofString "frame_mem_alloc") (ofString "n")
            (sourceFnBody Guest.Software.guestFn_frame_mem_alloc) diffw
            (by rw [hs5_code]; exact lookup_frame_mem_alloc_g10)
          rw [hargs_fma] at hnt ⊢; dsimp only at hnt ⊢
          rw [hlk_fma] at hnt ⊢; dsimp only at hnt ⊢
          by_cases hs5_clk0 : s5.clock = 0
          · rw [if_pos hs5_clk0] at hnt; simp at hnt
          · rw [if_neg hs5_clk0] at hnt ⊢
            let fmaCallee := HolFiniteMapExact.empty.update (ofString "n", ValueHOL.val (.word diffw))
            let fmaEntry := callEntryStateHOLFinite s5 fmaCallee
            have hfma_code : fmaEntry.code = originalRuntimeCode := hs5_code
            have hfma_no_evmErr := frame_mem_alloc_body_no_evmErr_g10 fmaEntry hfma_code
            rcases hfma_run : evaluateHOLFiniteState fmaEntry
                (sourceFnBody Guest.Software.guestFn_frame_mem_alloc) with ⟨rfma, fmaPost⟩
            rw [hfma_run] at hfma_no_evmErr
            have hfma_run_raw : evaluateHOLFiniteState
                (callEntryStateHOLFinite s5 (HolFiniteMapExact.empty.update (ofString "n", ValueHOL.val (.word diffw))))
                (sourceFnBody Guest.Software.guestFn_frame_mem_alloc) = (rfma, fmaPost) := hfma_run
            simp only [hfma_run_raw] at hnt ⊢
            cases rfma with
            | none => exact herr_triv
            | some rfma0 =>
              cases rfma0 with
              | timeOut => simp at hnt
              | exception eid ev =>
                dsimp only at hnt ⊢
                by_cases heid : eid = ofString "EvmErr"
                · subst heid; exact absurd ⟨ev, rfl⟩ hfma_no_evmErr
                · constructor
                  · intro _ h; cases h
                  · rintro ⟨_, h⟩; injection h with h'; injection h' with h1 _; exact (heid h1).elim
              | «break» => exact herr_triv
              | «continue» => exact herr_triv
              | finalFfi _ =>
                constructor
                · intro _ h; cases h
                · rintro ⟨_, h⟩; cases h
              | error => exact herr_triv
              | returned vfma =>
                have hfma_fp_lk : fmaEntry.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word fp_w)) := by
                  change s5.globals.lookup _ = _; rw [hs5_eq]; exact hfp_lk
                have hfma_sp_lk : fmaEntry.globals.lookup (ofString "scratch_ptr") = some (.val (.word sp_g_w)) := by
                  change s5.globals.lookup _ = _; rw [hs5_eq]; exact hsp_g_lk
                have hfma_n_lk : fmaEntry.locals.lookup (ofString "n") = some (.val (.word diffw)) := by
                  simp [fmaEntry, fmaCallee, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                obtain ⟨rfl, hcmp1_fma, hcmp2_fma, hfmaPost_eq_raw⟩ :=
                  frame_mem_alloc_body_run_g10 fmaEntry fp_w sp_g_w diffw
                    hfma_code hfma_fp_lk hfma_sp_lk hfma_n_lk vfma (by rw [hfma_run])
                have hfmaPost_eq : fmaPost = { fmaEntry with
                    globals := fmaEntry.globals.update (ofString "frame_mem_ptr",
                      .val (.word ((fp_w + (diffw + 7)) &&& ((0 : BitVec 64) - 8)))),
                    locals := fmaPost.locals,
                    clock := fmaPost.clock } := by
                  rw [hfma_run] at hfmaPost_eq_raw; exact hfmaPost_eq_raw
                dsimp only [fmaEntry] at hfmaPost_eq
                set qw : BitVec 64 := (fp_w + (diffw + 7)) &&& ((0 : BitVec 64) - 8)
                have hsh_p : shapeEqHOL (shapeOfHOLExact (.val (.word fp_w) : ValueHOL 64)) .one = true := by
                  simp [shapeEqHOL, shapeOfHOLExact]
                dsimp only at hnt ⊢
                simp only [hsh_p, ↓reduceIte] at hnt ⊢
                have hfp_le_sp_g : fp_w.toNat ≤ sp_g_w.toNat := by
                  have := hInv.1.2.2.2.2.1; omega
                have hsp_g_le_se : sp_g_w.toNat ≤ scratchEnd := by
                  have := hInv.1.2.2.2.2.2.1; omega
                have hfp_al8 : fp_w.toNat % 8 = 0 := by
                  have h8 : globN s "frame_mem_ptr" % 8 = 0 := hInv.1.2.2.2.2.2.2.2.1
                  rw [hfp_nat]; exact h8
                obtain ⟨hq_nat, hq_le_sp, hq_al8, hfp_le_q⟩ :=
                  frame_mem_alloc_arith_g10 fp_w sp_g_w diffw hfp_le_sp_g hsp_g_le_se hfp_al8 hcmp1_fma hcmp2_fma
                have hqw_nat : qw.toNat = fp_w.toNat + diffw.toNat := by
                  have hdiff_al8' : diffw.toNat % 8 = 0 := by
                    have hcapw_al8 : capw.toNat % 8 = 0 := by rw [hcapw_eq]; exact hmem40_8
                    omega
                  have halign_eq : (diffw.toNat + 7) / 8 * 8 = diffw.toNat := by omega
                  change qw.toNat = _ at hq_nat
                  omega
                have hqw_al8 : qw.toNat % 8 = 0 := hq_al8
                have hqw_le_sp : qw.toNat ≤ sp_g_w.toNat := hq_le_sp
                have hdiff_al8 : diffw.toNat % 8 = 0 := by
                  have hcapw_al8 : capw.toNat % 8 = 0 := by rw [hcapw_eq]; exact hmem40_8
                  omega
                have hdiff_pos : 0 < diffw.toNat := by omega
                set s6 : PanSemStateFiniteExact 64 F := { fmaPost with locals := s5.locals } with hs6_def
                have hs6_glob : s6.globals = s.globals.update (ofString "frame_mem_ptr", .val (.word qw)) := by
                  change fmaPost.globals = _
                  rw [hfmaPost_eq]; dsimp only [callEntryStateHOLFinite]; rw [hs5_eq]
                have hs6_code : s6.code = originalRuntimeCode := by
                  change fmaPost.code = _; rw [hfmaPost_eq]; dsimp only [callEntryStateHOLFinite]; exact hs5_code
                have hs6_ma : s6.memaddrs = ordinaryDomain := by
                  change fmaPost.memaddrs = _; rw [hfmaPost_eq]; dsimp only [callEntryStateHOLFinite]
                  rw [hs5_eq]; exact hInv.1.1.memaddrs
                have hs6_mem : s6.memory = s.memory := by
                  change fmaPost.memory = _; rw [hfmaPost_eq]; dsimp only [callEntryStateHOLFinite]; rw [hs5_eq]
                have hs6_ev : s6.globals.lookup (ofString "ev") = some (.val (.word evw)) := by
                  rw [hs6_glob]
                  simp [HolFiniteMapExact.lookup_update, FUPDATE,
                    show ofString "frame_mem_ptr" ≠ ofString "ev" by decide, hevw]
                have hs6_dom24 : s6.memaddrs (evw + 24#64) := by
                  rw [hs6_ma, ← hInv.1.1.memaddrs]
                  have hev24_eq : evw + 24#64 = BitVec.ofNat 64 (globN s "ev" + 24) := by
                    apply BitVec.eq_of_toNat_eq
                    have : (24#64 : BitVec 64).toNat = 24 := rfl
                    rw [BitVec.toNat_add, hevw_nat, this, BitVec.toNat_ofNat]
                  rw [hev24_eq]
                  exact ((hFW0.1 (globN s "ev", 280) (by simp)).2.2.2 3 (by omega)).choose_spec.1
                rcases hs_m24 : s.memory (evw + 24#64) with ⟨memPtrW⟩
                have hs6_m24 : s6.memory (evw + 24#64) = .word memPtrW := by rw [hs6_mem, hs_m24]
                have hmemPtrW_nat : memPtrW.toNat = memW s (globN s "ev" + 24) := by
                  have hev24_eq : evw + 24#64 = BitVec.ofNat 64 (globN s "ev" + 24) := by
                    apply BitVec.eq_of_toNat_eq
                    have : (24#64 : BitVec 64).toNat = 24 := rfl
                    rw [BitVec.toNat_add, hevw_nat, this, BitVec.toNat_ofNat]
                  unfold memW; rw [← hev24_eq, hs_m24]
                let freshIvl : Ivl := (globN s "frame_mem_ptr", diffw.toNat)
                let mzGrowDst : ExpHOL 64 :=
                  .op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]), .var .local (ofString "cap")]
                let mzGrowN : ExpHOL 64 :=
                  .op .sub [.var .local (ofString "ncap"), .var .local (ofString "cap")]
                have hev_mzg_dst : @evalHOLExact 64 F _ s6.toExact (fun a => Classical.propDecidable (s6.memaddrs a)) mzGrowDst =
                    some (.val (.word (memPtrW + capw))) := by
                  have hs6_cap : s6.locals.lookup (ofString "cap") = some (.val (.word capw)) := hs5_cap
                  simp [mzGrowDst, evalHOLExact, evalListHOLExact, hs6_ev, hs6_cap, wordOpHOL, wordOp,
                    valueIsWord, valueWord, memLoadHOLExact, hs6_dom24, hs6_m24]
                have hev_mzg_n : @evalHOLExact 64 F _ s6.toExact (fun a => Classical.propDecidable (s6.memaddrs a)) mzGrowN =
                    some (.val (.word diffw)) := by
                  have hs6_ncap : s6.locals.lookup (ofString "ncap") = some (.val (.word ncapw)) := hs5_ncap
                  have hs6_cap : s6.locals.lookup (ofString "cap") = some (.val (.word capw)) := hs5_cap
                  simp [mzGrowN, evalHOLExact, evalListHOLExact, hs6_ncap, hs6_cap, wordOpHOL, wordOp,
                    valueIsWord, valueWord, diffw]
                have hmzg_dst_nat : (memPtrW + capw).toNat = globN s "frame_mem_ptr" := by
                  rw [BitVec.toNat_add, hmemPtrW_nat, hcapw_eq, hmem_end_fp, Nat.mod_eq_of_lt (by omega)]
                let mzGrowCall : ProgHOL 64 := .call (some (none, none)) (ofString "memzero") [mzGrowDst, mzGrowN]
                rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
                have hnt_mzg : (evaluateHOLFiniteState s6 mzGrowCall).1 ≠ some .timeOut := by
                  intro hto
                  rcases hmzg_to : evaluateHOLFiniteState s6
                      (.call (some (none, none)) (ofString "memzero") [mzGrowDst, mzGrowN]) with ⟨rmzg_to, smzg_to⟩
                  have hto' : rmzg_to = some .timeOut := by
                    dsimp only [mzGrowCall] at hto; rw [hmzg_to] at hto; exact hto
                  subst hto'
                  have hmzg_to_raw : evaluateHOLFiniteState s6
                      (.call (some (none, none)) (ofString "memzero")
                        [.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]), .var .local (ofString "cap")],
                         .op .sub [.var .local (ofString "ncap"), .var .local (ofString "cap")]]) = (some .timeOut, smzg_to) := hmzg_to
                  simp only [hmzg_to_raw] at hnt
                  exact hnt rfl
                have hmzg := eval_call_memzero_bre_g10 s6 mzGrowDst mzGrowN
                  (memPtrW + capw) diffw [freshIvl] hs6_code hs6_ma hev_mzg_dst hev_mzg_n
                  (fun _ => ⟨freshIvl, by simp, by rw [hmzg_dst_nat]; dsimp only [freshIvl]; omega⟩) hnt_mzg
                dsimp only at hmzg
                rcases hmzg_run : evaluateHOLFiniteState s6 mzGrowCall with ⟨rmzg, s7⟩
                rw [hmzg_run] at hmzg
                have hmzg_run_raw : evaluateHOLFiniteState s6
                    (.call (some (none, none)) (ofString "memzero")
                      [.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]), .var .local (ofString "cap")],
                       .op .sub [.var .local (ofString "ncap"), .var .local (ofString "cap")]]) = (rmzg, s7) := hmzg_run
                simp only [hmzg_run_raw] at hnt ⊢
                cases rmzg with
                | some rmzg0 =>
                  dsimp only at hnt ⊢
                  have hnr := hmzg.2 (by simp)
                  refine ⟨fun v hv => absurd (Or.inl ⟨v, hv⟩) hnr, ?_⟩
                  rintro ⟨ev, hv⟩
                  injection hv with hv'; subst hv'
                  exact absurd (Or.inr ⟨ofString "EvmErr", ev, rfl, by decide⟩) hnr
                | none =>
                  dsimp only at hnt ⊢
                  obtain ⟨heff_mzg, hs7_loc⟩ := hmzg.1 rfl
                  rcases hst40 : evaluateHOLFiniteState s7
                      (.store (.op .add [.var .global (ofString "ev"), .const 40#64]) (.var .local (ofString "ncap"))) with ⟨rst40, s8⟩
                  simp only [hst40] at hnt ⊢
                  cases rst40 with
                  | some res40 =>
                    have herr := store_some_eq_error_g10 hst40; subst herr; dsimp only; exact herr_triv
                  | none =>
                    dsimp only at hnt ⊢
                    have hs7_ev : s7.globals.lookup (ofString "ev") = some (.val (.word evw)) := by
                      rw [heff_mzg.globals]; exact hs6_ev
                    have hs7_ncap : s7.locals.lookup (ofString "ncap") = some (.val (.word ncapw)) := by
                      rw [hs7_loc]; exact hs5_ncap
                    obtain ⟨w_ncap', hw_ncap_ev, hs8_eq⟩ := R14Shards.OpHandlersA.store_global_off_word (t := s7) (post := s8)
                      (gname := "ev") (gbase := globN s "ev") (off := 40) hs7_ev hevw_nat (by omega)
                      (fun v hv => by
                        change s7.locals.lookup (ofString "ncap") = some v at hv
                        rw [hs7_ncap] at hv; injection hv with hv'; exact ⟨ncapw, hv'.symm⟩) hst40
                    have hw_ncap_val : ncapw = w_ncap' := by
                      change s7.locals.lookup (ofString "ncap") = some (.val (.word w_ncap')) at hw_ncap_ev
                      rw [hs7_ncap] at hw_ncap_ev
                      injection hw_ncap_ev with h1; injection h1 with h2; injection h2 with h3
                    subst w_ncap'
                    have heff_st40 := (ByteRegionEffect.of_store_word (Rl := [(globN s "ev", 280)])
                      (heff_mzg.memaddrs.trans hs6_ma) hst40
                      (fun v hv => by
                        change s7.locals.lookup (ofString "ncap") = some v at hv
                        rw [hs7_ncap] at hv; injection hv with hv'; exact ⟨ncapw, hv'.symm⟩)
                      (fun addr hdst _ => by
                        simp [evalHOLExact, evalListHOLExact, hs7_ev, wordOpHOL, wordOp, valueIsWord, valueWord] at hdst
                        have h40_eq : (evw + 40#64).toNat = globN s "ev" + 40 := by
                          have : (40#64 : BitVec 64).toNat = 40 := rfl
                          rw [BitVec.toNat_add, hevw_nat, this, Nat.mod_eq_of_lt (by omega)]
                        exact ⟨(globN s "ev", 280), by simp, by rw [← hdst, h40_eq]; dsimp only; omega,
                          by rw [← hdst, h40_eq]; dsimp only; omega⟩)).1
                    let m : PanSemStateFiniteExact 64 F :=
                      { s8 with locals := s8.locals.resVarEq (ofString "ncap", s3.locals.lookup (ofString "ncap")) }
                    change (let out := evaluateHOLFiniteState m tailProg
                      let post := { out.2 with
                        locals := ((out.2.locals.resVarEq (ofString "nlen", s2.locals.lookup (ofString "nlen"))).resVarEq
                          (ofString "cap", s1.locals.lookup (ofString "cap"))).resVarEq
                          (ofString "len", s.locals.lookup (ofString "len")) }
                      (∀ v, out.1 = some (.returned v) →
                        (EvmInv post ∧ Group10.HeadMemChainWF post) ∧ evmChain post = evmChain s ∧ evmR post ≤ evmR s ∧
                        (∀ g : String, ofString g ≠ ofString "frame_mem_ptr" → globN post g = globN s g)) ∧
                      (IsEvmErr out.1 →
                        (EvmInv post ∧ Group10.HeadMemChainWF post) ∧ evmChain post = evmChain s ∧ evmR post ≤ evmR s))
                    have hm_glob : m.globals = s.globals.update (ofString "frame_mem_ptr", .val (.word qw)) := by
                      dsimp only [m]; rw [hs8_eq]; dsimp only; rw [heff_mzg.globals, hs6_glob]
                    have hm_fp_glob : globN m "frame_mem_ptr" = qw.toNat := by
                      unfold globN; rw [hm_glob]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
                    have hm_other_glob : ∀ g : String, ofString g ≠ ofString "frame_mem_ptr" →
                        m.globals.lookup (ofString g) = s.globals.lookup (ofString g) := by
                      intro g hg; rw [hm_glob]
                      simp [HolFiniteMapExact.lookup_update, FUPDATE, hg, Ne.symm hg]
                    have hm_G : GuestInv m := by
                      have hcode_m : m.code = s.code := by
                        dsimp only [m]; rw [hs8_eq]; dsimp only; rw [heff_mzg.code, hs6_code, hcode]
                      have hma_m : m.memaddrs = s.memaddrs := by
                        dsimp only [m]; rw [hs8_eq]; dsimp only; rw [heff_mzg.memaddrs, hs6_ma, hInv.1.1.memaddrs]
                      have hsh_m : m.shMemaddrs = s.shMemaddrs := by
                        dsimp only [m]; rw [hs8_eq]; dsimp only; rw [heff_mzg.shMemaddrs]
                        change fmaPost.shMemaddrs = _; rw [hfmaPost_eq]; dsimp only [callEntryStateHOLFinite]; rw [hs5_eq]
                      have hba_m : m.baseAddr = s.baseAddr := by
                        dsimp only [m]; rw [hs8_eq]; dsimp only; rw [heff_mzg.baseAddr]
                        change fmaPost.baseAddr = _; rw [hfmaPost_eq]; dsimp only [callEntryStateHOLFinite]; rw [hs5_eq]
                      exact guestInv_congr hcode_m hma_m hsh_m hba_m hInv.1.1
                    have hfm_m : globN s "frame_mem_ptr" ≤ globN m "frame_mem_ptr" := by
                      rw [hm_fp_glob, hqw_nat, hfp_nat]; omega
                    have hAm : ArenaReady m := by
                      refine ⟨hm_G, ?_⟩
                      unfold ArenaOK
                      have hhp_m : globN m "heap_ptr" = globN s "heap_ptr" :=
                        OpHandlers.globN_eq_of_lookup_eq (hm_other_glob "heap_ptr" (by decide))
                      have hsp_m : globN m "scratch_ptr" = globN s "scratch_ptr" :=
                        OpHandlers.globN_eq_of_lookup_eq (hm_other_glob "scratch_ptr" (by decide))
                      rw [hhp_m, hm_fp_glob, hsp_m]
                      have hA := hInv.1.2
                      have hss_le_fp : scratchStart ≤ globN s "frame_mem_ptr" := hA.2.2.1
                      exact ⟨hA.1, hA.2.1, by rw [hqw_nat, hfp_nat]; omega, by rw [← hsp_g_nat]; exact hqw_le_sp,
                        hA.2.2.2.2.1, hA.2.2.2.2.2.1, hqw_al8, hA.2.2.2.2.2.2.2.1,
                        globalsWord_update (ofString "frame_mem_ptr") qw hm_glob hA.2.2.2.2.2.2.2.2⟩
                    have heff_s_s6 : FrameMemByteEffG10 s s6 [freshIvl, (globN s "ev", 280), (memW s (globN s "ev" + 24), memW s (globN s "ev" + 40))] :=
                      ⟨hs6_code.trans hcode.symm,
                       hs6_ma.trans hInv.1.1.memaddrs.symm,
                       by change fmaPost.shMemaddrs = _; rw [hfmaPost_eq]; dsimp only [callEntryStateHOLFinite]; rw [hs5_eq],
                       by change fmaPost.baseAddr = _; rw [hfmaPost_eq]; dsimp only [callEntryStateHOLFinite]; rw [hs5_eq],
                       by change fmaPost.be = _; rw [hfmaPost_eq]; dsimp only [callEntryStateHOLFinite]; rw [hs5_eq],
                       fun g hg => by
                         change fmaPost.globals.lookup (ofString g) = _; rw [hfmaPost_eq]
                         dsimp only [callEntryStateHOLFinite]; rw [hs5_eq]
                         simp [HolFiniteMapExact.lookup_update, FUPDATE, hg, Ne.symm hg],
                       fun a _ => by rw [hs6_mem],
                       fun a _ => by rw [hs6_mem],
                       fun b _ _ => by
                         unfold memB; rw [hs6_mem]
                         have hbe6 : s6.be = s.be := by
                           change fmaPost.be = _; rw [hfmaPost_eq]; dsimp only [callEntryStateHOLFinite]; rw [hs5_eq]
                         rw [hbe6]⟩
                    have heff_m : FrameMemByteEffG10 s m
                        [freshIvl, (globN s "ev", 280), (memW s (globN s "ev" + 24), memW s (globN s "ev" + 40))] := by
                      have hmzg_fm : FrameMemByteEffG10 s6 s7 [freshIvl] :=
                        ⟨heff_mzg.code, heff_mzg.memaddrs, heff_mzg.shMemaddrs, heff_mzg.baseAddr,
                         heff_mzg.be, fun _ _ => by rw [heff_mzg.globals],
                         heff_mzg.out_dom, heff_mzg.cell_frame, heff_mzg.byte_frame⟩
                      have hst40_fm : FrameMemByteEffG10 s7 s8 [(globN s "ev", 280)] :=
                        ⟨heff_st40.code, heff_st40.memaddrs, heff_st40.shMemaddrs, heff_st40.baseAddr,
                         heff_st40.be, fun _ _ => by rw [heff_st40.globals],
                         heff_st40.out_dom, heff_st40.cell_frame, heff_st40.byte_frame⟩
                      have h1 := hmzg_fm.mono
                        (R2 := [freshIvl, (globN s "ev", 280), (memW s (globN s "ev" + 24), memW s (globN s "ev" + 40))])
                        (fun x hx => by simp at hx; subst hx; exact ⟨freshIvl, by simp, le_refl _, le_refl _⟩)
                      have h2 := hst40_fm.mono
                        (R2 := [freshIvl, (globN s "ev", 280), (memW s (globN s "ev" + 24), memW s (globN s "ev" + 40))])
                        (fun x hx => by simp at hx; subst hx; exact ⟨(globN s "ev", 280), by simp, le_refl _, le_refl _⟩)
                      have h3 := (heff_s_s6.trans h1).trans h2
                      exact ⟨h3.code, h3.memaddrs, h3.shMemaddrs, h3.baseAddr, h3.be,
                        h3.glob_other, h3.out_dom, h3.cell_frame, h3.byte_frame⟩
                    have hs7_e0_eq : ∀ off, off + 8 ≤ 280 → off % 8 = 0 →
                        memW s7 (globN s "ev" + off) = memW s (globN s "ev" + off) := by
                      intro off hoff hoff8
                      unfold memW
                      rw [heff_mzg.cell_frame (BitVec.ofNat 64 (globN s "ev" + off)), hs6_mem]
                      intro x hx; simp at hx; subst hx
                      have htn : (BitVec.ofNat 64 (globN s "ev" + off)).toNat = globN s "ev" + off :=
                        Nat.mod_eq_of_lt (by omega)
                      rw [htn]
                      have he0_8 : (globN s "ev") % 8 = 0 := (hFW0.1 (globN s "ev", 280) (by simp)).2.1
                      have ha8 : (globN s "ev" + off) % 8 = 0 := by omega
                      have hfp_s_8 : globN s "frame_mem_ptr" % 8 = 0 := hInv.1.2.2.2.2.2.2.2.1
                      obtain ⟨he0_scr, _⟩ := (hFW0.1 (globN s "ev", 280) (by simp)).1
                      exact not_cellHits_of_disj_aligned (i := (globN s "ev", 280)) ha8 hfp_s_8
                        (Nat.le_add_right _ off) (Nat.add_le_add_left hoff _)
                        (Or.inr (Or.inr (Or.inr (by dsimp only [freshIvl] at he0_scr ⊢; omega))))
                    have hm_e0_other : ∀ off, off + 8 ≤ 280 → off % 8 = 0 → off ≠ 32 → off ≠ 40 →
                        memW m (globN s "ev" + off) = memW s (globN s "ev" + off) := by
                      intro off hoff hoff8 _ hne40
                      change memW s8 (globN s "ev" + off) = memW s (globN s "ev" + off)
                      rw [hs8_eq, R14Shards.OpHandlersA.memW_updW_ne s7 (globN s "ev" + 40) (globN s "ev" + off) _ (by omega) (by omega) (by omega),
                          hs7_e0_eq off hoff hoff8]
                    have hm_e0_40 : memW m (globN s "ev" + 40) = ncapw.toNat := by
                      change memW s8 (globN s "ev" + 40) = ncapw.toNat
                      rw [hs8_eq, R14Shards.OpHandlersA.memW_updW_same s7 (globN s "ev" + 40) ncapw]
                    have hfresh_m : freshIvl = (0, 0) ∨
                        (freshIvl.1 % 8 = 0 ∧ freshIvl.2 % 8 = 0 ∧
                          Inside freshIvl (globN s "frame_mem_ptr") (globN m "frame_mem_ptr")) := by
                      refine Or.inr ⟨hInv.1.2.2.2.2.2.2.2.1, hdiff_al8, ?_⟩
                      rw [hm_fp_glob, hqw_nat, hfp_nat]; dsimp only [freshIvl, Inside]; omega
                    have hnew_m :
                        (freshIvl.2 = 0 ∧ memW m (globN s "ev" + 40) = memW s (globN s "ev" + 40) ∧
                          globN m "frame_mem_ptr" = globN s "frame_mem_ptr") ∨
                        (freshIvl.2 ≠ 0 ∧
                          memW s (globN s "ev" + 24) + memW s (globN s "ev" + 40) = freshIvl.1 ∧
                          memW m (globN s "ev" + 40) = memW s (globN s "ev" + 40) + freshIvl.2 ∧
                          globN m "frame_mem_ptr" = freshIvl.1 + freshIvl.2) := by
                      refine Or.inr ⟨by dsimp only [freshIvl]; omega, hmem_end_fp, ?_, ?_⟩
                      · rw [hm_e0_40]; dsimp only [freshIvl]; omega
                      · rw [hm_fp_glob, hqw_nat, hfp_nat]
                    have hm_loc_s5 : ∀ k, k ≠ ofString "ncap" → m.locals.lookup k = s5.locals.lookup k := by
                      intro k hk
                      have hres_ne : ∀ (mp : HolFiniteMapExact MlS (ValueHOL 64)) (key q : MlS) (old : Option (ValueHOL 64)),
                          key ≠ q → (mp.resVarEq (key, old)).lookup q = mp.lookup q := by
                        intro mp key q old hne
                        unfold HolFiniteMapExact.resVarEq
                        cases old with
                        | none => simp [HolFiniteMapExact.eraseEq, FDOMSUB_HOL, hne.symm]
                        | some v => simp [HolFiniteMapExact.updateEq, FUPDATE_HOL, hne.symm]
                      have hs8_l : s8.locals = s5.locals := by rw [hs8_eq]; exact hs7_loc
                      dsimp only [m]
                      rw [hres_ne _ _ _ _ hk.symm, hs8_l]
                    have hnt_m : (evaluateHOLFiniteState m tailProg).1 ≠ some .timeOut := by
                      dsimp only [m]
                      exact hnt
                    exact run_tail m freshIvl hAm hfm_m hm_other_glob heff_m hfresh_m hm_e0_other hnew_m
                      (by rw [hm_e0_40]; exact hnlen_le_ncap)
                      (by rw [hm_loc_s5 (ofString "len") (by decide)]; exact hs5_len)
                      (by rw [hm_loc_s5 (ofString "nlen") (by decide)]; exact hs5_nlen)
                      (by rw [hm_loc_s5 (ofString "expand_by") (by decide)]; exact hs5_eb)
                      hnt_m
        · have hnlen_le_cap : nlenw.toNat ≤ capw.toNat := by
            rw [BitVec.lt_def] at hgrow; omega
          simp only [hgrow, ↓reduceIte, evaluateHOLFiniteState_skip] at hnt ⊢
          exact run_tail s3 (0, 0)
            ⟨guestInv_congr (s := s) rfl rfl rfl rfl hInv.1.1, hInv.1.2⟩
            (le_refl _)
            (fun _ _ => rfl)
            ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩
            (Or.inl rfl)
            (fun _ _ _ _ _ => rfl)
            (Or.inl ⟨rfl, rfl, rfl⟩)
            (by change nlenw.toNat ≤ memW s (globN s "ev" + 40); rw [← hcapw_eq]; exact hnlen_le_cap)
            hs3_len hs3_nlen hs3_eb hnt

theorem epsA_extend_memory_cost1_aligned :
    EvmPreservingSpecA (fun _ => True)
      (fun s v post =>
        LocFrame s post ∧
        ∃ cw ebw : BitVec 64,
          v = .rStruct [.val (.word cw), .val (.word ebw)] ∧
          (ebw = 0#64 ∨
            (memW s (globN s "ev" + 32) + ebw.toNat < 2 ^ 37 ∧
              (memW s (globN s "ev" + 32) + ebw.toNat) % 32 = 0)))
      (ofString "extend_memory_cost1") := by
  obtain ⟨params, body, retShape, hlk, hro⟩ := epsA_extend_memory_cost1
  have hlk_eq := Group10.lookup_extend_memory_cost1.symm.trans hlk
  injection hlk_eq with hprod
  rcases Prod.mk.inj hprod with ⟨rfl, hprod2⟩
  rcases Prod.mk.inj hprod2 with ⟨hbody_eq, rfl⟩
  subst hbody_eq
  refine ⟨_, _, _, Group10.lookup_extend_memory_cost1, ?_⟩
  intro F s hcode hInv hHMWF hP hlookup hnt
  have hs := hro s hcode hInv hHMWF hP hlookup hnt
  dsimp only at hs ⊢
  refine ⟨fun v hv => ?_, hs.2⟩
  obtain ⟨h1, h2, h3, hlf⟩ := hs.1 v hv
  have hal : memW s (globN s "ev" + 32) % 32 = 0 :=
    (Group10.headMemChainWF_headMemAligned hHMWF).1
  exact ⟨h1, h2, h3, hlf, Group10.extend_memory_cost1_aligned_growth s hcode hal v hv⟩

private def emc1NcrProg (good : MlS → Bool) : ProgHOL 64 → Bool
  | .dec _ _ _ b => emc1NcrProg good b
  | .seq a b => emc1NcrProg good a && emc1NcrProg good b
  | .ite _ a b => emc1NcrProg good a && emc1NcrProg good b
  | .decCall _ _ f _ cont => good f && emc1NcrProg good cont
  | .primitive _ _ _ => true
  | .skip | .return _ => true
  | _ => false

private theorem lex_emc1Ncr {a1 a2 b1 b2 : Nat} (h : a1 < a2 ∨ a1 = a2 ∧ b1 < b2) :
    Prod.Lex (· < ·) (· < ·) (a1, b1) (a2, b2) := by
  rcases h with h | ⟨rfl, h⟩
  · exact Prod.Lex.left _ _ h
  · exact Prod.Lex.right _ h

private theorem evaluate_emc1NcrProg {F : Type} (good : MlS → Bool)
    (hgood : ∀ f, good f = true → ∀ values body callee rs,
      PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup f values =
        some (body, callee, rs) →
      emc1NcrProg good body = true)
    (p : ProgHOL 64) (hp : emc1NcrProg good p = true)
    (s : PanSemStateFiniteExact 64 F) (hcode : s.code = originalRuntimeCode) :
    ¬ IsEvmErr (evaluateHOLFiniteState s p).1 := by
  cases shape : p with
  | skip => rw [evaluateHOLFiniteState_skip]; rintro ⟨_, h⟩; cases h
  | «return» _ =>
    rw [evaluateHOLFiniteState_return]
    split
    · rintro ⟨_, h⟩; cases h
    · split <;> (rintro ⟨_, h⟩; cases h)
  | primitive _ _ _ =>
    rw [evaluateHOLFiniteState_primitive]
    split
    · rintro ⟨_, h⟩; cases h
    · split
      · rintro ⟨_, h⟩; cases h
      · split <;> (rintro ⟨_, h⟩; cases h)
  | dec name _ _ body =>
    have hb : emc1NcrProg good body = true := by simpa [shape, emc1NcrProg] using hp
    rw [evaluateHOLFiniteState_dec_total]; dsimp only
    split
    · rintro ⟨_, h⟩; cases h
    · rename_i val _
      split
      · exact evaluate_emc1NcrProg good hgood body hb (setVarHOLFinite name val s) hcode
      · rintro ⟨_, h⟩; cases h
  | seq a b =>
    have hab : emc1NcrProg good a = true ∧ emc1NcrProg good b = true := by
      simpa [shape, emc1NcrProg, Bool.and_eq_true] using hp
    have ih1 := evaluate_emc1NcrProg good hgood a hab.1 s hcode
    have rem := evaluateHOLFiniteState_clock_le s a
    have meta' := PanRunBounded.evaluateHOLFiniteState_metadata s a
    rw [evaluateHOLFiniteState_seq_line780]
    rcases hr : evaluateHOLFiniteState s a with ⟨r1, mid⟩
    rw [hr] at ih1 rem meta'
    dsimp only at ih1 rem meta' ⊢
    cases r1 with
    | none =>
      have mclock : mid.clock ≤ s.clock := rem
      exact evaluate_emc1NcrProg good hgood b hab.2 mid (meta'.1.trans hcode)
    | some _ => exact ih1
  | ite _ yes no =>
    have hy : emc1NcrProg good yes = true ∧ emc1NcrProg good no = true := by
      simpa [shape, emc1NcrProg, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_emc1NcrProg good hgood no hy.2 s hcode
      · exact evaluate_emc1NcrProg good hgood yes hy.1 s hcode
    · rintro ⟨_, h⟩; cases h
  | decCall name _ fn args cont =>
    have hc : good fn = true ∧ emc1NcrProg good cont = true := by
      simpa [shape, emc1NcrProg, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
    rcases evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
    · rintro ⟨_, h⟩; cases h
    · dsimp only
      rcases hl : lookupCodeHOLFinite s.code.lookup fn values with _ | ⟨body, callee, rs⟩
      · rintro ⟨_, h⟩; cases h
      · dsimp only
        have hl' : lookupCodeHOLFinite originalRuntimeCode.lookup fn values = some (body, callee, rs) := by
          rwa [← hcode]
        have bodyOk := hgood fn hc.1 values body callee rs hl'
        split
        · rintro ⟨_, h⟩; cases h
        · have ih1 := evaluate_emc1NcrProg good hgood body bodyOk (callEntryStateHOLFinite s callee) hcode
          have meta' := PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body
          have cl := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite s callee) body
          rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨res, st⟩
          rw [hrun] at ih1 meta' cl
          dsimp only at ih1 meta' cl ⊢
          change st.clock ≤ s.clock - 1 at cl
          have small : st.clock < s.clock := by omega
          have stCode : st.code = originalRuntimeCode := meta'.1.trans hcode
          cases res with
          | none => rintro ⟨_, h⟩; cases h
          | some r =>
            cases r with
            | returned v =>
              dsimp only
              split
              · set resumed := setVarHOLFinite name v { st with locals := s.locals }
                have smallR : resumed.clock < s.clock := small
                have rCode : resumed.code = originalRuntimeCode := stCode
                exact evaluate_emc1NcrProg good hgood cont hc.2 resumed rCode
              · rintro ⟨_, h⟩; cases h
            | «break» => rintro ⟨_, h⟩; cases h
            | «continue» => rintro ⟨_, h⟩; cases h
            | _ => exact ih1
  | _ => simp [shape, emc1NcrProg] at hp
termination_by (s.clock, sizeOf p)
decreasing_by
  all_goals
    simp_wf
    apply lex_emc1Ncr
    try subst shape
    try simp only [setVarHOLFinite, decClockHOLFinite, callEntryStateHOLFinite,
      ProgHOL.seq.sizeOf_spec, ProgHOL.ite.sizeOf_spec, ProgHOL.dec.sizeOf_spec,
      ProgHOL.decCall.sizeOf_spec, true_and]
    first
      | exact Or.inl smallR
      | exact Or.inl small
      | omega
      | (rcases Nat.lt_or_eq_of_le mclock with h | h
         · exact Or.inl h
         · exact Or.inr ⟨h, by simp +arith⟩)
      | exact Or.inr ⟨rfl, by simp +arith⟩

private def emc1NcrCallees (f : MlS) : Bool :=
  f == ofString "u256_is_zero" ||
  f == ofString "u256_fits_word" ||
  f == ofString "u256_low" ||
  f == ofString "sat_word" ||
  f == ofString "add_sat" ||
  f == ofString "ceil32" ||
  f == ofString "words_of" ||
  f == ofString "mul64x64" ||
  f == ofString "memory_gas_cost" ||
  f == ofString "extend_memory_cost1"

private theorem emc1NcrCallees_good :
    ∀ f, emc1NcrCallees f = true → ∀ values body callee rs,
      PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup f values =
        some (body, callee, rs) →
      emc1NcrProg emc1NcrCallees body = true := by
  have hb0 : emc1NcrProg emc1NcrCallees (sourceFnBody Guest.Software.guestFn_u256_is_zero) = true := by decide
  have hb1 : emc1NcrProg emc1NcrCallees (sourceFnBody Guest.Software.guestFn_u256_fits_word) = true := by decide
  have hb2 : emc1NcrProg emc1NcrCallees (sourceFnBody Guest.Software.guestFn_u256_low) = true := by decide
  have hb3 : emc1NcrProg emc1NcrCallees (sourceFnBody Guest.Software.guestFn_sat_word) = true := by decide
  have hb4 : emc1NcrProg emc1NcrCallees (sourceFnBody Guest.Software.guestFn_add_sat) = true := by decide
  have hb5 : emc1NcrProg emc1NcrCallees (sourceFnBody Guest.Software.guestFn_ceil32) = true := by decide
  have hb6 : emc1NcrProg emc1NcrCallees (sourceFnBody Guest.Software.guestFn_words_of) = true := by decide
  have hb7 : emc1NcrProg emc1NcrCallees (sourceFnBody Guest.Software.guestFn_mul64x64) = true := by decide
  have hb8 : emc1NcrProg emc1NcrCallees (sourceFnBody Guest.Software.guestFn_memory_gas_cost) = true := by decide
  have hb9 : emc1NcrProg emc1NcrCallees (sourceFnBody Guest.Software.guestFn_extend_memory_cost1) = true := by decide
  have hl0 : originalRuntimeCode.lookup (ofString "u256_is_zero") = _ :=
    lookup_of_guestAst_getElem 42 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_u256_is_zero) rfl
  have hl1 : originalRuntimeCode.lookup (ofString "u256_fits_word") = _ :=
    lookup_of_guestAst_getElem 41 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_u256_fits_word) rfl
  have hl2 : originalRuntimeCode.lookup (ofString "u256_low") = _ :=
    lookup_of_guestAst_getElem 40 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_u256_low) rfl
  have hl3 : originalRuntimeCode.lookup (ofString "sat_word") = _ :=
    lookup_of_guestAst_getElem 440 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_sat_word) rfl
  have hl4 : originalRuntimeCode.lookup (ofString "add_sat") = _ :=
    lookup_of_guestAst_getElem 441 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_add_sat) rfl
  have hl5 := Group10.lookup_ceil32
  have hl6 : originalRuntimeCode.lookup (ofString "words_of") = _ :=
    lookup_of_guestAst_getElem 443 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_words_of) rfl
  have hl7 := Group10.lookup_mul64x64
  have hl8 := Group10.lookup_memory_gas_cost
  have hl9 := Group10.lookup_extend_memory_cost1
  intro f hf values body callee rs hfound
  obtain ⟨params, rs', hinst⟩ := lookupCode_installed hfound
  simp only [emc1NcrCallees, Bool.or_eq_true, beq_iff_eq] at hf
  rcases hf with ((((((((rfl | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl
  · rw [hl0] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; exact hb0
  · rw [hl1] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; exact hb1
  · rw [hl2] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; exact hb2
  · rw [hl3] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; exact hb3
  · rw [hl4] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; exact hb4
  · rw [hl5] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; exact hb5
  · rw [hl6] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; exact hb6
  · rw [hl7] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; exact hb7
  · rw [hl8] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; exact hb8
  · rw [hl9] at hinst; rw [← (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1]; exact hb9

private theorem decCall_extend_memory_cost1_step_g10 {F : Type}
    {s : PanSemStateFiniteExact 64 F} {nm : MlS} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (hcode : s.code = originalRuntimeCode)
    (hal : memW s (globN s "ev" + 32) % 32 = 0) :
    let out := evaluateHOLFiniteState s
      (.decCall nm (.comb [.one, .one]) (ofString "extend_memory_cost1") args cont)
    out.1 ≠ some .timeOut →
    (out.1 ≠ none ∧ (∀ v, out.1 ≠ some (.returned v)) ∧ ¬ IsEvmErr out.1) ∨
    (∃ (cw ebw : BitVec 64) (s1 : PanSemStateFiniteExact 64 F),
      s1.code = originalRuntimeCode ∧
      LocFrame s s1 ∧
      s1.locals = s.locals.update (nm, .rStruct [.val (.word cw), .val (.word ebw)]) ∧
      (ebw = 0#64 ∨
        (memW s (globN s "ev" + 32) + ebw.toNat < 2 ^ 37 ∧
          (memW s (globN s "ev" + 32) + ebw.toNat) % 32 = 0)) ∧
      let outc := evaluateHOLFiniteState s1 cont
      out = (outc.1, { outc.2 with locals := outc.2.locals.resVarEq (nm, s.locals.lookup nm) })) := by
  dsimp only
  intro hnt
  have herr_ab :
      (some PanSemResultExact.error : Option (PanSemResultExact 64)) ≠ none ∧
      (∀ v, (some PanSemResultExact.error : Option (PanSemResultExact 64)) ≠ some (.returned v)) ∧
      ¬ IsEvmErr (some PanSemResultExact.error) :=
    ⟨by simp, fun _ => by simp, by rintro ⟨_, h⟩; cases h⟩
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt ⊢
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | vals
  · simp only [hargs]; exact Or.inl herr_ab
  · simp only [hargs] at hnt ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "extend_memory_cost1") vals with _ | ⟨body, callee, rs⟩
    · simp only [hl]; exact Or.inl herr_ab
    · simp only [hl] at hnt ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt ⊢
        have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "extend_memory_cost1") vals =
            some (body, callee, rs) := by rwa [← hcode]
        have hbody_eq : body = sourceFnBody Guest.Software.guestFn_extend_memory_cost1 :=
          lookupCodeHOLFinite_installed_body s.code.lookup (ofString "extend_memory_cost1")
            _ _ body _ rs vals callee (by rw [hcode]; exact Group10.lookup_extend_memory_cost1) hl
        subst hbody_eq
        have hrs_eq : rs = .comb [.one, .one] := by
          have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
            originalRuntimeCode.lookup (ofString "extend_memory_cost1") vals
            (sourceFnBody Guest.Software.guestFn_extend_memory_cost1) callee rs hl_orig
          simp only [Flapjack.lookupCodeHOLExact, Group10.lookup_extend_memory_cost1] at hx
          split at hx
          · exact (congrArg (fun x => x.2.2) (Option.some.inj hx)).symm
          · cases hx
        subst hrs_eq
        have hsafe := evaluate_readOnlyProg opRoCallees opRoCallees_good
          (sourceFnBody Guest.Software.guestFn_extend_memory_cost1) (by decide)
          (callEntryStateHOLFinite s callee) hcode
        have hnoerr := evaluate_emc1NcrProg emc1NcrCallees emc1NcrCallees_good
          (sourceFnBody Guest.Software.guestFn_extend_memory_cost1) (by decide)
          (callEntryStateHOLFinite s callee) hcode
        have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata
          (callEntryStateHOLFinite s callee)
          (sourceFnBody Guest.Software.guestFn_extend_memory_cost1)).1
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee)
          (sourceFnBody Guest.Software.guestFn_extend_memory_cost1) with ⟨rb, pb⟩
        simp only [hrun] at hnt hmeta hsafe hnoerr ⊢
        rcases rb with _ | r0
        · exact Or.inl herr_ab
        · cases r0 with
          | timeOut => exact absurd rfl hnt
          | returned vb =>
            dsimp only at hnt ⊢
            obtain ⟨cw, ebw, rfl, hgrowth⟩ :=
              Group10.extend_memory_cost1_aligned_growth (callEntryStateHOLFinite s callee) hcode hal vb (by rw [hrun])
            have hsh_ok : (shapeEqHOL (shapeOfHOLExact (.rStruct [.val (.word cw), .val (.word ebw)] : ValueHOL 64))
                (.comb [.one, .one]) &&
                shapeEqHOL (shapeOfHOLExact (.rStruct [.val (.word cw), .val (.word ebw)] : ValueHOL 64))
                (.comb [.one, .one])) = true := by
              simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL]
            rw [if_pos hsh_ok] at hnt ⊢
            have hlf_ce : LocFrame (callEntryStateHOLFinite s callee) pb :=
              hsafe.to_resumes (Or.inl ⟨_, rfl⟩)
            have hlf_s : LocFrame s pb := by
              unfold LocFrame at hlf_ce ⊢; rw [hlf_ce]; rfl
            let s1 := setVarHOLFinite nm (.rStruct [.val (.word cw), .val (.word ebw)])
              { pb with locals := s.locals }
            have hs1_code : s1.code = originalRuntimeCode := hmeta.trans hcode
            have hs1_lf : LocFrame s s1 :=
              hlf_s.with_locals_clock (s.locals.update (nm, .rStruct [.val (.word cw), .val (.word ebw)])) pb.clock
            rcases hcont : evaluateHOLFiniteState s1 cont with ⟨rc, pc⟩
            exact Or.inr ⟨cw, ebw, s1, hs1_code, hs1_lf, rfl, hgrowth,
              by dsimp only [s1] at hcont ⊢; rw [hcont]⟩
          | exception eid ev =>
            refine Or.inl ⟨by simp, fun _ => by simp, ?_⟩
            rintro ⟨ev', hev⟩
            injection hev with hev'
            injection hev' with heid' _
            subst heid'
            exact hnoerr ⟨ev, rfl⟩
          | error => exact Or.inl herr_ab
          | «break» => exact Or.inl herr_ab
          | «continue» => exact Or.inl herr_ab
          | finalFfi outcome => exact Or.inl ⟨by simp, fun _ => by simp, by rintro ⟨_, h⟩; cases h⟩

theorem epsA_extend_memory_cost2 :
    EvmPreservingSpecA (fun _ => True)
      (fun s v post =>
        LocFrame s post ∧
        ∃ cw ebw : BitVec 64,
          v = .rStruct [.val (.word cw), .val (.word ebw)] ∧
          (ebw = 0#64 ∨
            (memW s (globN s "ev" + 32) + ebw.toNat < 2 ^ 37 ∧
              (memW s (globN s "ev" + 32) + ebw.toNat) % 32 = 0)))
      (ofString "extend_memory_cost2") := by
  refine ⟨_, _, _, lookup_extend_memory_cost2, ?_⟩
  intro F s hcode hInv hHMWF _ _ hnt
  have herr_triv : ∀ {P1 : ValueHOL 64 → Prop} {P2 : Prop},
      (∀ v, (some PanSemResultExact.error : Option (PanSemResultExact 64)) = some (.returned v) → P1 v) ∧
      (IsEvmErr (some PanSemResultExact.error) → P2) := by
    intro _ _; constructor
    · intro _ h; cases h
    · rintro ⟨_, h⟩; cases h
  have h10 : ¬ ((1#64 : BitVec 64) = 0) := by decide
  have h00 : (0#64 : BitVec 64) = 0 := rfl
  have hal_s : memW s (globN s "ev" + 32) % 32 = 0 :=
    (Group10.headMemChainWF_headMemAligned hHMWF).1
  have hb_ev := evmInv_head_ev_bounds_g10 hInv
  obtain ⟨evw, hevw, hevw_nat⟩ := global_word_of_pos s "ev" hb_ev.1
  have hhead_mem : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by simp [evmChain, evmChainFrom]
  have hFW0 := hInv.2.choose_spec.2.2.2.2.1 _ hhead_mem
  have hlen_le_cap : memW s (globN s "ev" + 32) ≤ memW s (globN s "ev" + 40) := hFW0.2.2.2.2.2.2.1
  have hcap_in := hFW0.2.1
  dsimp only [Inside] at hcap_in
  have hfp_le : globN s "frame_mem_ptr" ≤ scratchEnd :=
    Nat.le_trans hInv.1.2.2.2.2.1 hInv.1.2.2.2.2.2.1
  have hlen_bound : memW s (globN s "ev" + 32) < 2 ^ 37 := by
    rw [R11Shards.scratchStart_val] at hcap_in
    rw [R11Shards.scratchEnd_val] at hfp_le
    omega
  have hret_rstruct2 : ∀ (st : PanSemStateFiniteExact 64 F) (e : ExpHOL 64) (w1 w2 : BitVec 64),
      @evalHOLExact 64 F _ st.toExact (fun x => Classical.propDecidable (st.memaddrs x)) e =
        some (.rStruct [.val (.word w1), .val (.word w2)]) →
      evaluateHOLFiniteState st (.return e) =
        (some (.returned (.rStruct [.val (.word w1), .val (.word w2)])), st.emptyLocalsHOLFinite) := by
    intro st e w1 w2 hev
    rw [evaluateHOLFiniteState_return, hev]; dsimp only
    have hsz : sizeOfShapeWithContextHOL st.structs
        (shapeOfHOLExact (.rStruct [.val (.word w1), .val (.word w2)] : ValueHOL 64)) ≤ 32 := by
      simp [shapeOfHOLExact, sizeOfShapeWithContextHOL, sizeOfShapesWithContextHOL]
    rw [if_pos hsz]
  have hpost_lf : ∀ {post : PanSemStateFiniteExact 64 F} {cw ebw : BitVec 64},
      LocFrame s post →
      (ebw = 0#64 ∨
        (memW s (globN s "ev" + 32) + ebw.toNat < 2 ^ 37 ∧
          (memW s (globN s "ev" + 32) + ebw.toNat) % 32 = 0)) →
      (∀ v, (some (.returned (.rStruct [.val (.word cw), .val (.word ebw)])) : Option (PanSemResultExact 64)) =
          some (.returned v) →
        (EvmInv post ∧ Group10.HeadMemChainWF post) ∧
          evmChain post = evmChain s ∧ evmR post ≤ evmR s ∧
          (LocFrame s post ∧
            ∃ cw' ebw' : BitVec 64,
              v = .rStruct [.val (.word cw'), .val (.word ebw')] ∧
              (ebw' = 0#64 ∨
                (memW s (globN s "ev" + 32) + ebw'.toNat < 2 ^ 37 ∧
                  (memW s (globN s "ev" + 32) + ebw'.toNat) % 32 = 0)))) ∧
      (IsEvmErr (some (.returned (.rStruct [.val (.word cw), .val (.word ebw)]))) →
        (EvmInv post ∧ Group10.HeadMemChainWF post) ∧
          evmChain post = evmChain s ∧ evmR post ≤ evmR s) := by
    intro post cw ebw hlf hgr
    have hm : post.memory = s.memory := by unfold LocFrame at hlf; conv_lhs => rw [hlf]
    have hg : post.globals = s.globals := by unfold LocFrame at hlf; conv_lhs => rw [hlf]
    have hlc : post = { s with locals := post.locals, clock := post.clock } := hlf
    have hInv_p : EvmInv post := by rw [hlc]; exact localsFree_evmInv s _ _ hInv
    have hWF_p : Group10.HeadMemChainWF post := (Group10.headMemChainWF_congr hm hg).2 hHMWF
    have hc := evm_congr hm hg
    refine ⟨fun v hv => ?_, by rintro ⟨_, h⟩; cases h⟩
    injection hv with hv'; injection hv' with hv''
    exact ⟨⟨hInv_p, hWF_p⟩, evmChain_congr hm hg, le_of_eq hc.2.1, hlf, cw, ebw, hv''.symm, hgr⟩
  have hbody : sourceFnBody Guest.Software.guestFn_extend_memory_cost2 =
      .decCall (ofString "a") (.comb [.one, .one]) (ofString "extend_memory_cost1")
        [.var .local (ofString "s1"), .var .local (ofString "n1")]
        (.seq
          (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "a"))) (.const 18446744073709551615#64))
            (.return (.var .local (ofString "a")))
            .skip)
          (.dec (ofString "saved") .one (.load .one (.op .add [.var .global (ofString "ev"), .const 32#64]))
            (.seq
              (.store (.op .add [.var .global (ofString "ev"), .const 32#64])
                (.op .add [.var .local (ofString "saved"), .rfield 1 (.var .local (ofString "a"))]))
              (.decCall (ofString "b") (.comb [.one, .one]) (ofString "extend_memory_cost1")
                [.var .local (ofString "s2"), .var .local (ofString "n2")]
                (.seq
                  (.store (.op .add [.var .global (ofString "ev"), .const 32#64]) (.var .local (ofString "saved")))
                  (.seq
                    (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "b"))) (.const 18446744073709551615#64))
                      (.return (.var .local (ofString "b")))
                      .skip)
                    (.return (.rstruct
                      [.op .add [.rfield 0 (.var .local (ofString "a")), .rfield 0 (.var .local (ofString "b"))],
                       .op .add [.rfield 1 (.var .local (ofString "a")), .rfield 1 (.var .local (ofString "b"))]])))))))) := rfl
  dsimp only at hnt ⊢
  rcases hrun_all : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_extend_memory_cost2) with ⟨res_all, post_all⟩
  simp only [hrun_all] at hnt ⊢
  rw [hbody] at hrun_all
  have hstep1 := decCall_extend_memory_cost1_step_g10 hcode hal_s (by rw [hrun_all]; exact hnt)
  dsimp only at hstep1
  rcases hstep1 with ⟨hne1, hnret1, hnerr1⟩ | ⟨acw, aebw, s1, hs1_code, hs1_lf, hs1_loc, ha_gr, hrun1⟩
  · rw [hrun_all] at hne1 hnret1 hnerr1; dsimp only at hne1 hnret1 hnerr1
    exact ⟨fun v hv => False.elim (hnret1 v hv), fun he => False.elim (hnerr1 he)⟩
  · rw [hrun_all] at hrun1
    rcases hcont1 : evaluateHOLFiniteState s1 _ with ⟨r1, p1⟩
    rw [hcont1] at hrun1; dsimp only at hrun1
    injection hrun1 with hr_eq hp_eq
    have hnt1 : r1 ≠ some .timeOut := by rw [hr_eq] at hnt; exact hnt
    have hs1_a : s1.locals.lookup (ofString "a") = some (.rStruct [.val (.word acw), .val (.word aebw)]) := by
      rw [hs1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hcont1
    have hcmp_a : @evalHOLExact 64 F _ s1.toExact (fun x => Classical.propDecidable (s1.memaddrs x))
        (.cmp .equal (.rfield 0 (.var .local (ofString "a"))) (.const 18446744073709551615#64)) =
        some (.val (.word (if acw = 18446744073709551615#64 then 1#64 else 0#64))) := by
      simp [evalHOLExact, hs1_a, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    rw [hcmp_a] at hcont1; dsimp only at hcont1
    by_cases hac : acw = 18446744073709551615#64
    · rw [if_pos hac, if_neg h10] at hcont1
      rw [hret_rstruct2 s1 (.var .local (ofString "a")) acw aebw (by simp [evalHOLExact, hs1_a])] at hcont1
      dsimp only at hcont1
      injection hcont1 with hr1_eq hp1_eq
      subst hr_eq; subst hr1_eq
      have hlf_post : LocFrame s post_all := by
        rw [hp_eq, ← hp1_eq]
        exact hs1_lf.with_locals_clock _ s1.clock
      exact hpost_lf hlf_post ha_gr
    · rw [if_neg hac, if_pos h00, evaluateHOLFiniteState_skip] at hcont1; dsimp only at hcont1
      rw [evaluateHOLFiniteState_dec_total] at hcont1; dsimp only at hcont1
      rcases hld_sav : @evalHOLExact 64 F _ s1.toExact (fun x => Classical.propDecidable (s1.memaddrs x))
          (.load .one (.op .add [.var .global (ofString "ev"), .const 32#64])) with _ | vsav
      · rw [hld_sav] at hcont1; dsimp only at hcont1
        injection hcont1 with hr1_eq _; rw [hr_eq, ← hr1_eq]; exact herr_triv
      · obtain ⟨savw, rfl, hsavw_nat⟩ := evalAt_loadG_word s1 "ev" 32#64 vsav hld_sav
        rw [hld_sav] at hcont1; dsimp only at hcont1
        have hsh_sav : shapeEqHOL .one (shapeOfHOLExact (.val (.word savw))) = true := by
          simp [shapeEqHOL, shapeOfHOLExact]
        rw [if_pos hsh_sav] at hcont1; try dsimp only at hcont1
        have hs1_mem : s1.memory = s.memory := by unfold LocFrame at hs1_lf; conv_lhs => rw [hs1_lf]
        have hs1_glob : s1.globals = s.globals := by unfold LocFrame at hs1_lf; conv_lhs => rw [hs1_lf]
        have hsav_eq : savw.toNat = memW s (globN s "ev" + 32) := by
          have h32 : (32#64 : BitVec 64).toNat = 32 := rfl
          rw [hsavw_nat, h32]; simp [memW, globN, hs1_mem, hs1_glob]
        have hsav_cell : s.memory (BitVec.ofNat 64 (globN s "ev" + 32)) = .word savw := by
          have hhead_w : WordAt s (globN s "ev" + 32) := by
            have := (hFW0.1 (globN s "ev", 280) (by simp)).2.2.2 4 (by show 4 < 280 / 8; decide)
            simpa using this
          obtain ⟨w0, _, hw0⟩ := hhead_w
          have hw0_nat : memW s (globN s "ev" + 32) = w0.toNat := by unfold memW; rw [hw0]
          have hw_eq : w0 = savw := BitVec.eq_of_toNat_eq (by omega)
          rwa [← hw_eq]
        set s2 := setVarHOLFinite (ofString "saved") (.val (.word savw)) s1 with hs2_def
        have hs2_lf : LocFrame s s2 := hs1_lf.with_locals_clock _ s1.clock
        have hs2_mem : s2.memory = s.memory := by unfold LocFrame at hs2_lf; conv_lhs => rw [hs2_lf]
        have hs2_ev : s2.globals.lookup (ofString "ev") = some (.val (.word evw)) := by
          simp [hs2_def, setVarHOLFinite, hs1_glob, hevw]
        have hs2_sav : s2.locals.lookup (ofString "saved") = some (.val (.word savw)) := by
          simp [hs2_def, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have hs2_a : s2.locals.lookup (ofString "a") = some (.rStruct [.val (.word acw), .val (.word aebw)]) := by
          simp [hs2_def, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs1_a,
            show ofString "saved" ≠ ofString "a" by decide]
        rcases hcont2 : evaluateHOLFiniteState s2 _ with ⟨r2, p2⟩
        rw [hcont2] at hcont1; dsimp only at hcont1
        injection hcont1 with hr1_eq hp1_eq
        rw [evaluateHOLFiniteState_seq_line780] at hcont2
        rcases hst1 : evaluateHOLFiniteState s2
            (.store (.op .add [.var .global (ofString "ev"), .const 32#64])
              (.op .add [.var .local (ofString "saved"), .rfield 1 (.var .local (ofString "a"))])) with ⟨rst1, s3⟩
        rw [hst1] at hcont2
        rcases rst1 with _ | rst1_val
        · dsimp only at hcont2
          have hev_tmp : @evalHOLExact 64 F _ s2.toExact (fun x => Classical.propDecidable (s2.memaddrs x))
              (.op .add [.var .local (ofString "saved"), .rfield 1 (.var .local (ofString "a"))]) =
              some (.val (.word (savw + aebw))) := by
            simp [evalHOLExact, evalListHOLExact, hs2_sav, hs2_a, wordOpHOL, wordOp, valueIsWord, valueWord]
          obtain ⟨w_tmp, hw_tmp_ev, hs3_eq⟩ := R14Shards.OpHandlersA.store_global_off_word (t := s2) (post := s3)
            (gname := "ev") (gbase := globN s "ev") (off := 32) hs2_ev hevw_nat (by omega)
            (fun v hv => by rw [hev_tmp] at hv; injection hv with hv'; exact ⟨savw + aebw, hv'.symm⟩) hst1
          have hw_tmp_val : w_tmp = savw + aebw := by
            rw [hev_tmp] at hw_tmp_ev
            injection hw_tmp_ev with h1; injection h1 with h2; injection h2 with h3; exact h3.symm
          subst hw_tmp_val
          have hs3_code : s3.code = originalRuntimeCode := by rw [hs3_eq]; exact hs1_code
          have haebw_sum_lt : memW s (globN s "ev" + 32) + aebw.toNat < 2 ^ 37 := by
            rcases ha_gr with rfl | ⟨hb, _⟩
            · have : (0#64 : BitVec 64).toNat = 0 := rfl; omega
            · exact hb
          have haebw_sum_al : (memW s (globN s "ev" + 32) + aebw.toNat) % 32 = 0 := by
            rcases ha_gr with rfl | ⟨_, ha⟩
            · have : (0#64 : BitVec 64).toNat = 0 := rfl; rw [this, Nat.add_zero]; exact hal_s
            · exact ha
          have hsav_add_nat : (savw + aebw).toNat = memW s (globN s "ev" + 32) + aebw.toNat := by
            rw [BitVec.toNat_add, hsav_eq, Nat.mod_eq_of_lt (by omega)]
          have hs3_glob : s3.globals = s.globals := by rw [hs3_eq]; exact hs1_glob
          have hs3_len : memW s3 (globN s3 "ev" + 32) = memW s (globN s "ev" + 32) + aebw.toNat := by
            have hge : globN s3 "ev" = globN s "ev" := by simp [globN, hs3_glob]
            rw [hge, hs3_eq, R14Shards.OpHandlersA.memW_updW_same s2 (globN s "ev" + 32) (savw + aebw), hsav_add_nat]
          have hs3_al : memW s3 (globN s3 "ev" + 32) % 32 = 0 := by rw [hs3_len]; exact haebw_sum_al
          have hnt2 : r2 ≠ some .timeOut := by rw [hr_eq, ← hr1_eq] at hnt; exact hnt
          have hstep2 := decCall_extend_memory_cost1_step_g10 hs3_code hs3_al (by rw [hcont2]; exact hnt2)
          dsimp only at hstep2
          rcases hstep2 with ⟨hne2, hnret2, hnerr2⟩ | ⟨bcw, bebw, s4, hs4_code, hs4_lf, hs4_loc, hb_gr, hrun2⟩
          · rw [hcont2] at hne2 hnret2 hnerr2; dsimp only at hne2 hnret2 hnerr2
            subst hr_eq; subst hr1_eq
            exact ⟨fun v hv => False.elim (hnret2 v hv), fun he => False.elim (hnerr2 he)⟩
          · rw [hcont2] at hrun2
            rcases hcont4 : evaluateHOLFiniteState s4 _ with ⟨r4, p4⟩
            rw [hcont4] at hrun2; dsimp only at hrun2
            injection hrun2 with hr2_eq hp2_eq
            rw [evaluateHOLFiniteState_seq_line780] at hcont4
            have hs4_glob : s4.globals = s.globals := by
              have hg4 : s4.globals = s3.globals := by unfold LocFrame at hs4_lf; conv_lhs => rw [hs4_lf]
              exact hg4.trans hs3_glob
            have hs4_mem : s4.memory = s3.memory := by
              unfold LocFrame at hs4_lf; conv_lhs => rw [hs4_lf]
            have hs4_ev : s4.globals.lookup (ofString "ev") = some (.val (.word evw)) := by
              rw [hs4_glob]; exact hevw
            have hs4_sav : s4.locals.lookup (ofString "saved") = some (.val (.word savw)) := by
              rw [hs4_loc]; simp [hs3_eq, hs2_sav, HolFiniteMapExact.lookup_update, FUPDATE,
                show ofString "b" ≠ ofString "saved" by decide]
            have hs4_a : s4.locals.lookup (ofString "a") = some (.rStruct [.val (.word acw), .val (.word aebw)]) := by
              rw [hs4_loc]; simp [hs3_eq, hs2_a, HolFiniteMapExact.lookup_update, FUPDATE,
                show ofString "b" ≠ ofString "a" by decide]
            have hs4_b : s4.locals.lookup (ofString "b") = some (.rStruct [.val (.word bcw), .val (.word bebw)]) := by
              rw [hs4_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
            rcases hst2 : evaluateHOLFiniteState s4
                (.store (.op .add [.var .global (ofString "ev"), .const 32#64]) (.var .local (ofString "saved"))) with ⟨rst2, s5⟩
            rw [hst2] at hcont4
            rcases rst2 with _ | rst2_val
            · dsimp only at hcont4
              obtain ⟨w_sav', hw_sav_ev, hs5_eq⟩ := R14Shards.OpHandlersA.store_global_off_word (t := s4) (post := s5)
                (gname := "ev") (gbase := globN s "ev") (off := 32) hs4_ev hevw_nat (by omega)
                (fun v hv => by
                  change s4.locals.lookup (ofString "saved") = some v at hv
                  rw [hs4_sav] at hv; injection hv with hv'; exact ⟨savw, hv'.symm⟩) hst2
              have hw_sav_val : w_sav' = savw := by
                change s4.locals.lookup (ofString "saved") = some (.val (.word w_sav')) at hw_sav_ev
                rw [hs4_sav] at hw_sav_ev
                injection hw_sav_ev with h1; injection h1 with h2; injection h2 with h3; exact h3.symm
              subst hw_sav_val
              have hs5_mem : s5.memory = s.memory := by
                rw [hs5_eq]; dsimp only
                funext addr
                unfold R14Shards.OpHandlersA.updW
                by_cases haddr : addr = BitVec.ofNat 64 (globN s "ev" + 32)
                · subst haddr; simp [hsav_cell]
                · simp only [haddr, ↓reduceIte]
                  rw [hs4_mem, hs3_eq]; dsimp only
                  unfold R14Shards.OpHandlersA.updW
                  simp [haddr, hs2_mem]
              have hs5_lf : LocFrame s s5 := by
                have hs4_lf_eq : s4 = { s3 with locals := s4.locals, clock := s4.clock } := hs4_lf
                have hs2_lf_eq : s2 = { s with locals := s2.locals, clock := s2.clock } := hs2_lf
                unfold LocFrame
                rw [hs5_eq]; dsimp only
                conv_lhs => rw [hs4_lf_eq, hs3_eq, hs2_lf_eq]
                dsimp only
                rw [show R14Shards.OpHandlersA.updW
                    (R14Shards.OpHandlersA.updW s.memory (BitVec.ofNat 64 (globN s "ev" + 32)) (w_sav' + aebw))
                    (BitVec.ofNat 64 (globN s "ev" + 32)) w_sav' = s.memory from by
                  funext addr
                  unfold R14Shards.OpHandlersA.updW
                  by_cases haddr : addr = BitVec.ofNat 64 (globN s "ev" + 32)
                  · subst haddr; simp [hsav_cell]
                  · simp [haddr]]
              have hs5_a : s5.locals.lookup (ofString "a") = some (.rStruct [.val (.word acw), .val (.word aebw)]) := by
                rw [hs5_eq]; exact hs4_a
              have hs5_b : s5.locals.lookup (ofString "b") = some (.rStruct [.val (.word bcw), .val (.word bebw)]) := by
                rw [hs5_eq]; exact hs4_b
              rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hcont4
              have hcmp_b : @evalHOLExact 64 F _ s5.toExact (fun x => Classical.propDecidable (s5.memaddrs x))
                  (.cmp .equal (.rfield 0 (.var .local (ofString "b"))) (.const 18446744073709551615#64)) =
                  some (.val (.word (if bcw = 18446744073709551615#64 then 1#64 else 0#64))) := by
                simp [evalHOLExact, hs5_b, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
              rw [hcmp_b] at hcont4; dsimp only at hcont4
              by_cases hbc : bcw = 18446744073709551615#64
              · rw [if_pos hbc, if_neg h10] at hcont4
                rw [hret_rstruct2 s5 (.var .local (ofString "b")) bcw bebw (by simp [evalHOLExact, hs5_b])] at hcont4
                injection hcont4 with hr4_eq hp4_eq
                subst hr_eq; subst hr1_eq; subst hr2_eq; subst hr4_eq
                have hlf_post : LocFrame s post_all := by
                  rw [hp_eq, ← hp1_eq, hp2_eq, ← hp4_eq]
                  exact hs5_lf.with_locals_clock _ s5.clock
                have hb_gr_s : bebw = 0#64 ∨
                    (memW s (globN s "ev" + 32) + bebw.toNat < 2 ^ 37 ∧
                      (memW s (globN s "ev" + 32) + bebw.toNat) % 32 = 0) := by
                  rcases hb_gr with rfl | ⟨hb_lt, hb_al⟩
                  · exact Or.inl rfl
                  · rw [hs3_len] at hb_lt hb_al
                    exact Or.inr ⟨by omega, by omega⟩
                exact hpost_lf hlf_post hb_gr_s
              · rw [if_neg hbc, if_pos h00, evaluateHOLFiniteState_skip] at hcont4; dsimp only at hcont4
                have hev_ret : @evalHOLExact 64 F _ s5.toExact (fun x => Classical.propDecidable (s5.memaddrs x))
                    (.rstruct
                      [.op .add [.rfield 0 (.var .local (ofString "a")), .rfield 0 (.var .local (ofString "b"))],
                       .op .add [.rfield 1 (.var .local (ofString "a")), .rfield 1 (.var .local (ofString "b"))]]) =
                    some (.rStruct [.val (.word (acw + bcw)), .val (.word (aebw + bebw))]) := by
                  simp [evalHOLExact, evalListHOLExact, hs5_a, hs5_b, wordOpHOL, wordOp, valueIsWord, valueWord]
                rw [hret_rstruct2 s5 _ (acw + bcw) (aebw + bebw) hev_ret] at hcont4
                injection hcont4 with hr4_eq hp4_eq
                subst hr_eq; subst hr1_eq; subst hr2_eq; subst hr4_eq
                have hlf_post : LocFrame s post_all := by
                  rw [hp_eq, ← hp1_eq, hp2_eq, ← hp4_eq]
                  exact hs5_lf.with_locals_clock _ s5.clock
                have hab_gr : aebw + bebw = 0#64 ∨
                    (memW s (globN s "ev" + 32) + (aebw + bebw).toNat < 2 ^ 37 ∧
                      (memW s (globN s "ev" + 32) + (aebw + bebw).toNat) % 32 = 0) := by
                  rcases hb_gr with rfl | ⟨hb_lt, hb_al⟩
                  · simp only [BitVec.add_zero]; exact ha_gr
                  · rw [hs3_len] at hb_lt hb_al
                    have hadd_nat : (aebw + bebw).toNat = aebw.toNat + bebw.toNat := by
                      rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
                    exact Or.inr ⟨by omega, by rw [hadd_nat, ← Nat.add_assoc]; exact hb_al⟩
                exact hpost_lf hlf_post hab_gr
            · have herr_st2 := store_some_eq_error_g10 hst2
              subst herr_st2; dsimp only at hcont4
              injection hcont4 with hr4_eq _
              rw [hr_eq, ← hr1_eq, hr2_eq, ← hr4_eq]; exact herr_triv
        · have herr_st1 := store_some_eq_error_g10 hst1
          subst herr_st1; dsimp only at hcont2
          injection hcont2 with hr2_eq _
          rw [hr_eq, ← hr1_eq, ← hr2_eq]; exact herr_triv

theorem HandlerRunA.seq_store_ev_nonstruct {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {P Q : PanSemStateFiniteExact 64 F → Prop} {charged : Bool}
    (off : Nat) (hoff : off ∈ nonStructFrameOffs) {valExp : ExpHOL 64} {cont : ProgHOL 64}
    (hval : ∀ (t : PanSemStateFiniteExact 64 F) (v : ValueHOL 64),
      P t →
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) valExp = some v →
      ∃ w : BitVec 64, v = .val (.word w))
    (hstep : ∀ t (w : BitVec 64),
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) valExp =
        some (.val (.word w)) →
      EvmInv t → P t →
      Q { t with memory := R14Shards.OpHandlersA.updW t.memory (BitVec.ofNat 64 (globN t "ev" + off)) w })
    (hcont : HandlerRunA s0 Q charged cont) :
    HandlerRunA s0 P charged
      (.seq (.store (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 off)]) valExp) cont) := by
  intro t hc hInv hWF hlen hR hP hnt
  have hoff_lt : off + 8 ≤ 280 := by
    simp only [nonStructFrameOffs, List.mem_cons, List.not_mem_nil, or_false] at hoff
    rcases hoff with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  have hoff_safe : off ≠ 24 ∧ off ≠ 32 ∧ off ≠ 40 := by
    simp only [nonStructFrameOffs, List.mem_cons, List.not_mem_nil, or_false] at hoff
    rcases hoff with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  obtain ⟨hb_ev, evw, hevw, hevw_nat⟩ := ev_word_bounds hInv
  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
  rcases hst : evaluateHOLFiniteState t
      (.store (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 off)]) valExp) with ⟨r1, t1⟩
  simp only [hst] at hnt ⊢
  cases r1 with
  | some res1 =>
    have herr := store_some_eq_error_g10 hst
    subst herr
    exact opDispatchPostA_error s0 t1
  | none =>
    dsimp only at hnt ⊢
    obtain ⟨w, hw_ev, ht1_eq⟩ := R14Shards.OpHandlersA.store_global_off_word (t := t) (post := t1)
      (gname := "ev") (gbase := globN t "ev") (off := off) hevw hevw_nat (by omega)
      (fun v hv => hval t v hP hv) hst
    have hGt1 : GuestInv t1 := guestInv_congr (s := t)
      (by simp [ht1_eq]) (by simp [ht1_eq]) (by simp [ht1_eq]) (by simp [ht1_eq]) hInv.1.1
    have hmem_out : ∀ x : BitVec 64,
        (∀ off' ∈ nonStructFrameOffs, x ≠ BitVec.ofNat 64 (globN t "ev" + off')) →
        t1.memory x = t.memory x := by
      intro x hx
      rw [ht1_eq]
      dsimp only [R14Shards.OpHandlersA.updW]
      rw [if_neg (hx off hoff)]
    obtain ⟨hInv1, hch1, hR1_eq⟩ := evmInv_of_head_nonstruct hInv hGt1
      (by simp [ht1_eq]) (by simp [ht1_eq]) hmem_out
    have hWF1 : Group10.HeadMemChainWF t1 := by
      apply headMemChainWF_store_headSafe hInv hWF
        (x := BitVec.ofNat 64 (globN t "ev" + off))
      · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        exact Or.inl ⟨off, rfl, by omega, hoff_safe.1, hoff_safe.2.1, hoff_safe.2.2⟩
      · simp [ht1_eq]
      · exact hch1
      · intro a ha
        simp [ht1_eq, R14Shards.OpHandlersA.updW, ha]
    have hQ1 : Q t1 := by
      rw [ht1_eq]
      exact hstep t w hw_ev hInv hP
    exact hcont t1 (by rw [ht1_eq]; exact hc) hInv1 hWF1
      (by rw [hch1]; exact hlen) (by rw [hR1_eq]; exact hR) hQ1 hnt

theorem HandlerRunA.ret_done {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    (hRun : EvmRun s0) {P : PanSemStateFiniteExact 64 F → Prop} {charged : Bool}
    (hdone : ∀ t, EvmInv t → P t → EvmDone t) (e : ExpHOL 64) :
    HandlerRunA s0 P charged (.return e) := by
  intro t _ hInv hWF hlen hR hP _
  have hR_le : evmR t ≤ evmR s0 := rboundA_to_le hR
  rw [evaluateHOLFiniteState_return]
  split
  · exact opDispatchPostA_error s0 t
  · split
    · have hInv' : EvmInv (emptyLocalsHOLFinite t) :=
        localsFree_evmInv t (emptyLocalsHOLFinite t).locals t.clock hInv
      have hWF' := Group10.headMemChainWF_locals t (emptyLocalsHOLFinite t).locals t.clock hWF
      have hc := evm_congr (s := t) (t := emptyLocalsHOLFinite t) rfl rfl
      have hDone' : EvmDone (emptyLocalsHOLFinite t) := by
        unfold EvmDone globN memW
        exact hdone t hInv hP
      refine ⟨fun _ => ⟨⟨hInv', hWF'⟩, evmPot_lt_of_done hRun hInv' hDone'
        (by rw [hc.2.2.1, hlen]) (by rw [hc.2.1]; exact hR_le)⟩, ?_⟩
      rintro ⟨_, h⟩
      cases h
    · exact opDispatchPostA_error s0 t

theorem epsA_charge_gas_keep32 :
    EvmPreservingSpecA (fun _ => True)
      (fun s _ post => post.globals = s.globals ∧ memW post (globN s "ev" + 32) = memW s (globN s "ev" + 32))
      (ofString "charge_gas") := by
  refine ⟨_, _, _, M21.lookup_charge_gas, ?_⟩
  intro F s _ hInv hWF _ ⟨vals, hl⟩ _
  have hlen1 : ∃ v0, vals = [v0] := by
    have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
      originalRuntimeCode.lookup (ofString "charge_gas") vals _ _ _ hl
    simp only [Flapjack.lookupCodeHOLExact, M21.lookup_charge_gas] at hx
    rcases vals with _ | ⟨v0, _ | _⟩ <;> simp at hx
    exact ⟨v0, rfl⟩
  obtain ⟨v0, rfl⟩ := hlen1
  obtain ⟨_, _, amtw, rfl, hamt⟩ := one_word_arg_lookup M21.lookup_charge_gas hl
  have hcg := charge_gas_body_exactA s hInv hWF hamt
  dsimp only at hcg ⊢
  obtain ⟨hb_ev, _, _, _⟩ := ev_word_bounds hInv
  have hm32 : ∀ v, (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_charge_gas)).1 =
      some (.returned v) →
      memW (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_charge_gas)).2 (globN s "ev" + 32) =
        memW s (globN s "ev" + 32) := by
    intro v hv
    have hnot_err : ¬ ((some (.returned v) : Option (PanSemResultExact 64)) = some .error) := by
      intro h; cases h
    have hbody : sourceFnBody Guest.Software.guestFn_charge_gas =
        .dec (ofString "gl") .one (.load .one (.op .add [.var .global (ofString "ev"), .const 64]))
          (.seq
            (.ite (.cmp .lower (.var .local (ofString "gl")) (.var .local (ofString "amount")))
              (.raise (ofString "EvmErr") (.const 4))
              .skip)
            (.seq
              (.store (.op .add [.var .global (ofString "ev"), .const 64])
                (.op .sub [.var .local (ofString "gl"), .var .local (ofString "amount")]))
              (.seq
                (.store (.op .add [.var .global (ofString "ev"), .const 184])
                  (.op .add
                    [.load .one (.op .add [.var .global (ofString "ev"), .const 184]),
                     .var .local (ofString "amount")]))
                (.return (.const 0))))) := rfl
    obtain ⟨_, evw, hevw, hevw_nat⟩ := ev_word_bounds hInv
    revert hv
    rw [hbody, evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · intro hv; cases hv
    · rename_i glv _
      split
      · dsimp only
        set s1 := setVarHOLFinite (ofString "gl") glv s
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
        split
        · split
          · simp only [evaluateHOLFiniteState_skip]
            rw [evaluateHOLFiniteState_seq_line780]
            rcases hst1 : evaluateHOLFiniteState s1
                (.store (.op .add [.var .global (ofString "ev"), .const 64])
                  (.op .sub [.var .local (ofString "gl"), .var .local (ofString "amount")])) with ⟨r1, s2⟩
            cases r1 with
            | some res1 =>
              have herr1 := store_some_eq_error_g10 hst1; subst herr1; dsimp only
              intro hv; cases hv
            | none =>
              dsimp only
              obtain ⟨w1, _, hs2_eq⟩ := R14Shards.OpHandlersA.store_global_off_word (t := s1) (post := s2)
                (gname := "ev") (gbase := globN s "ev") (off := 64) hevw hevw_nat (by omega)
                (fun u hu => by
                  simp only [evalHOLExact, wordOpHOL] at hu; revert hu
                  rcases @evalListHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a)) _ with _ | vs
                  · simp
                  · dsimp only; split
                    · simp only [Option.map]
                      rcases wordOp .sub (vs.map valueWord) with _ | w
                      · simp
                      · intro hu; injection hu with hu'; exact ⟨w, hu'.symm⟩
                    · simp) hst1
              rw [evaluateHOLFiniteState_seq_line780]
              rcases hst2 : evaluateHOLFiniteState s2
                  (.store (.op .add [.var .global (ofString "ev"), .const 184])
                    (.op .add
                      [.load .one (.op .add [.var .global (ofString "ev"), .const 184]),
                       .var .local (ofString "amount")])) with ⟨r2, s3⟩
              cases r2 with
              | some res2 =>
                have herr2 := store_some_eq_error_g10 hst2; subst herr2; dsimp only
                intro hv; cases hv
              | none =>
                dsimp only
                obtain ⟨w2, _, hs3_eq⟩ := R14Shards.OpHandlersA.store_global_off_word (t := s2) (post := s3)
                  (gname := "ev") (gbase := globN s "ev") (off := 184)
                  (by rw [hs2_eq]; exact hevw) hevw_nat (by omega)
                  (fun u hu => by
                    simp only [evalHOLExact, wordOpHOL] at hu; revert hu
                    rcases @evalListHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a)) _ with _ | vs
                    · simp
                    · dsimp only; split
                      · simp only [Option.map]
                        rcases wordOp .add (vs.map valueWord) with _ | w
                        · simp
                        · intro hu; injection hu with hu'; exact ⟨w, hu'.symm⟩
                      · simp) hst2
                have hx32_64 : BitVec.ofNat 64 (globN s "ev" + 32) ≠ BitVec.ofNat 64 (globN s "ev" + 64) := by
                  intro h; have := congrArg BitVec.toNat h
                  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
                  omega
                have hx32_184 : BitVec.ofNat 64 (globN s "ev" + 32) ≠ BitVec.ofNat 64 (globN s "ev" + 184) := by
                  intro h; have := congrArg BitVec.toNat h
                  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
                  omega
                have hs3_m32 : memW s3 (globN s "ev" + 32) = memW s (globN s "ev" + 32) := by
                  unfold memW
                  rw [hs3_eq]; dsimp only [R14Shards.OpHandlersA.updW]; rw [if_neg hx32_184, hs2_eq]
                  dsimp only [R14Shards.OpHandlersA.updW]; rw [if_neg hx32_64]; rfl
                rw [evaluateHOLFiniteState_return]
                split
                · intro hv; cases hv
                · split
                  · intro _; exact hs3_m32
                  · intro hv; cases hv
          · rcases hraise : evaluateHOLFiniteState s1 (.raise (ofString "EvmErr") (.const 4)) with ⟨rr, sr⟩
            have hr_ne : ∀ u, rr ≠ some (.returned u) := by
              intro u
              rw [evaluateHOLFiniteState_raise] at hraise; dsimp only [evalHOLExact] at hraise
              split at hraise
              · split at hraise <;> (injection hraise with h1 _; subst h1; simp)
              · injection hraise with h1 _; subst h1; simp
            cases rr with
            | none =>
              exfalso
              exact raise_ne_none s1 (ofString "EvmErr") (.const 4) (by rw [hraise])
            | some rr0 =>
              dsimp only; intro hv; exact absurd hv (hr_ne v)
        · intro hv; cases hv
      · intro hv; cases hv
  refine ⟨fun v hv => ?_, fun herr => ?_⟩
  · obtain ⟨hIW, hg, hch, hR⟩ := hcg.1 v hv
    exact ⟨hIW, hch, by change _ + _ = _ at hR; omega, hg, hm32 v hv⟩
  · obtain ⟨hIW, _, hch, hR⟩ := hcg.2 herr
    exact ⟨hIW, hch, le_of_eq hR⟩

theorem HandlerRunA.decCall_shaped {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {P Q : PanSemStateFiniteExact 64 F → Prop}
    {Pc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {Qc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    {charged : Bool}
    {nm : MlS} {sh : ShapeHOL} {fname : MlS} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (hf : EvmPreservingSpecA Pc Qc fname)
    (hentry : ∀ t values body' callee ret',
      t.code = originalRuntimeCode → EvmInv t → Group10.HeadMemChainWF t → P t →
      evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) args = some values →
      lookupCodeHOLFinite t.code.lookup fname values = some (body', callee, ret') →
      Pc (callEntryStateHOLFinite t callee))
    (hstep : ∀ t values body callee retShape v cpost,
      EvmInv t → Group10.HeadMemChainWF t → P t →
      shapeEqHOL (shapeOfHOLExact v) sh = true →
      evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) args = some values →
      lookupCodeHOLFinite originalRuntimeCode.lookup fname values = some (body, callee, retShape) →
      EvmInv cpost → Group10.HeadMemChainWF cpost →
      evmChain cpost = evmChain (callEntryStateHOLFinite t callee) →
      Qc (callEntryStateHOLFinite t callee) v cpost →
      Q (setVarHOLFinite nm v { cpost with locals := t.locals }))
    (hcont : HandlerRunA s0 Q charged cont) :
    HandlerRunA s0 P charged (.decCall nm sh fname args cont) := by
  intro t hc hi hw hlen hR hp hn
  obtain ⟨params, body, retShape, hlook, hspec⟩ := hf
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hn ⊢
  rcases hargs : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) args with _ | values
  · exact opDispatchPostA_error s0 t
  · simp only [hargs] at hn ⊢
    rcases hl : lookupCodeHOLFinite t.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · exact opDispatchPostA_error s0 t
    · simp only [hl] at hn ⊢
      by_cases hz : t.clock = 0
      · simp [hz] at hn
      · simp only [hz, ↓reduceIte] at hn ⊢
        have hbody_eq : body' = body :=
          lookupCodeHOLFinite_installed_body t.code.lookup fname params body body'
            retShape ret' values callee (by rw [hc]; exact hlook) hl
        subst body'
        have hret_eq : ret' = retShape := by
          have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
            t.code.lookup fname values body callee ret' hl
          rw [hc] at hx; simp only [Flapjack.lookupCodeHOLExact, hlook] at hx
          split at hx
          · exact (congrArg (fun x => x.2.2) (Option.some.inj hx)).symm
          · cases hx
        subst ret'
        have hi_ce : EvmInv (callEntryStateHOLFinite t callee) := localsFree_evmInv t callee (t.clock - 1) hi
        have hw_ce : Group10.HeadMemChainWF (callEntryStateHOLFinite t callee) :=
          Group10.headMemChainWF_locals t callee (t.clock - 1) hw
        have hPc : Pc (callEntryStateHOLFinite t callee) := hentry t values body callee retShape hc hi hw hp hargs hl
        have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup fname values =
            some (body, callee, retShape) := by rwa [← hc]
        have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite t callee) body).1
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite t callee) body with ⟨res, cpost⟩
        simp only [hrun] at hn hmeta ⊢
        change cpost.code = t.code at hmeta
        have hc_ce := evm_congr (s := t) (t := callEntryStateHOLFinite t callee) rfl rfl
        have hQ (hsafe : res ≠ some .timeOut) :
            (∀ v, res = some (.returned v) →
              (EvmInv cpost ∧ Group10.HeadMemChainWF cpost) ∧
              evmChain cpost = evmChain (callEntryStateHOLFinite t callee) ∧
              evmR cpost ≤ evmR (callEntryStateHOLFinite t callee) ∧
              Qc (callEntryStateHOLFinite t callee) v cpost) ∧
            (IsEvmErr res →
              (EvmInv cpost ∧ Group10.HeadMemChainWF cpost) ∧
              evmChain cpost = evmChain (callEntryStateHOLFinite t callee) ∧
              evmR cpost ≤ evmR (callEntryStateHOLFinite t callee)) := by
          have hs := hspec (callEntryStateHOLFinite t callee) hc hi_ce hw_ce hPc ⟨values, hl_orig⟩
            (by rw [hrun]; exact hsafe)
          dsimp only at hs; rw [hrun] at hs; exact hs
        cases res with
        | none => exact opDispatchPostA_error s0 cpost
        | some r0 =>
          cases r0 with
          | timeOut => simp at hn
          | returned v =>
            dsimp only at hn ⊢
            split
            · rename_i hsh_ok
              rw [if_pos hsh_ok] at hn
              have hsh_v : shapeEqHOL (shapeOfHOLExact v) sh = true := by
                simp only [Bool.and_eq_true] at hsh_ok; exact hsh_ok.1
              obtain ⟨⟨hi_cp, hw_cp⟩, hch_cp, hR_cp, hQc_cp⟩ := (hQ (by simp)).1 v rfl
              let resumed := setVarHOLFinite nm v { cpost with locals := t.locals }
              have hcode_res : resumed.code = originalRuntimeCode := hmeta.trans hc
              have hi_res : EvmInv resumed := localsFree_evmInv cpost resumed.locals cpost.clock hi_cp
              have hw_res : Group10.HeadMemChainWF resumed :=
                Group10.headMemChainWF_locals cpost resumed.locals cpost.clock hw_cp
              have hc_res := evm_congr (s := cpost) (t := resumed) rfl rfl
              have hlen_res : (evmChain resumed).length = (evmChain s0).length := by
                rw [hc_res.2.2.1, hch_cp, hc_ce.2.2.1]; exact hlen
              have hR_res : if charged then evmR resumed < evmR s0 else evmR resumed ≤ evmR s0 :=
                rboundA_step (by rw [hc_res.2.1]; rw [hc_ce.2.1] at hR_cp; exact hR_cp) hR
              have hQ_res : Q resumed :=
                hstep t values body callee retShape v cpost hi hw hp hsh_v hargs hl_orig hi_cp hw_cp hch_cp hQc_cp
              have hb := hcont resumed hcode_res hi_res hw_res hlen_res hR_res hQ_res (by simpa [resumed] using hn)
              exact opDispatchPostA_congr_lc rfl hb
            · exact opDispatchPostA_error s0 cpost
          | exception eid ev =>
            by_cases heid : eid = ofString "EvmErr"
            · subst heid
              obtain ⟨⟨hi_cp, hw_cp⟩, hch_cp, hR_cp⟩ := (hQ (by simp)).2 ⟨ev, rfl⟩
              have hi_el : EvmInv cpost.emptyLocalsHOLFinite :=
                localsFree_evmInv cpost _ cpost.clock hi_cp
              have hw_el : Group10.HeadMemChainWF cpost.emptyLocalsHOLFinite :=
                Group10.headMemChainWF_locals cpost _ cpost.clock hw_cp
              have hc_el := evm_congr (s := cpost) (t := cpost.emptyLocalsHOLFinite) rfl rfl
              refine ⟨?_, fun _ => ⟨⟨hi_el, hw_el⟩, ?_, ?_⟩⟩
              · rintro ⟨_, h⟩; cases h
              · rw [hc_el.2.2.1, hch_cp, hc_ce.2.2.1]; exact hlen
              · have := rboundA_to_le hR; rw [hc_el.2.1]; rw [hc_ce.2.1] at hR_cp; omega
            · refine opDispatchPostA_other (fun _ h => by cases h) ?_
              rintro ⟨_, h⟩; injection h with h'; injection h' with h1 _; exact heid h1
          | «break» => exact opDispatchPostA_error s0 cpost
          | «continue» => exact opDispatchPostA_error s0 cpost
          | finalFfi _ =>
            refine opDispatchPostA_other (fun _ h => by cases h) ?_
            rintro ⟨_, h⟩; cases h
          | error => exact opDispatchPostA_error s0 cpost.emptyLocalsHOLFinite

private theorem shapeEq_one_iff_g10 (v : ValueHOL 64)
    (h : shapeEqHOL (shapeOfHOLExact v) .one = true) :
    ∃ w : BitVec 64, v = .val (.word w) := by
  cases v with
  | val wl =>
    cases wl with
    | word w => exact ⟨w, rfl⟩
  | rStruct _ => simp [shapeOfHOLExact, shapeEqHOL] at h
  | nStruct _ _ => simp [shapeOfHOLExact, shapeEqHOL] at h

private theorem eval_add_word_g10 {F : Type} {t : PanSemStateFiniteExact 64 F}
    {e1 e2 : ExpHOL 64} {v : ValueHOL 64}
    (hv : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
      (.op .add [e1, e2]) = some v) :
    ∃ w : BitVec 64, v = .val (.word w) := by
  simp only [evalHOLExact, wordOpHOL] at hv
  revert hv
  rcases @evalListHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) [e1, e2] with _ | vs
  · simp
  · dsimp only
    split
    · simp only [Option.map]
      rcases wordOp .add (vs.map valueWord) with _ | w
      · simp
      · intro hv; injection hv with hv'; exact ⟨w, hv'.symm⟩
    · simp

theorem op_return_specA : OpHandlerSpecA (ofString "op_return") := by
  refine opHandlerSpecA_of_run 568 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_return rfl ?_
  intro F s0 hInv0 _ hnd0
  have hRun0 : EvmRun s0 := ⟨hInv0, hnd0⟩
  dsimp only [Guest.Software.guestFn_op_return, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    List.map]
  refine HandlerRunA.decCall_simple epsA_stack_pop ?_
  refine HandlerRunA.decCall_simple epsA_stack_pop ?_
  refine HandlerRunA.decCall
    (Q := fun t =>
      ∃ cw ebw : BitVec 64,
        t.locals.lookup (ofString "x") = some (.rStruct [.val (.word cw), .val (.word ebw)]) ∧
        (ebw = 0#64 ∨
          (memW t (globN t "ev" + 32) + ebw.toNat < 2 ^ 37 ∧
            (memW t (globN t "ev" + 32) + ebw.toNat) % 32 = 0)))
    epsA_extend_memory_cost1_aligned
    (fun _ _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun t _ _ callee _ v cpost _ _ _ _ _ _ _ _ hQc => by
      obtain ⟨hlf, cw, ebw, rfl, heb⟩ := hQc
      let res := setVarHOLFinite (ofString "x") (.rStruct [.val (.word cw), .val (.word ebw)]) { cpost with locals := t.locals }
      refine ⟨cw, ebw, by simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE], ?_⟩
      have hg : globN res "ev" = globN (callEntryStateHOLFinite t callee) "ev" := by
        change globN cpost "ev" = globN (callEntryStateHOLFinite t callee) "ev"
        exact congrFun (globN_congr (congrArg PanSemStateFiniteExact.globals hlf)) "ev"
      have hm : memW res (globN (callEntryStateHOLFinite t callee) "ev" + 32) =
          memW (callEntryStateHOLFinite t callee) (globN (callEntryStateHOLFinite t callee) "ev" + 32) := by
        change memW cpost _ = _
        unfold memW; rw [congrArg PanSemStateFiniteExact.memory hlf]
      change ebw = 0#64 ∨ (memW res (globN res "ev" + 32) + ebw.toNat < 2 ^ 37 ∧ (memW res (globN res "ev" + 32) + ebw.toNat) % 32 = 0)
      rw [hg, hm]
      exact heb)
    ?_
  refine HandlerRunA.seq_call
    (Q := fun t =>
      ∃ cw ebw : BitVec 64,
        t.locals.lookup (ofString "x") = some (.rStruct [.val (.word cw), .val (.word ebw)]) ∧
        (ebw = 0#64 ∨
          (memW t (globN t "ev" + 32) + ebw.toNat < 2 ^ 37 ∧
            (memW t (globN t "ev" + 32) + ebw.toNat) % 32 = 0)))
    epsA_charge_gas_keep32
    (fun _ _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun t _ _ callee _ _ cpost _ _ ⟨cw, ebw, hx, heb⟩ _ _ _ _ _ ⟨hg_cp, hm32_cp⟩ => by
      let res : PanSemStateFiniteExact 64 F := { cpost with locals := t.locals }
      refine ⟨cw, ebw, hx, ?_⟩
      have hg_ce : globN (callEntryStateHOLFinite t callee) "ev" = globN t "ev" := rfl
      have hg_eq : globN res "ev" = globN t "ev" := by
        change globN cpost "ev" = globN t "ev"
        rw [globN_congr hg_cp]; exact hg_ce
      have hm32_eq : memW res (globN t "ev" + 32) = memW t (globN t "ev" + 32) := by
        change memW cpost (globN t "ev" + 32) = memW t (globN t "ev" + 32)
        rw [hg_ce] at hm32_cp
        exact hm32_cp
      change ebw = 0#64 ∨ (memW res (globN res "ev" + 32) + ebw.toNat < 2 ^ 37 ∧ (memW res (globN res "ev" + 32) + ebw.toNat) % 32 = 0)
      rw [hg_eq, hm32_eq]
      exact heb)
    ?_
  refine HandlerRunA.seq_call
    (Q := fun _ => True)
    epsA_extend_memory
    (fun t values b_em callee rs_em hc _ hw ⟨cw, ebw, hx, heb⟩ hargs hl => by
      have hx1 : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
          [.rfield 1 (.var .local (ofString "x"))] = some [.val (.word ebw)] := by
        rw [evalListHOLFinite_eq_toExact]
        simp [evalListHOLExact, evalHOLExact, hx]
      rw [hx1] at hargs; injection hargs with hvs; subst hvs
      have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "extend_memory") [.val (.word ebw)] =
          some (b_em, callee, rs_em) := by rwa [← hc]
      obtain ⟨_, _, ebw', heq_eb, hcal_eb⟩ := one_word_arg_lookup Group10.lookup_extend_memory hl_orig
      injection heq_eb with heq1; injection heq1 with heq2; subst heq2
      rcases heb with rfl | ⟨hb_lt, hb_32⟩
      · exact ⟨0#64, hcal_eb, Or.inl rfl⟩
      · exact Group10.extendMemoryPre_of_headMemAligned
          (Group10.headMemChainWF_headMemAligned (Group10.headMemChainWF_locals t callee (t.clock - 1) hw))
          ebw hcal_eb hb_lt hb_32)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial)
    ?_
  refine HandlerRunA.decCall_shaped
    (Q := fun t => ∃ nw : BitVec 64, t.locals.lookup (ofString "n") = some (.val (.word nw)))
    epsA_sat_word
    (fun _ _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ v _ _ _ _ hsh _ _ _ _ _ _ => by
      obtain ⟨nw, rfl⟩ := shapeEq_one_iff_g10 v hsh
      exact ⟨nw, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩)
    ?_
  refine HandlerRunA.decCall_shaped
    (Q := fun t => ∃ nw : BitVec 64, t.locals.lookup (ofString "n") = some (.val (.word nw)))
    epsA_sat_word
    (fun _ _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ _ _ _ ⟨nw, hn_lk⟩ _ _ _ _ _ _ _ => by
      have hne : ofString "s" ≠ ofString "n" := by decide
      exact ⟨nw, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne, hn_lk]⟩)
    ?_
  refine HandlerRunA.seq_store_ev_nonstruct
    (Q := fun t => ∃ nw : BitVec 64, t.locals.lookup (ofString "n") = some (.val (.word nw)))
    120 (by simp [nonStructFrameOffs])
    (fun _ _ _ hv => eval_add_word_g10 hv)
    (fun _ _ _ _ ⟨nw, hn_lk⟩ => ⟨nw, hn_lk⟩)
    ?_
  refine HandlerRunA.seq_store_ev_nonstruct
    (Q := fun _ => True)
    128 (by simp [nonStructFrameOffs])
    (fun t v ⟨nw, hn_lk⟩ hv => by
      change t.locals.lookup (ofString "n") = some v at hv
      rw [hn_lk] at hv; injection hv with hv'; exact ⟨nw, hv'.symm⟩)
    (fun _ _ _ _ _ => trivial)
    ?_
  refine HandlerRunA.seq_store_ev_nonstruct
    (Q := fun t => memW t (globN t "ev" + 104) = 0)
    104 (by simp [nonStructFrameOffs])
    (fun _ v _ hv => by
      change some (ValueHOL.val (.word 0#64)) = some v at hv
      injection hv with hv'
      exact ⟨0, hv'.symm⟩)
    (fun t w hw _ _ => by
      change some (ValueHOL.val (.word 0#64)) = some (.val (.word w)) at hw
      injection hw with hw1; injection hw1 with hw2; injection hw2 with hw3; subst hw3
      simpa [globN] using R14Shards.OpHandlersA.memW_updW_same t (globN t "ev" + 104) 0)
    (HandlerRunA.ret_done hRun0 (fun _ _ hP => Or.inr (Or.inl hP)) _)

theorem HandlerRunA.seq_raise_evmErr {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {P : PanSemStateFiniteExact 64 F → Prop} {charged : Bool}
    (errExp : ExpHOL 64) (cont : ProgHOL 64) :
    HandlerRunA s0 P charged (.seq (.raise (ofString "EvmErr") errExp) cont) := by
  intro t hc hi hw hlen hR hp hn
  rw [evaluateHOLFiniteState_seq_line780] at hn ⊢
  rcases hraise : evaluateHOLFiniteState t (.raise (ofString "EvmErr") errExp) with ⟨rr, sr⟩
  simp only [hraise] at hn ⊢
  cases rr with
  | none => exact absurd hraise (fun h => raise_ne_none t _ errExp (by rw [h]))
  | some _ =>
    dsimp only at hn ⊢
    have hr := (HandlerRunA.raise_evmErr (P := P) (charged := charged) errExp) t hc hi hw hlen hR hp
      (by rw [hraise]; exact hn)
    rw [hraise] at hr
    exact hr

theorem op_revert_specA : OpHandlerSpecA (ofString "op_revert") := by
  refine opHandlerSpecA_of_run 569 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_revert rfl ?_
  intro F s0 _ _ _
  dsimp only [Guest.Software.guestFn_op_revert, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    List.map]
  refine HandlerRunA.decCall_simple epsA_stack_pop ?_
  refine HandlerRunA.decCall_simple epsA_stack_pop ?_
  refine HandlerRunA.decCall
    (Q := fun t =>
      ∃ cw ebw : BitVec 64,
        t.locals.lookup (ofString "x") = some (.rStruct [.val (.word cw), .val (.word ebw)]) ∧
        (ebw = 0#64 ∨
          (memW t (globN t "ev" + 32) + ebw.toNat < 2 ^ 37 ∧
            (memW t (globN t "ev" + 32) + ebw.toNat) % 32 = 0)))
    epsA_extend_memory_cost1_aligned
    (fun _ _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun t _ _ callee _ v cpost _ _ _ _ _ _ _ _ hQc => by
      obtain ⟨hlf, cw, ebw, rfl, heb⟩ := hQc
      let res := setVarHOLFinite (ofString "x") (.rStruct [.val (.word cw), .val (.word ebw)]) { cpost with locals := t.locals }
      refine ⟨cw, ebw, by simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE], ?_⟩
      have hg : globN res "ev" = globN (callEntryStateHOLFinite t callee) "ev" := by
        change globN cpost "ev" = globN (callEntryStateHOLFinite t callee) "ev"
        exact congrFun (globN_congr (congrArg PanSemStateFiniteExact.globals hlf)) "ev"
      have hm : memW res (globN (callEntryStateHOLFinite t callee) "ev" + 32) =
          memW (callEntryStateHOLFinite t callee) (globN (callEntryStateHOLFinite t callee) "ev" + 32) := by
        change memW cpost _ = _
        unfold memW; rw [congrArg PanSemStateFiniteExact.memory hlf]
      change ebw = 0#64 ∨ (memW res (globN res "ev" + 32) + ebw.toNat < 2 ^ 37 ∧ (memW res (globN res "ev" + 32) + ebw.toNat) % 32 = 0)
      rw [hg, hm]
      exact heb)
    ?_
  refine HandlerRunA.seq_call
    (Q := fun t =>
      ∃ cw ebw : BitVec 64,
        t.locals.lookup (ofString "x") = some (.rStruct [.val (.word cw), .val (.word ebw)]) ∧
        (ebw = 0#64 ∨
          (memW t (globN t "ev" + 32) + ebw.toNat < 2 ^ 37 ∧
            (memW t (globN t "ev" + 32) + ebw.toNat) % 32 = 0)))
    epsA_charge_gas_keep32
    (fun _ _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun t _ _ callee _ _ cpost _ _ ⟨cw, ebw, hx, heb⟩ _ _ _ _ _ ⟨hg_cp, hm32_cp⟩ => by
      let res : PanSemStateFiniteExact 64 F := { cpost with locals := t.locals }
      refine ⟨cw, ebw, hx, ?_⟩
      have hg_ce : globN (callEntryStateHOLFinite t callee) "ev" = globN t "ev" := rfl
      have hg_eq : globN res "ev" = globN t "ev" := by
        change globN cpost "ev" = globN t "ev"
        rw [globN_congr hg_cp]; exact hg_ce
      have hm32_eq : memW res (globN t "ev" + 32) = memW t (globN t "ev" + 32) := by
        change memW cpost (globN t "ev" + 32) = memW t (globN t "ev" + 32)
        rw [hg_ce] at hm32_cp
        exact hm32_cp
      change ebw = 0#64 ∨ (memW res (globN res "ev" + 32) + ebw.toNat < 2 ^ 37 ∧ (memW res (globN res "ev" + 32) + ebw.toNat) % 32 = 0)
      rw [hg_eq, hm32_eq]
      exact heb)
    ?_
  refine HandlerRunA.seq_call
    (Q := fun _ => True)
    epsA_extend_memory
    (fun t values b_em callee rs_em hc _ hw ⟨cw, ebw, hx, heb⟩ hargs hl => by
      have hx1 : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
          [.rfield 1 (.var .local (ofString "x"))] = some [.val (.word ebw)] := by
        rw [evalListHOLFinite_eq_toExact]
        simp [evalListHOLExact, evalHOLExact, hx]
      rw [hx1] at hargs; injection hargs with hvs; subst hvs
      have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "extend_memory") [.val (.word ebw)] =
          some (b_em, callee, rs_em) := by rwa [← hc]
      obtain ⟨_, _, ebw', heq_eb, hcal_eb⟩ := one_word_arg_lookup Group10.lookup_extend_memory hl_orig
      injection heq_eb with heq1; injection heq1 with heq2; subst heq2
      rcases heb with rfl | ⟨hb_lt, hb_32⟩
      · exact ⟨0#64, hcal_eb, Or.inl rfl⟩
      · exact Group10.extendMemoryPre_of_headMemAligned
          (Group10.headMemChainWF_headMemAligned (Group10.headMemChainWF_locals t callee (t.clock - 1) hw))
          ebw hcal_eb hb_lt hb_32)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial)
    ?_
  refine HandlerRunA.decCall_shaped
    (Q := fun t => ∃ nw : BitVec 64, t.locals.lookup (ofString "n") = some (.val (.word nw)))
    epsA_sat_word
    (fun _ _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ v _ _ _ _ hsh _ _ _ _ _ _ => by
      obtain ⟨nw, rfl⟩ := shapeEq_one_iff_g10 v hsh
      exact ⟨nw, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩)
    ?_
  refine HandlerRunA.decCall_shaped
    (Q := fun t => ∃ nw : BitVec 64, t.locals.lookup (ofString "n") = some (.val (.word nw)))
    epsA_sat_word
    (fun _ _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ _ _ _ ⟨nw, hn_lk⟩ _ _ _ _ _ _ _ => by
      have hne : ofString "s" ≠ ofString "n" := by decide
      exact ⟨nw, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne, hn_lk]⟩)
    ?_
  refine HandlerRunA.seq_store_ev_nonstruct
    (Q := fun t => ∃ nw : BitVec 64, t.locals.lookup (ofString "n") = some (.val (.word nw)))
    120 (by simp [nonStructFrameOffs])
    (fun _ _ _ hv => eval_add_word_g10 hv)
    (fun _ _ _ _ ⟨nw, hn_lk⟩ => ⟨nw, hn_lk⟩)
    ?_
  refine HandlerRunA.seq_store_ev_nonstruct
    (Q := fun _ => True)
    128 (by simp [nonStructFrameOffs])
    (fun t v ⟨nw, hn_lk⟩ hv => by
      change t.locals.lookup (ofString "n") = some v at hv
      rw [hn_lk] at hv; injection hv with hv'; exact ⟨nw, hv'.symm⟩)
    (fun _ _ _ _ _ => trivial)
    (HandlerRunA.seq_raise_evmErr _ _)

/-! ## `op_selfdestruct_specA` and `WorldAccountSpecsA` -/

theorem epsA_memeq_ro :
    EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "memeq") :=
  epsA_of_readOnly 18 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_memeq rfl
    opRoCallees opRoCallees_good rfl

theorem epsA_htab_has_ro :
    EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "htab_has") :=
  epsA_of_readOnly 133 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_htab_has rfl
    opRoCallees opRoCallees_good rfl

theorem epsA_htab_set_head_del :
    EvmPreservingSpecA
      (fun s => locN s "t" = memW s (globN s "ev" + 136))
      (fun s _ post => GlobalsKept ["heap_ptr"] s post ∧ evmR post = evmR s)
      (ofString "htab_set") := by
  obtain ⟨params, body, rs, hlk, hfn_spec⟩ := SoloHtabSet.htab_set_spec_proof
  refine ⟨params, body, rs, hlk, ?_⟩
  intro F s hcode hInv hHMWF ht_eq hlookup hnt
  have hbody_eq : ([(ofString "t", ShapeHOL.one), (ofString "key", ShapeHOL.one), (ofString "value", ShapeHOL.one)],
      sourceFnBody Guest.Software.guestFn_htab_set, ShapeHOL.one) = (params, body, rs) :=
    Option.some.inj (SoloHtabSet.lookup_htab_set.symm.trans hlk)
  rcases Prod.mk.inj hbody_eq with ⟨_, hbr⟩
  rcases Prod.mk.inj hbr with ⟨hb_eq, _⟩
  subst hb_eq
  obtain ⟨hAs, S, hInvAt⟩ := hInv
  have hhead_mem : (globN s "ev", globN s "cur_cont") ∈ evmChain s := List.mem_cons_self
  have ht0_S : memW s (globN s "ev" + 136) ∈ S := (hInvAt.2.2.2.2.1 _ hhead_mem).2.2.2.2.2.2.2.1
  have hArg : HtabArgWF s := by
    refine ⟨hAs, ?_, ?_⟩
    · rw [ht_eq]; exact (hInvAt.1.1.2.1 _ ht0_S).1
    · rw [ht_eq]; intro i hi; exact ((hInvAt.1.1.2.1 _ ht0_S).2 i hi).1
  dsimp only
  refine ⟨fun v hv => ?_, ?_⟩
  · have hexit := hfn_spec s hcode hArg hlookup hnt v hv
    unfold HtabExit at hexit; dsimp only at hexit
    rw [ht_eq] at hexit
    obtain ⟨hAp, hwf, hhdr0, _, hhp, hfp, hfr, hg⟩ := hexit
    set post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_htab_set)).2
    have hbe : post.be = s.be :=
      evaluate_be_eq s (sourceFnBody Guest.Software.guestFn_htab_set)
    obtain ⟨hInv_p, hch_p, hR_p⟩ := evmInvAt_of_head_del_htab_step
      hAs hInvAt hAp hbe hwf hhdr0 hhp hfp hfr hg
    have hInv_post : EvmInv post := ⟨hAp, S, hInv_p⟩
    have hInv_orig : EvmInv s := ⟨hAs, S, hInvAt⟩
    obtain ⟨⟨hT, _, _, _⟩, _, _, _, hFW_all, _, _, _, hFO_disj, _⟩ := hInvAt
    have hf_al1 : (globN s "heap_ptr") % 8 = 0 := hAs.2.2.2.2.2.2.1
    have hf_al2 : (globN post "heap_ptr" - globN s "heap_ptr") % 8 = 0 := by
      have := hAs.2.2.2.2.2.2.1; have := hAp.2.2.2.2.2.2.1; omega
    have ht0_al : ∀ j ∈ htabFootprint s (memW s (globN s "ev" + 136)),
        j.1 % 8 = 0 ∧ j.2 % 8 = 0 := fun j hj => by
      have hw := ((hT.2.1 _ ht0_S).1.1 j hj).2; exact ⟨hw.1, hw.2.1⟩
    have hu : ∀ ec ∈ evmChain s, R16Shards.IvlUnhit s post (ec.1, 280) ∧
        R16Shards.IvlUnhit s post (ec.2, 104) := by
      intro ec hec
      have hFW := hFW_all ec hec
      have h1 := hFW.1 (ec.1, 280) (by simp)
      have h2 := hFW.1 (ec.2, 104) (by simp)
      exact ⟨R16Shards.ivlUnhit_of_frameOutside ⟨h1.2.1, h1.2.2.1⟩ hfr ht0_al ⟨hf_al1, hf_al2⟩
               (fun j hj => (hFO_disj ec hec (ec.1, 280) (by simp [frameObjects])).1 _ ht0_S j hj)
               (R16Shards.disj_fresh_of_allocated hAs.2 hAp.2 hhp (Or.inr h1.1)),
             R16Shards.ivlUnhit_of_frameOutside ⟨h2.2.1, h2.2.2.1⟩ hfr ht0_al ⟨hf_al1, hf_al2⟩
               (fun j hj => (hFO_disj ec hec (ec.2, 104) (by simp [frameObjects])).1 _ ht0_S j hj)
               (R16Shards.disj_fresh_of_allocated hAs.2 hAp.2 hhp (Or.inr h2.1))⟩
    have hev_eq : globN post "ev" = globN s "ev" :=
      OpHandlers.globN_eq_of_lookup_eq (hg (ofString "ev") (by decide)).symm
    have hfmp_eq : globN post "frame_mem_ptr" = globN s "frame_mem_ptr" :=
      OpHandlers.globN_eq_of_lookup_eq (hg (ofString "frame_mem_ptr") (by decide)).symm
    exact ⟨⟨hInv_post, headMemChainWF_of_unhit_g10 hInv_orig hHMWF hch_p hu hev_eq hfmp_eq⟩,
      hch_p, le_of_eq hR_p, hg, hR_p⟩
  · intro ⟨ev, hev⟩
    have hnc := evaluate_noCatchableRaise R16Shards.StateRestoreEpilogue.htabMutCallees
      R16Shards.StateRestoreEpilogue.htabMutCallees_good
      (sourceFnBody Guest.Software.guestFn_htab_set) (by decide) s hcode
    exact False.elim (hnc (ofString "EvmErr") ev (by decide) hev)

theorem HandlerRunA.seq_assoc
    {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {P : PanSemStateFiniteExact 64 F → Prop} {charged : Bool}
    {p1 p2 p3 : ProgHOL 64}
    (hrun : HandlerRunA s0 P charged (.seq p1 (.seq p2 p3))) :
    HandlerRunA s0 P charged (.seq (.seq p1 p2) p3) := by
  intro t hc hi hw hlen hR hp hnt
  have hr := hrun t hc hi hw hlen hR hp
  rw [evaluateHOLFiniteState_seq_line780] at hnt hr ⊢
  dsimp only at hnt hr ⊢
  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
  dsimp only at hnt ⊢
  rcases h1 : evaluateHOLFiniteState t p1 with ⟨r1, s1⟩
  simp only [h1] at hnt hr ⊢
  cases r1 with
  | none =>
    dsimp only at hnt hr ⊢
    rw [evaluateHOLFiniteState_seq_line780] at hr
    exact hr hnt
  | some _ =>
    dsimp only at hnt hr ⊢
    exact hr hnt

theorem HandlerRunA.seq_ite_unit
    {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {P : PanSemStateFiniteExact 64 F → Prop} {charged : Bool}
    {cond : ExpHOL 64} {yes no cont : ProgHOL 64}
    (hyes : ∀ (t : PanSemStateFiniteExact 64 F) (w : BitVec 64),
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) cond = some (.val (.word w)) →
      w ≠ 0 →
      HandlerRunA s0 P charged (.seq yes cont))
    (hno : ∀ (t : PanSemStateFiniteExact 64 F),
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) cond = some (.val (.word 0)) →
      HandlerRunA s0 (fun s => P s) charged (.seq no cont)) :
    HandlerRunA s0 P charged (.seq (.ite cond yes no) cont) := by
  intro t hc hi hw hlen hR hp hnt
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt ⊢
  revert hnt
  split
  · rename_i w hcond
    by_cases hw0 : w = 0
    · subst hw0; simp only [↓reduceIte]
      rw [← evaluateHOLFiniteState_seq_line780]
      intro hnt; exact hno t hcond t hc hi hw hlen hR hp hnt
    · simp only [hw0, ↓reduceIte]
      rw [← evaluateHOLFiniteState_seq_line780]
      intro hnt; exact hyes t w hcond hw0 t hc hi hw hlen hR hp hnt
  · intro _; dsimp only; exact opDispatchPostA_error s0 t

private theorem rboundA_step_g10 {charged : Bool} {r1 r2 r0 : Nat}
    (h1 : r2 ≤ r1) (h2 : if charged then r1 < r0 else r1 ≤ r0) :
    if charged then r2 < r0 else r2 ≤ r0 := by
  cases charged <;> simp only [↓reduceIte, Bool.false_eq_true] at h2 ⊢ <;> omega

private theorem rboundA_to_le_g10 {charged : Bool} {r1 r0 : Nat}
    (h : if charged then r1 < r0 else r1 ≤ r0) : r1 ≤ r0 := by
  cases charged <;> simp only [↓reduceIte, Bool.false_eq_true] at h <;> omega

theorem HandlerRunA.seq_call_assign_local
    {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {P Q : PanSemStateFiniteExact 64 F → Prop}
    {Pc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {Qc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    {charged : Bool}
    {nm : MlS} {fname : MlS} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (hf : EvmPreservingSpecA Pc Qc fname)
    (hentry : ∀ (t : PanSemStateFiniteExact 64 F) values body' callee ret',
      t.code = originalRuntimeCode → EvmInv t → Group10.HeadMemChainWF t → P t →
      evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) args = some values →
      lookupCodeHOLFinite t.code.lookup fname values = some (body', callee, ret') →
      Pc (callEntryStateHOLFinite t callee))
    (hstep : ∀ (t : PanSemStateFiniteExact 64 F) values body callee retShape v (cpost : PanSemStateFiniteExact 64 F),
      EvmInv t → Group10.HeadMemChainWF t → P t →
      evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) args = some values →
      lookupCodeHOLFinite originalRuntimeCode.lookup fname values = some (body, callee, retShape) →
      shapeEqHOL (shapeOfHOLExact v) retShape = true →
      EvmInv cpost → Group10.HeadMemChainWF cpost →
      evmChain cpost = evmChain (callEntryStateHOLFinite t callee) →
      Qc (callEntryStateHOLFinite t callee) v cpost →
      Q (setVarHOLFinite nm v { cpost with locals := t.locals }))
    (hcont : HandlerRunA s0 Q charged cont) :
    HandlerRunA s0 P charged (.seq (.call (some (some (.local, nm), none)) fname args) cont) := by
  intro t hc hi hw hlen hR hp hn
  obtain ⟨params, body, retShape, hlook, hspec⟩ := hf
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_call] at hn ⊢
  rcases hargs : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) args with _ | values
  · dsimp only; exact opDispatchPostA_error s0 t
  · simp only [hargs] at hn ⊢
    rcases hl : lookupCodeHOLFinite t.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · dsimp only; exact opDispatchPostA_error s0 t
    · simp only [hl] at hn ⊢
      by_cases hz : t.clock = 0
      · simp [hz] at hn
      · simp only [hz, ↓reduceIte] at hn ⊢
        have hbody_eq : body' = body :=
          lookupCodeHOLFinite_installed_body t.code.lookup fname params body body'
            retShape ret' values callee (by rw [hc]; exact hlook) hl
        subst body'
        have hret_eq : ret' = retShape := by
          have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
            t.code.lookup fname values body callee ret' hl
          rw [hc] at hx; simp only [Flapjack.lookupCodeHOLExact, hlook] at hx
          split at hx
          · exact (congrArg (fun x => x.2.2) (Option.some.inj hx)).symm
          · cases hx
        subst ret'
        have hi_ce : EvmInv (callEntryStateHOLFinite t callee) := localsFree_evmInv t callee (t.clock - 1) hi
        have hw_ce : Group10.HeadMemChainWF (callEntryStateHOLFinite t callee) :=
          Group10.headMemChainWF_locals t callee (t.clock - 1) hw
        have hPc : Pc (callEntryStateHOLFinite t callee) := hentry t values body callee retShape hc hi hw hp hargs hl
        have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup fname values =
            some (body, callee, retShape) := by rwa [← hc]
        have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite t callee) body).1
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite t callee) body with ⟨res, cpost⟩
        simp only [hrun] at hn hmeta ⊢
        change cpost.code = t.code at hmeta
        have hc_ce := evm_congr (s := t) (t := callEntryStateHOLFinite t callee) rfl rfl
        have hQ (hsafe : res ≠ some .timeOut) :
            (∀ v, res = some (.returned v) →
              (EvmInv cpost ∧ Group10.HeadMemChainWF cpost) ∧
              evmChain cpost = evmChain (callEntryStateHOLFinite t callee) ∧
              evmR cpost ≤ evmR (callEntryStateHOLFinite t callee) ∧
              Qc (callEntryStateHOLFinite t callee) v cpost) ∧
            (IsEvmErr res →
              (EvmInv cpost ∧ Group10.HeadMemChainWF cpost) ∧
              evmChain cpost = evmChain (callEntryStateHOLFinite t callee) ∧
              evmR cpost ≤ evmR (callEntryStateHOLFinite t callee)) := by
          have hs := hspec (callEntryStateHOLFinite t callee) hc hi_ce hw_ce hPc ⟨values, hl_orig⟩
            (by rw [hrun]; exact hsafe)
          dsimp only at hs; rw [hrun] at hs; exact hs
        cases res with
        | none => dsimp only; exact opDispatchPostA_error s0 cpost
        | some r0 =>
          cases r0 with
          | timeOut => simp at hn
          | returned v =>
            dsimp only at hn ⊢
            by_cases hsh_ok : shapeEqHOL (shapeOfHOLExact v) retShape = true
            · simp only [hsh_ok, ↓reduceIte] at hn ⊢
              by_cases hvld : isValidValueHOLExact t.toExact .local nm v = true
              · simp only [hvld, ↓reduceIte] at hn ⊢
                dsimp only [setKvarHOLFinite] at hn ⊢
                obtain ⟨⟨hi_cp, hw_cp⟩, hch_cp, hR_cp, hQc_cp⟩ := (hQ (by simp)).1 v rfl
                let resumed : PanSemStateFiniteExact 64 F := setVarHOLFinite nm v { cpost with locals := t.locals }
                have hcode_res : resumed.code = originalRuntimeCode := hmeta.trans hc
                have hi_res : EvmInv resumed := localsFree_evmInv cpost resumed.locals cpost.clock hi_cp
                have hw_res : Group10.HeadMemChainWF resumed :=
                  Group10.headMemChainWF_locals cpost resumed.locals cpost.clock hw_cp
                have hc_res := evm_congr (s := cpost) (t := resumed) rfl rfl
                have hlen_res : (evmChain resumed).length = (evmChain s0).length := by
                  rw [hc_res.2.2.1, hch_cp, hc_ce.2.2.1]; exact hlen
                have hR_res : if charged then evmR resumed < evmR s0 else evmR resumed ≤ evmR s0 :=
                  rboundA_step_g10 (by rw [hc_res.2.1]; rw [hc_ce.2.1] at hR_cp; exact hR_cp) hR
                have hQ_res : Q resumed :=
                  hstep t values body callee retShape v cpost hi hw hp hargs hl_orig hsh_ok hi_cp hw_cp hch_cp hQc_cp
                exact hcont resumed hcode_res hi_res hw_res hlen_res hR_res hQ_res (by simpa [resumed] using hn)
              · simp only [hvld, Bool.false_eq_true, ↓reduceIte]
                exact opDispatchPostA_error s0 cpost
            · simp only [hsh_ok, Bool.false_eq_true, ↓reduceIte]
              exact opDispatchPostA_error s0 cpost
          | exception eid ev =>
            dsimp only at hn ⊢
            by_cases heid : eid = ofString "EvmErr"
            · subst heid
              obtain ⟨⟨hi_cp, hw_cp⟩, hch_cp, hR_cp⟩ := (hQ (by simp)).2 ⟨ev, rfl⟩
              have hi_el : EvmInv cpost.emptyLocalsHOLFinite :=
                localsFree_evmInv cpost _ cpost.clock hi_cp
              have hw_el : Group10.HeadMemChainWF cpost.emptyLocalsHOLFinite :=
                Group10.headMemChainWF_locals cpost _ cpost.clock hw_cp
              have hc_el := evm_congr (s := cpost) (t := cpost.emptyLocalsHOLFinite) rfl rfl
              refine ⟨?_, fun _ => ⟨⟨hi_el, hw_el⟩, ?_, ?_⟩⟩
              · rintro ⟨_, h⟩; cases h
              · rw [hc_el.2.2.1, hch_cp, hc_ce.2.2.1]; exact hlen
              · have := rboundA_to_le_g10 hR; rw [hc_el.2.1]; rw [hc_ce.2.1] at hR_cp; omega
            · refine opDispatchPostA_other (fun _ h => by cases h) ?_
              rintro ⟨_, h⟩; injection h with h'; injection h' with h1 _; exact heid h1
          | «break» => dsimp only; exact opDispatchPostA_error s0 cpost
          | «continue» => dsimp only; exact opDispatchPostA_error s0 cpost
          | finalFfi _ =>
            dsimp only
            refine opDispatchPostA_other (fun _ h => by cases h) ?_
            rintro ⟨_, h⟩; cases h
          | error => dsimp only; exact opDispatchPostA_error s0 cpost.emptyLocalsHOLFinite

theorem HandlerRunA.seq_call_assign_local_simple
    {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {Qc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    {charged : Bool}
    {nm : MlS} {fname : MlS} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (hf : EvmPreservingSpecA (fun _ => True) Qc fname)
    (hcont : HandlerRunA s0 (fun _ => True) charged cont) :
    HandlerRunA s0 (fun _ => True) charged (.seq (.call (some (some (.local, nm), none)) fname args) cont) :=
  HandlerRunA.seq_call_assign_local hf
    (fun _ _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial)
    hcont

structure WorldAccountSpecsA : Prop where
  epsA_get_account :
    EvmPreservingSpecA (fun _ => True)
      (fun s _ post => GlobalsKept ["heap_ptr", "scratch_ptr"] s post ∧ evmR post = evmR s)
      (ofString "get_account")
  epsA_ext_code_of :
    EvmPreservingSpecA (fun _ => True)
      (fun s _ post => GlobalsKept ["heap_ptr", "scratch_ptr"] s post ∧ evmR post = evmR s)
      (ofString "ext_code_of")
  epsA_get_storage :
    EvmPreservingSpecA (fun _ => True)
      (fun s _ post => GlobalsKept ["heap_ptr", "scratch_ptr"] s post ∧ evmR post = evmR s)
      (ofString "get_storage")
  epsA_get_storage_original :
    EvmPreservingSpecA (fun _ => True)
      (fun s _ post => GlobalsKept ["heap_ptr", "scratch_ptr"] s post ∧ evmR post = evmR s)
      (ofString "get_storage_original")
  epsA_set_storage :
    EvmPreservingSpecA (fun _ => True)
      (fun s _ post => GlobalsKept ["heap_ptr", "scratch_ptr", "journal", "journal_n", "journal_cap"] s post ∧ evmR post = evmR s)
      (ofString "set_storage")
  epsA_is_account_alive :
    EvmPreservingSpecA (fun _ => True)
      (fun s _ post => GlobalsKept ["heap_ptr", "scratch_ptr"] s post ∧ evmR post = evmR s)
      (ofString "is_account_alive")
  epsA_move_ether :
    EvmPreservingSpecA (fun _ => True)
      (fun s _ post => GlobalsKept ["heap_ptr", "scratch_ptr", "journal", "journal_n", "journal_cap"] s post ∧ evmR post = evmR s)
      (ofString "move_ether")
  epsA_emit_transfer_log :
    EvmPreservingSpecA (fun _ => True)
      (fun s _ post => GlobalsKept ["heap_ptr", "scratch_ptr"] s post ∧ evmR post = evmR s)
      (ofString "emit_transfer_log")

private theorem word_local_pos_of_lookup_g10 {F : Type} (t : PanSemStateFiniteExact 64 F)
    (nm : MlS) {v : ValueHOL 64}
    (heval : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
      (.var .local nm) = some v)
    {cw : BitVec 64} (hlk : t.locals.lookup nm = some (.val (.word cw))) :
    v = .val (.word cw) := by
  simpa [evalHOLExact, hlk] using heval.symm

theorem HandlerRunA.seq_ite_branch
    {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {P R : PanSemStateFiniteExact 64 F → Prop} {charged : Bool}
    {cond : ExpHOL 64} {yes no cont : ProgHOL 64}
    (hyes : ∀ {cont' : ProgHOL 64}, HandlerRunA s0 R charged cont' →
      ∀ (t : PanSemStateFiniteExact 64 F) (w : BitVec 64),
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) cond = some (.val (.word w)) →
      w ≠ 0 →
      HandlerRunA s0 P charged (.seq yes cont'))
    (hno : ∀ {cont' : ProgHOL 64}, HandlerRunA s0 R charged cont' →
      ∀ (t : PanSemStateFiniteExact 64 F),
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) cond = some (.val (.word 0)) →
      HandlerRunA s0 P charged (.seq no cont'))
    (hcont : HandlerRunA s0 R charged cont) :
    HandlerRunA s0 P charged (.seq (.ite cond yes no) cont) :=
  HandlerRunA.seq_ite_unit (hyes hcont) (hno hcont)

theorem op_selfdestruct_specA (hW : WorldAccountSpecsA) :
    OpHandlerSpecA (ofString "op_selfdestruct") := by
  refine opHandlerSpecA_of_run 570 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_selfdestruct rfl ?_
  intro F s0 hInv0 _ hnd0
  have hRun0 : EvmRun s0 := ⟨hInv0, hnd0⟩
  dsimp only [Guest.Software.guestFn_op_selfdestruct, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural,
    List.map, Option.map]
  refine HandlerRunA.seq_call_simple epsA_require_not_static ?_
  refine HandlerRunA.decCall_simple epsA_stack_pop ?_
  refine HandlerRunA.decCall_simple epsA_to_address_masked ?_
  refine HandlerRunA.decCall_simple epsA_is_warm_address ?_
  refine HandlerRunA.dec (Q := fun t =>
      t.locals.lookup (ofString "gas_cost") = some (.val (.word 5000#64)))
    (fun _ v hv _ _ => by
      change some (ValueHOL.val (.word 5000#64)) = some v at hv
      injection hv with hv'; subst hv'
      simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]) ?_
  refine HandlerRunA.seq_ite_branch
    (R := fun t => ∃ gw : BitVec 64,
      t.locals.lookup (ofString "gas_cost") = some (.val (.word gw)) ∧ 0 < gw.toNat)
    (fun hcont _ _ _ _ =>
      HandlerRunA.seq_assign_local
        (fun t v hv _ hlk => by
          simp [evalHOLExact, evalListHOLExact, hlk, wordOpHOL, wordOp, valueIsWord, valueWord] at hv
          subst hv
          refine ⟨8000#64, ?_, by decide⟩
          simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
        hcont)
    (fun hcont _ _ =>
      HandlerRunA.seq_skip
        (HandlerRunA.weaken (fun _ _ hlk => ⟨5000#64, hlk, by decide⟩) hcont))
    ?_
  refine HandlerRunA.seq_charge_gas (Q := fun _ => True)
    (fun t w hw _ _ ⟨gw, hlk, hpos⟩ => by
      have heq := word_local_pos_of_lookup_g10 t (ofString "gas_cost") hw hlk
      injection heq with h1; injection h1 with h2; subst h2
      exact hpos)
    (fun _ _ _ _ _ _ _ _ _ => trivial) ?_
  refine HandlerRunA.seq_ite_branch (R := fun _ => True)
    (fun hcont _ _ _ _ => HandlerRunA.seq_call_simple epsA_warm_address hcont)
    (fun hcont _ _ => HandlerRunA.seq_skip hcont)
    ?_
  refine HandlerRunA.dec_simple ?_
  refine HandlerRunA.decCall_simple hW.epsA_is_account_alive ?_
  refine HandlerRunA.decCall_simple hW.epsA_get_account ?_
  refine HandlerRunA.decCall_simple epsA_u256_is_zero ?_
  refine HandlerRunA.dec_simple ?_
  refine HandlerRunA.dec_simple ?_
  refine HandlerRunA.seq_ite_branch (R := fun _ => True)
    (fun hcont _ _ _ _ =>
      HandlerRunA.seq_assoc
        (HandlerRunA.seq_assign_local (Q := fun _ => True) (fun _ _ _ _ _ => trivial)
          (HandlerRunA.seq_assign_local (Q := fun _ => True) (fun _ _ _ _ _ => trivial) hcont)))
    (fun hcont _ _ => HandlerRunA.seq_skip hcont)
    ?_
  refine HandlerRunA.seq_call_simple epsA_charge_gas_any ?_
  refine HandlerRunA.seq_call_simple epsA_charge_state_gas ?_
  refine HandlerRunA.seq_call_assign_local_simple hW.epsA_get_account ?_
  refine HandlerRunA.dec_simple ?_
  refine HandlerRunA.seq_call_simple hW.epsA_move_ether ?_
  refine HandlerRunA.decCall_simple epsA_memeq_ro ?_
  refine HandlerRunA.seq_ite_branch (R := fun _ => True)
    (fun hcont _ _ _ _ => HandlerRunA.seq_call_simple hW.epsA_emit_transfer_log hcont)
    (fun hcont _ _ => HandlerRunA.seq_skip hcont)
    ?_
  refine HandlerRunA.decCall_simple epsA_htab_has_ro ?_
  refine HandlerRunA.seq_ite_branch (R := fun _ => True)
    (fun hcont _ _ _ _ =>
      HandlerRunA.seq_call (Q := fun _ => True) epsA_htab_set_head_del
        (fun t _ _ _ _ hc hInv _ _ hargs hl => htab_set_head_del_callee_t t hInv hc hargs hl)
        (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial)
        hcont)
    (fun hcont _ _ => HandlerRunA.seq_skip hcont)
    ?_
  exact HandlerRunA.seq_store_ev_nonstruct (Q := fun t => memW t (globN t "ev" + 104) = 0)
    104 (by simp [nonStructFrameOffs])
    (fun _ v _ hv => by
      change some (ValueHOL.val (.word 0#64)) = some v at hv
      injection hv with hv'; exact ⟨0, hv'.symm⟩)
    (fun t w hw _ _ => by
      change some (ValueHOL.val (.word 0#64)) = some (.val (.word w)) at hw
      injection hw with hw1; injection hw1 with hw2; injection hw2 with hw3; subst hw3
      simpa [globN] using R14Shards.OpHandlersA.memW_updW_same t (globN t "ev" + 104) 0)
    (HandlerRunA.ret_done hRun0 (fun _ _ hP => Or.inr (Or.inl hP)) _)

/-- Preserve the aligned frame-chain invariant when a child is pushed and the
old frames' structural cells are unchanged. The saved mark links the child to
the old head's memory end. -/
theorem Group10.headMemChainWF_push {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (hs : Group10.HeadMemChainWF s)
    (hchain : evmChain post =
      (globN post "ev", globN post "cur_cont") :: evmChain s)
    (hmem : ∀ ec ∈ evmChain s,
      memW post (ec.1 + 24) = memW s (ec.1 + 24) ∧
      memW post (ec.1 + 32) = memW s (ec.1 + 32) ∧
      memW post (ec.1 + 40) = memW s (ec.1 + 40) ∧
      memW post (ec.2 + 56) = memW s (ec.2 + 56))
    (hlen : memW post (globN post "ev" + 32) % 32 = 0)
    (hcap : memW post (globN post "ev" + 40) % 8 = 0)
    (hend : memW post (globN post "ev" + 24) +
      memW post (globN post "ev" + 40) = globN post "frame_mem_ptr")
    (hmark : memW post (globN post "cur_cont" + 56) = globN s "frame_mem_ptr") :
    Group10.HeadMemChainWF post := by
  refine ⟨?_, hend, ?_⟩
  · intro ec hec
    rw [hchain, List.mem_cons] at hec
    rcases hec with rfl | hec
    · exact ⟨hlen, hcap⟩
    · rw [(hmem ec hec).2.1, (hmem ec hec).2.2.1]
      exact hs.1 ec hec
  · rw [hchain]
    have ht := Group10.chainLinks_transport (memW s) (memW post) (evmChain s)
      (fun ec hec => ⟨(hmem ec hec).1, (hmem ec hec).2.2.1,
        (hmem ec hec).2.2.2⟩) hs.2.2
    have hh : (globN s "ev", globN s "cur_cont") ∈ evmChain s :=
      List.mem_cons_self
    change _ ∧ Group10.ChainLinks (memW post) (evmChain s)
    refine ⟨?_, ht⟩
    rw [(hmem _ hh).1, (hmem _ hh).2.2.1, hmark]
    exact hs.2.1

/-- Account emptiness is read-only, including its memory and integer helpers. -/
theorem epsA_acct_is_empty :
    EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "acct_is_empty") :=
  epsA_of_readOnly 384 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_acct_is_empty rfl opRoCallees opRoCallees_good rfl

/-- Strict resource decrease suffices even when a successful call adds a frame. -/
theorem opDispatchPostA_return_of_resource_drop {F : Type}
    {s post : PanSemStateFiniteExact 64 F} (v : ValueHOL 64)
    (hi : EvmInv post) (hw : Group10.HeadMemChainWF post)
    (hr : evmR post < evmR s) :
    OpDispatchPostA s (some (.returned v)) post := by
  refine ⟨fun _ => ⟨⟨hi, hw⟩, evmPot_lt_of_evmR_lt hi hr⟩, ?_⟩
  rintro ⟨ev, he⟩
  cases he

/-! Account lookup table mutations and their caller argument bindings. -/

theorem ts8_worldTableRef_g10 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (S : List Nat) (hts : globN s "ts" ≠ 0) :
    memW s (globN s "ts" + 8) ∈ worldTableRefs s S := by
  unfold worldTableRefs
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_right
  unfold recordSlots
  rw [if_neg hts]
  exact List.mem_map.2 ⟨8, by decide, rfl⟩

theorem ts8_not_delExclusive_g10 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (S : List Nat) (hts : globN s "ts" ≠ 0) (i : Nat) :
    ¬ DelExclusive s S (evmChain s) i (memW s (globN s "ts" + 8)) := by
  intro h
  exact h.1 (ts8_worldTableRef_g10 s S hts)

theorem worldRole_unique_g10 {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S : List Nat} (hi : EvmInvAt s S) {t : Nat} {r r' : String}
    (h : (t, r) ∈ worldRoleSlots s) (h' : (t, r') ∈ worldRoleSlots s) :
    r = r' := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hRoles, _⟩ := hi
  have hpw : (worldRoleSlots s).Pairwise
      (fun a b => a.1 = b.1 → a.2 = b.2 ∧ a.2 ∈ sharedRoles) :=
    (List.pairwise_append.1 hRoles.2.1).1
  obtain ⟨i, hi, hei⟩ := List.mem_iff_getElem.1 h
  obtain ⟨j, hj, hej⟩ := List.mem_iff_getElem.1 h'
  by_cases heq : i = j
  · subst j
    exact (Prod.mk.inj (hei.symm.trans hej)).2
  · rcases Nat.lt_or_gt_of_ne heq with hlt | hgt
    · have hp := List.pairwise_iff_getElem.1 hpw i j hi hj hlt
      rw [hei, hej] at hp
      exact (hp rfl).1
    · have hp := List.pairwise_iff_getElem.1 hpw j i hj hi hgt
      rw [hei, hej] at hp
      exact (hp rfl).1.symm

theorem ts8_worldRole_g10 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hts : globN s "ts" ≠ 0) (ht : memW s (globN s "ts" + 8) ≠ 0) :
    (memW s (globN s "ts" + 8), "ts+8") ∈ worldRoleSlots s := by
  unfold worldRoleSlots
  refine List.mem_filter.2 ⟨?_, by simp [ht]⟩
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_append_left; apply List.mem_append_right
  unfold recRoles
  rw [if_neg hts]
  exact List.mem_map.2 ⟨(8, "ts+8"), by decide, rfl⟩

theorem ts8_separation_g10 {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S : List Nat} (hi : EvmInvAt s S)
    (hts : globN s "ts" ≠ 0) (ht : memW s (globN s "ts" + 8) ≠ 0) :
    (globN s "ws" ≠ 0 → memW s (globN s "ws" + 32) ≠ memW s (globN s "ts" + 8)) ∧
    (globN s "bs" ≠ 0 → memW s (globN s "bs" + 32) ≠ memW s (globN s "ts" + 8)) ∧
    globN s "bal_accounts" ≠ memW s (globN s "ts" + 8) ∧
    (∀ ad ∈ balRecords s, memW s ad ≠ memW s (globN s "ts" + 8)) ∧
    memW s (globN s "ts" + 32) ≠ memW s (globN s "ts" + 8) := by
  have hnot : ∀ r, r ≠ "ts+8" → (memW s (globN s "ts" + 8), r) ∉ worldRoleSlots s := by
    intro r hr hm
    exact hr (worldRole_unique_g10 hi hm (ts8_worldRole_g10 s hts ht))
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hws heq
    apply hnot "ws+32" (by decide)
    unfold worldRoleSlots
    refine List.mem_filter.2 ⟨?_, by simp [ht]⟩
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    unfold recRoles; simp [hws, heq]
  · intro hbs heq
    apply hnot "bs+32" (by decide)
    unfold worldRoleSlots
    refine List.mem_filter.2 ⟨?_, by simp [ht]⟩
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_right
    unfold recRoles; simp [hbs, heq]
  · intro heq
    apply hnot "bal_accounts" (by decide)
    unfold worldRoleSlots
    refine List.mem_filter.2 ⟨?_, by simp [ht]⟩
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    apply List.mem_append_right
    simp [heq]
  · intro ad had heq
    apply hnot "bal.stor" (by decide)
    unfold worldRoleSlots
    refine List.mem_filter.2 ⟨?_, by simp [ht]⟩
    apply List.mem_append_right
    exact List.mem_flatMap.2 ⟨ad, had, by simp [heq]⟩
  · intro heq
    apply hnot "ts+32" (by decide)
    unfold worldRoleSlots
    refine List.mem_filter.2 ⟨?_, by simp [ht]⟩
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    apply List.mem_append_left; apply List.mem_append_right
    unfold recRoles
    rw [if_neg hts]
    exact List.mem_map.2 ⟨(32, "ts+32"), by decide, by simp [heq]⟩

theorem epsA_htab_set_ts8_g10 :
    EvmPreservingSpecA
      (fun s => globN s "ts" ≠ 0 ∧ locN s "t" = memW s (globN s "ts" + 8) ∧ locN s "t" ≠ 0)
      (fun s _ post => GlobalsKept ["heap_ptr"] s post ∧ evmR post = evmR s)
      (ofString "htab_set") := by
  obtain ⟨params, body, rs, hlk, hfn⟩ := SoloHtabSet.htab_set_spec_proof
  refine ⟨params, body, rs, hlk, ?_⟩
  intro F s hc hi hw hp hl hn
  obtain ⟨hts, heq, hnz⟩ := hp
  have ht : memW s (globN s "ts" + 8) ≠ 0 := by rwa [heq] at hnz
  have hb := Option.some.inj (SoloHtabSet.lookup_htab_set.symm.trans hlk)
  rcases Prod.mk.inj hb with ⟨_, hbr⟩
  rcases Prod.mk.inj hbr with ⟨hbody, _⟩
  subst hbody
  obtain ⟨ha, S, hi⟩ := hi
  have hS : memW s (globN s "ts" + 8) ∈ S := by
    rcases hi.1.1.2.2.2.2.2.1 8 (by decide) hts with hz | hm
    · exact False.elim (ht hz)
    · exact hm
  have harg : HtabArgWF s := by
    refine ⟨ha, ?_, ?_⟩
    · rw [heq]; exact (hi.1.1.2.1 _ hS).1
    · rw [heq]; intro i hi'; exact ((hi.1.1.2.1 _ hS).2 i hi').1
  dsimp only
  refine ⟨fun v hv => ?_, ?_⟩
  · have hx := hfn s hc harg hl hn v hv
    unfold HtabExit at hx
    dsimp only at hx
    rw [heq] at hx
    obtain ⟨hap, htf, hhdr, _, hhp, hfp, hfr, hg⟩ := hx
    set post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_htab_set)).2
    obtain ⟨hws, hbs, hba, had, hts32⟩ := ts8_separation_g10 hi hts ht
    have hgw : GlobalsKept ["heap_ptr", "journal_n"] s post := by
      intro name hn
      apply hg name
      intro hm
      apply hn
      simp only [List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
      obtain ⟨x, rfl, hx⟩ := hm
      exact ⟨"heap_ptr", Or.inl rfl, hx⟩
    have hj : globN post "journal_n" ≤ globN s "journal_n" := by
      exact le_of_eq (OpHandlers.globN_eq_of_lookup_eq (hg (ofString "journal_n") (by decide))).symm
    obtain ⟨hip, hch, hr, hu⟩ := R16Shards.evmInvAt_of_htab_step ha hi hap
      (R16Shards.evaluate_be_eq s _) htf hhdr hhp hfp hfr hgw hj hS
      (fun i _ => ts8_not_delExclusive_g10 s S hts i) hws hbs hba had (Or.inl (fun _ => hts32))
    have hev := (OpHandlers.globN_eq_of_lookup_eq (hg (ofString "ev") (by decide))).symm
    have hfm := (OpHandlers.globN_eq_of_lookup_eq (hg (ofString "frame_mem_ptr") (by decide))).symm
    exact ⟨⟨⟨hap, S, hip⟩, headMemChainWF_of_unhit_g10 ⟨ha, S, hi⟩ hw hch hu hev hfm⟩,
      hch, le_of_eq hr, hg, hr⟩
  · intro ⟨ev, hev⟩
    have hnc := R16Shards.StateRestoreEpilogue.evaluate_noCatchableRaise
      R16Shards.StateRestoreEpilogue.htabMutCallees R16Shards.StateRestoreEpilogue.htabMutCallees_good
      (sourceFnBody Guest.Software.guestFn_htab_set) (by decide) s hc
    exact False.elim (hnc (ofString "EvmErr") ev (by decide) hev)

theorem bs72_worldTableRef_g10 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (S : List Nat) (hbs : globN s "bs" ≠ 0) :
    memW s (globN s "bs" + 72) ∈ worldTableRefs s S := by
  unfold worldTableRefs
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_append_right
  unfold recordSlots
  rw [if_neg hbs]
  exact List.mem_map.2 ⟨72, by decide, rfl⟩

theorem bs72_worldRole_g10 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hbs : globN s "bs" ≠ 0) (ht : memW s (globN s "bs" + 72) ≠ 0) :
    (memW s (globN s "bs" + 72), "bs+72") ∈ worldRoleSlots s := by
  unfold worldRoleSlots
  refine List.mem_filter.2 ⟨?_, by simp [ht]⟩
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_right
  unfold recRoles
  rw [if_neg hbs]
  exact List.mem_map.2 ⟨(72, "bs+72"), by decide, rfl⟩

theorem bs72_not_delExclusive_g10 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (S : List Nat) (hbs : globN s "bs" ≠ 0) (i : Nat) :
    ¬ DelExclusive s S (evmChain s) i (memW s (globN s "bs" + 72)) := by
  intro h
  exact h.1 (bs72_worldTableRef_g10 s S hbs)

theorem bs72_separation_g10 {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S : List Nat} (hi : EvmInvAt s S)
    (hbs : globN s "bs" ≠ 0) (ht : memW s (globN s "bs" + 72) ≠ 0) :
    (globN s "ws" ≠ 0 → memW s (globN s "ws" + 32) ≠ memW s (globN s "bs" + 72)) ∧
    (globN s "bs" ≠ 0 → memW s (globN s "bs" + 32) ≠ memW s (globN s "bs" + 72)) ∧
    globN s "bal_accounts" ≠ memW s (globN s "bs" + 72) ∧
    (∀ ad ∈ balRecords s, memW s ad ≠ memW s (globN s "bs" + 72)) ∧
    (globN s "ts" ≠ 0 → memW s (globN s "ts" + 32) ≠ memW s (globN s "bs" + 72)) := by
  have hnot : ∀ r, r ≠ "bs+72" → (memW s (globN s "bs" + 72), r) ∉ worldRoleSlots s := by
    intro r hr hm
    exact hr (worldRole_unique_g10 hi hm (bs72_worldRole_g10 s hbs ht))
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hws heq
    apply hnot "ws+32" (by decide)
    unfold worldRoleSlots
    refine List.mem_filter.2 ⟨?_, by simp [ht]⟩
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    unfold recRoles; simp [hws, heq]
  · intro _ heq
    apply hnot "bs+32" (by decide)
    unfold worldRoleSlots
    refine List.mem_filter.2 ⟨?_, by simp [ht]⟩
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_right
    unfold recRoles; simp [hbs, heq]
  · intro heq
    apply hnot "bal_accounts" (by decide)
    unfold worldRoleSlots
    refine List.mem_filter.2 ⟨?_, by simp [ht]⟩
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    apply List.mem_append_right
    simp [heq]
  · intro ad had heq
    apply hnot "bal.stor" (by decide)
    unfold worldRoleSlots
    refine List.mem_filter.2 ⟨?_, by simp [ht]⟩
    apply List.mem_append_right
    exact List.mem_flatMap.2 ⟨ad, had, by simp [heq]⟩
  · intro hts heq
    apply hnot "ts+32" (by decide)
    unfold worldRoleSlots
    refine List.mem_filter.2 ⟨?_, by simp [ht]⟩
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    apply List.mem_append_left; apply List.mem_append_right
    unfold recRoles
    rw [if_neg hts]
    exact List.mem_map.2 ⟨(32, "ts+32"), by decide, by simp [heq]⟩

theorem epsA_htab_set_bs72_g10 :
    EvmPreservingSpecA
      (fun s => globN s "bs" ≠ 0 ∧ locN s "t" = memW s (globN s "bs" + 72) ∧ locN s "t" ≠ 0)
      (fun s _ post => GlobalsKept ["heap_ptr"] s post ∧ evmR post = evmR s)
      (ofString "htab_set") := by
  obtain ⟨params, body, rs, hlk, hfn⟩ := SoloHtabSet.htab_set_spec_proof
  refine ⟨params, body, rs, hlk, ?_⟩
  intro F s hc hi hw hp hl hn
  obtain ⟨hbs, heq, hnz⟩ := hp
  have ht : memW s (globN s "bs" + 72) ≠ 0 := by rwa [heq] at hnz
  have hb := Option.some.inj (SoloHtabSet.lookup_htab_set.symm.trans hlk)
  rcases Prod.mk.inj hb with ⟨_, hbr⟩
  rcases Prod.mk.inj hbr with ⟨hbody, _⟩
  subst hbody
  obtain ⟨ha, S, hi⟩ := hi
  have hS : memW s (globN s "bs" + 72) ∈ S := by
    rcases hi.1.1.2.2.2.2.1 72 (by decide) hbs with hz | hm
    · exact False.elim (ht hz)
    · exact hm
  have harg : HtabArgWF s := by
    refine ⟨ha, ?_, ?_⟩
    · rw [heq]; exact (hi.1.1.2.1 _ hS).1
    · rw [heq]; intro i hi'; exact ((hi.1.1.2.1 _ hS).2 i hi').1
  dsimp only
  refine ⟨fun v hv => ?_, ?_⟩
  · have hx := hfn s hc harg hl hn v hv
    unfold HtabExit at hx
    dsimp only at hx
    rw [heq] at hx
    obtain ⟨hap, htf, hhdr, _, hhp, hfp, hfr, hg⟩ := hx
    set post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_htab_set)).2
    obtain ⟨hws, hbs32, hba, had, hts32⟩ := bs72_separation_g10 hi hbs ht
    have hgw : GlobalsKept ["heap_ptr", "journal_n"] s post := by
      intro name hn
      apply hg name
      intro hm
      apply hn
      simp only [List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
      obtain ⟨x, rfl, hx⟩ := hm
      exact ⟨"heap_ptr", Or.inl rfl, hx⟩
    have hj : globN post "journal_n" ≤ globN s "journal_n" := by
      exact le_of_eq (OpHandlers.globN_eq_of_lookup_eq (hg (ofString "journal_n") (by decide))).symm
    obtain ⟨hip, hch, hr, hu⟩ := R16Shards.evmInvAt_of_htab_step ha hi hap
      (R16Shards.evaluate_be_eq s _) htf hhdr hhp hfp hfr hgw hj hS
      (fun i _ => bs72_not_delExclusive_g10 s S hbs i) hws hbs32 hba had (Or.inl hts32)
    have hev := (OpHandlers.globN_eq_of_lookup_eq (hg (ofString "ev") (by decide))).symm
    have hfm := (OpHandlers.globN_eq_of_lookup_eq (hg (ofString "frame_mem_ptr") (by decide))).symm
    exact ⟨⟨⟨hap, S, hip⟩, headMemChainWF_of_unhit_g10 ⟨ha, S, hi⟩ hw hch hu hev hfm⟩,
      hch, le_of_eq hr, hg, hr⟩
  · intro ⟨ev, hev⟩
    have hnc := R16Shards.StateRestoreEpilogue.evaluate_noCatchableRaise
      R16Shards.StateRestoreEpilogue.htabMutCallees R16Shards.StateRestoreEpilogue.htabMutCallees_good
      (sourceFnBody Guest.Software.guestFn_htab_set) (by decide) s hc
    exact False.elim (hnc (ofString "EvmErr") ev (by decide) hev)

theorem htab_set_callee_first_arg_g10 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hc : s.code = originalRuntimeCode)
    (tw : BitVec 64) (key value : ValueHOL 64)
    {body : ProgHOL 64} {callee : HolFiniteMapExact Flapjack.Pancake.PanLang.MlS (ValueHOL 64)}
    {rs : ShapeHOL}
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "htab_set")
      [.val (.word tw), key, value] = some (body, callee, rs)) :
    locN (callEntryStateHOLFinite s callee) "t" = tw.toNat := by
  have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some s.code.lookup
    (ofString "htab_set") [.val (.word tw), key, value] body callee rs hl
  rw [hc] at hx
  simp only [Flapjack.lookupCodeHOLExact, SoloHtabSet.lookup_htab_set] at hx
  split at hx
  · have hm := congrArg (fun x => x.2.1) (Option.some.inj hx)
    have ht : callee.lookup (ofString "t") = some (.val (.word tw)) := by
      have hh := congrFun hm.symm (ofString "t")
      have h1 : ofString "t" ≠ ofString "value" := by decide
      have h2 : ofString "t" ≠ ofString "key" := by decide
      have h3 : ofString "value" ≠ ofString "t" := by decide
      have h4 : ofString "key" ≠ ofString "t" := by decide
      simpa [List.map, List.zip, List.foldl, FUPDATE_LIST, FUPDATE, h1, h2, h3, h4] using hh
    simp [callEntryStateHOLFinite, locN, ht]
  · cases hx

theorem loaded_word_nat_g10 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (addr : ExpHOL 64) (a : Nat) (v : ValueHOL 64)
    (ha : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) addr =
      some (.val (.word (BitVec.ofNat 64 a))))
    (hv : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x))
      (.load .one addr) = some v) :
    ∃ w : BitVec 64, v = .val (.word w) ∧ w.toNat = memW s a := by
  unfold evalHOLExact at hv
  rw [ha] at hv
  dsimp only at hv
  unfold memLoadHOLExact at hv
  split at hv
  · split at hv
    · injection hv with heq
      unfold memW
      cases hm : s.memory (BitVec.ofNat 64 a) with
      | word w =>
        change ValueHOL.val (s.memory (BitVec.ofNat 64 a)) = v at heq
        rw [hm] at heq
        exact ⟨w, heq.symm, rfl⟩
    · cases hv
  · cases hv

theorem global_offset_eval_g10 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (g : String) (w : BitVec 64) (off : Nat)
    (hg : s.globals.lookup (ofString g) = some (.val (.word w))) :
    @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x))
      (.op .add [.var .global (ofString g), .const (BitVec.ofNat 64 off)]) =
      some (.val (.word (BitVec.ofNat 64 (globN s g + off)))) := by
  have hn : globN s g = w.toNat := by simp [globN, hg]
  simp only [evalHOLExact, evalListHOLExact, hg, wordOpHOL, wordOp, valueIsWord,
    valueWord, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr]
  congr 3
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, hn, Nat.add_mod]

theorem htab_set_loaded_global_callee_g10 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hc : s.code = originalRuntimeCode)
    (g : String) (off : Nat) (w : BitVec 64)
    (hg : s.globals.lookup (ofString g) = some (.val (.word w)))
    (keyExp : ExpHOL 64) {values : List (ValueHOL 64)}
    {body : ProgHOL 64} {callee : HolFiniteMapExact Flapjack.Pancake.PanLang.MlS (ValueHOL 64)}
    {rs : ShapeHOL}
    (hargs : evalListHOLFinite s (h := fun x => Classical.propDecidable (s.memaddrs x))
      [.load .one (.op .add [.var .global (ofString g), .const (BitVec.ofNat 64 off)]),
       keyExp, .const 1] = some values)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "htab_set") values = some (body, callee, rs)) :
    locN (callEntryStateHOLFinite s callee) "t" = memW s (globN s g + off) := by
  rw [evalListHOLFinite_eq_toExact] at hargs
  unfold evalListHOLExact at hargs
  rcases hv : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x))
      (.load .one (.op .add [.var .global (ofString g), .const (BitVec.ofNat 64 off)])) with _ | v
  · rw [hv] at hargs; simp at hargs
  · rw [hv] at hargs
    unfold evalListHOLExact at hargs
    rcases hk : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) keyExp with _ | key
    · rw [hk] at hargs; simp at hargs
    · rw [hk] at hargs
      unfold evalListHOLExact at hargs
      dsimp only [evalHOLExact] at hargs
      injection hargs with heq
      subst values
      obtain ⟨tw, rfl, htw⟩ := loaded_word_nat_g10 s _ _ v (global_offset_eval_g10 s g w off hg) hv
      exact (htab_set_callee_first_arg_g10 s hc tw key (.val (.word 1)) hl).trans htw

theorem bs72_callee_pre_of_nonzero_g10 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hc : s.code = originalRuntimeCode)
    (hbs : globN s "bs" ≠ 0) (ht : memW s (globN s "bs" + 72) ≠ 0)
    (keyExp : ExpHOL 64) {values : List (ValueHOL 64)}
    {body : ProgHOL 64} {callee : HolFiniteMapExact MlS (ValueHOL 64)}
    {rs : ShapeHOL}
    (hargs : evalListHOLFinite s (h := fun x => Classical.propDecidable (s.memaddrs x))
      [.load .one (.op .add [.var .global (ofString "bs"), .const 72]), keyExp, .const 1] = some values)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "htab_set") values = some (body, callee, rs)) :
    let ce := callEntryStateHOLFinite s callee
    globN ce "bs" ≠ 0 ∧ locN ce "t" = memW ce (globN ce "bs" + 72) ∧ locN ce "t" ≠ 0 := by
  obtain ⟨w, hg, _⟩ := global_word_of_pos s "bs" (Nat.pos_of_ne_zero hbs)
  have heq := htab_set_loaded_global_callee_g10 s hc "bs" 72 w hg keyExp hargs hl
  exact ⟨hbs, heq, by rw [heq]; exact ht⟩

theorem return_zero_preserves_aligned_g10 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hi : EvmInv s) (hw : Group10.HeadMemChainWF s) :
    let post := (evaluateHOLFiniteState s (.return (.const 0#64))).2
    EvmInv post ∧ Group10.HeadMemChainWF post ∧ evmChain post = evmChain s ∧
      evmR post = evmR s ∧ post.globals = s.globals := by
  rw [evaluateHOLFiniteState_return]
  dsimp only [evalHOLExact]
  have hsz : sizeOfShapeWithContextHOL s.structs (shapeOfHOLExact (.val (.word 0#64))) ≤ 32 := by
    simp [shapeOfHOLExact]
  rw [if_pos hsz]
  dsimp only
  refine ⟨localsFree_evmInv s _ s.clock hi,
    Group10.headMemChainWF_locals s _ s.clock hw, ?_, ?_, rfl⟩
  · exact evmChain_congr rfl rfl
  · exact (evm_congr (s := s) (t := s.emptyLocalsHOLFinite) rfl rfl).2.1

theorem call0_returned_inv_g10 {F : Type} {s post_call : PanSemStateFiniteExact 64 F}
    {fname : MlS} {args : List (ExpHOL 64)}
    (hcall : evaluateHOLFiniteState s (.call (some (none, none)) fname args) = (none, post_call)) :
    ∃ values body callee ret v cpost,
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some values ∧
      lookupCodeHOLFinite s.code.lookup fname values = some (body, callee, ret) ∧
      evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), cpost) ∧
      post_call = { cpost with locals := s.locals } := by
  rw [evaluateHOLFiniteState_call] at hcall
  revert hcall
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
  · simp
  · dsimp only
    rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body, callee, ret⟩
    · simp
    · dsimp only
      by_cases hz : s.clock = 0
      · simp [hz]
      · simp only [hz, ↓reduceIte]
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨res, cpost⟩
        rcases res with _ | r
        · simp
        · cases r with
          | returned v =>
            dsimp only; split
            · intro h; injection h with _ hp
              exact ⟨values, body, callee, ret, v, cpost, rfl, hl, hrun, hp.symm⟩
            · simp
          | _ => simp

theorem bs72_call_preserves_g10 {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hc : s.code = originalRuntimeCode) (hi : EvmInv s) (hw : Group10.HeadMemChainWF s)
    (hbs : globN s "bs" ≠ 0) (ht : memW s (globN s "bs" + 72) ≠ 0)
    (keyExp : ExpHOL 64)
    (hcall : evaluateHOLFiniteState s (.call (some (none, none)) (ofString "htab_set")
      [.load .one (.op .add [.var .global (ofString "bs"), .const 72]), keyExp, .const 1]) = (none, post)) :
    EvmInv post ∧ Group10.HeadMemChainWF post ∧ evmChain post = evmChain s ∧
      evmR post = evmR s ∧ GlobalsKept ["heap_ptr"] s post := by
  obtain ⟨values, body, callee, rs, v, cp, hargs, hl, hr, rfl⟩ := call0_returned_inv_g10 hcall
  obtain ⟨params, body0, rs0, hl0, hs⟩ := epsA_htab_set_bs72_g10
  have hbody : body = body0 := lookupCodeHOLFinite_installed_body s.code.lookup
    (ofString "htab_set") params body0 body rs0 rs values callee (by rwa [hc]) hl
  subst body
  have hrs : rs = rs0 := by
    have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some s.code.lookup
      (ofString "htab_set") values body0 callee rs hl
    rw [hc] at hx
    simp only [Flapjack.lookupCodeHOLExact, hl0] at hx
    split at hx
    · exact (congrArg (fun x => x.2.2) (Option.some.inj hx)).symm
    · cases hx
  subst rs
  have hp := bs72_callee_pre_of_nonzero_g10 s hc hbs ht keyExp hargs hl
  have hs' := hs (callEntryStateHOLFinite s callee) hc
    (localsFree_evmInv s callee (s.clock - 1) hi)
    (Group10.headMemChainWF_locals s callee (s.clock - 1) hw) hp
    ⟨values, by rwa [← hc]⟩
  dsimp only at hs'
  rw [hr] at hs'
  obtain ⟨⟨hic, hwc⟩, hch, _, hg, heq⟩ := (hs' (by simp)).1 v rfl
  refine ⟨localsFree_evmInv cp s.locals cp.clock hic,
    Group10.headMemChainWF_locals cp s.locals cp.clock hwc, ?_, ?_, hg⟩
  · have h1 : evmChain {cp with locals := s.locals} = evmChain cp :=
      evmChain_congr rfl rfl
    have h2 : evmChain (callEntryStateHOLFinite s callee) = evmChain s :=
      evmChain_congr rfl rfl
    exact h1.trans (hch.trans h2)
  · exact (evm_congr (s := cp) (t := {cp with locals := s.locals}) rfl rfl).2.1.trans
      (heq.trans (evm_congr (s := s) (t := callEntryStateHOLFinite s callee) rfl rfl).2.1)

theorem guestInv_zero_not_mem_g10 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hi : GuestInv s) : ¬ s.memaddrs 0 := by
  rw [hi.memaddrs, SoloHtabSet.ordinaryDomain_iff]
  decide

theorem htab_set_zero_fails_g10 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hi : GuestInv s)
    (ht : s.locals.lookup (ofString "t") = some (.val (.word 0#64))) :
    (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_htab_set)).1 =
      some .error := by
  have hz := guestInv_zero_not_mem_g10 s hi
  change ¬ s.memaddrs 0#64 at hz
  have hb : ∃ body, sourceFnBody Guest.Software.guestFn_htab_set =
      .dec (ofString "klen") .one
        (.load .one (.op .add [.var .local (ofString "t"), .const 0])) body := ⟨_, rfl⟩
  obtain ⟨body, hb⟩ := hb
  rw [hb, evaluateHOLFiniteState_dec_total]
  simp [evalHOLExact, evalListHOLExact, ht, wordOpHOL, wordOp, valueIsWord,
    valueWord, memLoadHOLExact, hz]

theorem htab_set_returned_word_nonzero_g10 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hi : GuestInv s)
    (w : BitVec 64)
    (ht : s.locals.lookup (ofString "t") = some (.val (.word w)))
    (v : ValueHOL 64)
    (hr : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_htab_set)).1 =
      some (.returned v)) : w.toNat ≠ 0 := by
  intro hz
  have hw : w = 0#64 := BitVec.eq_of_toNat_eq hz
  subst w
  rw [htab_set_zero_fails_g10 s hi ht] at hr
  cases hr

theorem htab_set_word_return_nonzero_g10 {F : Type}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)}
    (s : PanSemStateFiniteExact 64 F) (hc : s.code = originalRuntimeCode)
    (hi : GuestInv (callEntryStateHOLFinite s callee))
    (tw : BitVec 64) (key value v : ValueHOL 64)
    {body : ProgHOL 64} {rs : ShapeHOL}
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "htab_set")
      [.val (.word tw), key, value] = some (body, callee, rs))
    (hr : (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body).1 = some (.returned v)) :
    tw.toNat ≠ 0 := by
  have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some s.code.lookup
    (ofString "htab_set") [.val (.word tw), key, value] body callee rs hl
  rw [hc] at hx
  simp only [Flapjack.lookupCodeHOLExact, SoloHtabSet.lookup_htab_set] at hx
  split at hx
  · have hm := congrArg (fun x => x.2.1) (Option.some.inj hx)
    have ht : callee.lookup (ofString "t") = some (.val (.word tw)) := by
      have hh := congrFun hm.symm (ofString "t")
      have h1 : ofString "t" ≠ ofString "value" := by decide
      have h2 : ofString "t" ≠ ofString "key" := by decide
      have h3 : ofString "value" ≠ ofString "t" := by decide
      have h4 : ofString "key" ≠ ofString "t" := by decide
      simpa [List.map, List.zip, List.foldl, FUPDATE_LIST, FUPDATE, h1, h2, h3, h4] using hh
    have hb : body = sourceFnBody Guest.Software.guestFn_htab_set :=
      lookupCodeHOLFinite_installed_body s.code.lookup (ofString "htab_set") _ _ _ _ _ _ _
        (by rw [hc]; exact SoloHtabSet.lookup_htab_set) hl
    apply htab_set_returned_word_nonzero_g10 (callEntryStateHOLFinite s callee) hi tw ht v
    rw [← hb]
    exact hr
  · cases hx

theorem loaded_global_return_nonzero_g10 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hc : s.code = originalRuntimeCode)
    (g : String) (off : Nat) (w : BitVec 64)
    (hg : s.globals.lookup (ofString g) = some (.val (.word w)))
    (keyExp : ExpHOL 64) {values : List (ValueHOL 64)}
    {body : ProgHOL 64} {callee : HolFiniteMapExact MlS (ValueHOL 64)} {rs : ShapeHOL}
    (hi : GuestInv (callEntryStateHOLFinite s callee))
    (hargs : evalListHOLFinite s (h := fun x => Classical.propDecidable (s.memaddrs x))
      [.load .one (.op .add [.var .global (ofString g), .const (BitVec.ofNat 64 off)]),
       keyExp, .const 1] = some values)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "htab_set") values = some (body, callee, rs))
    (ret : ValueHOL 64)
    (hr : (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body).1 = some (.returned ret)) :
    memW s (globN s g + off) ≠ 0 := by
  rw [evalListHOLFinite_eq_toExact] at hargs
  unfold evalListHOLExact at hargs
  rcases hv : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x))
      (.load .one (.op .add [.var .global (ofString g), .const (BitVec.ofNat 64 off)])) with _ | v
  · rw [hv] at hargs; simp at hargs
  · rw [hv] at hargs
    unfold evalListHOLExact at hargs
    rcases hk : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) keyExp with _ | key
    · rw [hk] at hargs; simp at hargs
    · rw [hk] at hargs
      unfold evalListHOLExact at hargs
      dsimp only [evalHOLExact] at hargs
      injection hargs with heq
      subst values
      obtain ⟨tw, rfl, htw⟩ := loaded_word_nat_g10 s _ _ v (global_offset_eval_g10 s g w off hg) hv
      rw [← htw]
      exact htab_set_word_return_nonzero_g10 s hc hi tw key (.val (.word 1)) ret hl hr

theorem bs72_call_nonzero_g10 {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hc : s.code = originalRuntimeCode) (hi : EvmInv s)
    (hbs : globN s "bs" ≠ 0) (keyExp : ExpHOL 64)
    (hcall : evaluateHOLFiniteState s (.call (some (none, none)) (ofString "htab_set")
      [.load .one (.op .add [.var .global (ofString "bs"), .const 72]), keyExp, .const 1]) = (none, post)) :
    memW s (globN s "bs" + 72) ≠ 0 := by
  obtain ⟨values, body, callee, rs, v, cp, hargs, hl, hr, _⟩ := call0_returned_inv_g10 hcall
  obtain ⟨w, hg, _⟩ := global_word_of_pos s "bs" (Nat.pos_of_ne_zero hbs)
  exact loaded_global_return_nonzero_g10 s hc "bs" 72 w hg keyExp
    (localsFree_evmInv s callee (s.clock - 1) hi).1.1 hargs hl v (congrArg Prod.fst hr)

theorem guestInv_low_not_mem_g10 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hi : GuestInv s) (a : BitVec 64) (ha : a.toNat < 2701131776) :
    ¬ s.memaddrs a := by
  rw [hi.memaddrs, SoloHtabSet.ordinaryDomain_iff]
  omega

theorem global_zero_offset_load_none_g10 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hi : GuestInv s)
    (g : String) (off : Nat) (hoff : off < 2701131776)
    (hg : s.globals.lookup (ofString g) = some (.val (.word 0#64))) :
    @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x))
      (.load .one (.op .add [.var .global (ofString g), .const (BitVec.ofNat 64 off)])) = none := by
  have hn : globN s g = 0 := by simp [globN, hg]
  have he := global_offset_eval_g10 s g 0 off hg
  rw [hn, Nat.zero_add] at he
  have hm := guestInv_low_not_mem_g10 s hi (BitVec.ofNat 64 off)
    (by rw [BitVec.toNat_ofNat]; exact lt_of_le_of_lt (Nat.mod_le _ _) hoff)
  unfold evalHOLExact
  rw [he]
  simp [memLoadHOLExact, hm]

theorem global_offset_load_success_nonzero_g10 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hi : GuestInv s)
    (g : String) (off : Nat) (hoff : off < 2701131776) (v : ValueHOL 64)
    (hv : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x))
      (.load .one (.op .add [.var .global (ofString g), .const (BitVec.ofNat 64 off)])) = some v) :
    globN s g ≠ 0 := by
  intro hz
  cases hg : s.globals.lookup (ofString g) with
  | none => simp [evalHOLExact, evalListHOLExact, hg] at hv
  | some val =>
    cases val with
    | rStruct fields => simp [evalHOLExact, evalListHOLExact, hg, valueIsWord] at hv
    | nStruct name fields => simp [evalHOLExact, evalListHOLExact, hg, valueIsWord] at hv
    | val word =>
      cases word with
      | word w =>
        have hw : w.toNat = 0 := by simpa [globN, hg] using hz
        have hw0 : w = 0#64 := BitVec.eq_of_toNat_eq hw
        subst w
        rw [global_zero_offset_load_none_g10 s hi g off hoff hg] at hv
        cases hv

theorem bs72_call_root_nonzero_g10 {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hi : EvmInv s) (keyExp : ExpHOL 64)
    (hcall : evaluateHOLFiniteState s (.call (some (none, none)) (ofString "htab_set")
      [.load .one (.op .add [.var .global (ofString "bs"), .const 72]), keyExp, .const 1]) = (none, post)) :
    globN s "bs" ≠ 0 := by
  obtain ⟨values, body, callee, rs, v, cp, hargs, _, _, _⟩ := call0_returned_inv_g10 hcall
  rw [evalListHOLFinite_eq_toExact] at hargs
  unfold evalListHOLExact at hargs
  rcases hv : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x))
      (.load .one (.op .add [.var .global (ofString "bs"), .const 72])) with _ | value
  · rw [hv] at hargs; simp at hargs
  · exact global_offset_load_success_nonzero_g10 s hi.1.1 "bs" 72 (by decide) value hv

/-- Recording a pre-state read preserves alignment; successful execution supplies both roots. -/
theorem epsA_record_pre_state_read_g10 :
    EvmPreservingSpecA
      (fun _ => True)
      (fun s _ post => GlobalsKept ["heap_ptr"] s post ∧ evmR post = evmR s)
      (ofString "record_pre_state_read") := by
  have hl : originalRuntimeCode.lookup (ofString "record_pre_state_read") =
      some ((sourceFunctionEntry Guest.Software.guestFn_record_pre_state_read).2) :=
    lookup_of_guestAst_getElem 364 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_record_pre_state_read) rfl
  refine ⟨[(ofString "addr", ShapeHOL.one)], sourceFnBody Guest.Software.guestFn_record_pre_state_read,
    ShapeHOL.one, hl, ?_⟩
  intro F s hc hi hw hp _ _
  have hb : sourceFnBody Guest.Software.guestFn_record_pre_state_read =
      .seq (.call (some (none, none)) (ofString "htab_set")
        [.load .one (.op .add [.var .global (ofString "bs"), .const 72]),
         .var .local (ofString "addr"), .const 1]) (.return (.const 0#64)) := rfl
  dsimp only
  refine ⟨?_, ?_⟩
  · intro v hv
    rcases hr : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_record_pre_state_read) with ⟨r, post⟩
    rw [hr] at hv
    dsimp only at hv
    subst r
    have hr' := hr
    rw [hb] at hr'
    obtain ⟨mid, hcall, hret⟩ := seq_call0_ret_inv hr'
    have hbs := bs72_call_root_nonzero_g10 hi _ hcall
    have ht := bs72_call_nonzero_g10 hc hi hbs _ hcall
    obtain ⟨him, hwm, hch, hR, hg⟩ := bs72_call_preserves_g10 hc hi hw hbs ht _ hcall
    have hpost := return_zero_preserves_aligned_g10 mid him hwm
    dsimp only at hpost
    rw [hret] at hpost
    obtain ⟨hip, hwp, hchp, hRp, hgp⟩ := hpost
    exact ⟨⟨hip, hwp⟩, hchp.trans hch, le_of_eq (hRp.trans hR),
      (by intro n hn; rw [hgp]; exact hg n hn), hRp.trans hR⟩
  · intro ⟨ev, hev⟩
    have hnc := R16Shards.StateRestoreEpilogue.evaluate_noCatchableRaise
      R16Shards.StateRestoreEpilogue.htabMutCallees R16Shards.StateRestoreEpilogue.htabMutCallees_good
      (sourceFnBody Guest.Software.guestFn_record_pre_state_read) (by decide) s hc
    exact False.elim (hnc (ofString "EvmErr") ev (by decide) hev)

theorem ts8_call_roots_nonzero_g10 {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hc : s.code = originalRuntimeCode) (hi : EvmInv s) (keyExp : ExpHOL 64)
    (hcall : evaluateHOLFiniteState s (.call (some (none, none)) (ofString "htab_set")
      [.load .one (.op .add [.var .global (ofString "ts"), .const 8]), keyExp, .const 1]) = (none, post)) :
    globN s "ts" ≠ 0 ∧ memW s (globN s "ts" + 8) ≠ 0 := by
  obtain ⟨values, body, callee, rs, v, cp, hargs, hl, hr, _⟩ := call0_returned_inv_g10 hcall
  have hts : globN s "ts" ≠ 0 := by
    have ha := hargs
    rw [evalListHOLFinite_eq_toExact] at ha
    unfold evalListHOLExact at ha
    rcases hv : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x))
        (.load .one (.op .add [.var .global (ofString "ts"), .const 8])) with _ | value
    · rw [hv] at ha; simp at ha
    · exact global_offset_load_success_nonzero_g10 s hi.1.1 "ts" 8 (by decide) value hv
  obtain ⟨w, hg, _⟩ := global_word_of_pos s "ts" (Nat.pos_of_ne_zero hts)
  exact ⟨hts, loaded_global_return_nonzero_g10 s hc "ts" 8 w hg keyExp
    (localsFree_evmInv s callee (s.clock - 1) hi).1.1 hargs hl v (congrArg Prod.fst hr)⟩

theorem ts8_call_preserves_g10 {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hc : s.code = originalRuntimeCode) (hi : EvmInv s) (hw : Group10.HeadMemChainWF s)
    (keyExp : ExpHOL 64)
    (hcall : evaluateHOLFiniteState s (.call (some (none, none)) (ofString "htab_set")
      [.load .one (.op .add [.var .global (ofString "ts"), .const 8]), keyExp, .const 1]) = (none, post)) :
    EvmInv post ∧ Group10.HeadMemChainWF post ∧ evmChain post = evmChain s ∧
      evmR post = evmR s ∧ GlobalsKept ["heap_ptr"] s post := by
  obtain ⟨hts, ht⟩ := ts8_call_roots_nonzero_g10 hc hi keyExp hcall
  obtain ⟨values, body, callee, rs, v, cp, hargs, hl, hr, rfl⟩ := call0_returned_inv_g10 hcall
  obtain ⟨params, body0, rs0, hl0, hs⟩ := epsA_htab_set_ts8_g10
  have hbody : body = body0 := lookupCodeHOLFinite_installed_body s.code.lookup
    (ofString "htab_set") params body0 body rs0 rs values callee (by rwa [hc]) hl
  subst body
  have hrs : rs = rs0 := by
    have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some s.code.lookup
      (ofString "htab_set") values body0 callee rs hl
    rw [hc] at hx
    simp only [Flapjack.lookupCodeHOLExact, hl0] at hx
    split at hx
    · exact (congrArg (fun x => x.2.2) (Option.some.inj hx)).symm
    · cases hx
  subst rs
  obtain ⟨w, hg, _⟩ := global_word_of_pos s "ts" (Nat.pos_of_ne_zero hts)
  have heq := htab_set_loaded_global_callee_g10 s hc "ts" 8 w hg keyExp hargs hl
  have hp : let ce := callEntryStateHOLFinite s callee
      globN ce "ts" ≠ 0 ∧ locN ce "t" = memW ce (globN ce "ts" + 8) ∧ locN ce "t" ≠ 0 :=
    ⟨hts, heq, by rw [heq]; exact ht⟩
  have hs' := hs (callEntryStateHOLFinite s callee) hc
    (localsFree_evmInv s callee (s.clock - 1) hi)
    (Group10.headMemChainWF_locals s callee (s.clock - 1) hw) hp
    ⟨values, by rwa [← hc]⟩
  dsimp only at hs'
  rw [hr] at hs'
  obtain ⟨⟨hic, hwc⟩, hch, _, hglobals, hR⟩ := (hs' (by simp)).1 v rfl
  refine ⟨localsFree_evmInv cp s.locals cp.clock hic,
    Group10.headMemChainWF_locals cp s.locals cp.clock hwc, ?_, ?_, hglobals⟩
  · have h1 : evmChain {cp with locals := s.locals} = evmChain cp := evmChain_congr rfl rfl
    have h2 : evmChain (callEntryStateHOLFinite s callee) = evmChain s := evmChain_congr rfl rfl
    exact h1.trans (hch.trans h2)
  · exact (evm_congr (s := cp) (t := {cp with locals := s.locals}) rfl rfl).2.1.trans
      (hR.trans (evm_congr (s := s) (t := callEntryStateHOLFinite s callee) rfl rfl).2.1)

theorem readOnly_preserves_aligned_g10 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (p : ProgHOL 64)
    (hc : s.code = originalRuntimeCode) (hi : EvmInv s) (hw : Group10.HeadMemChainWF s)
    (hp : readOnlyProg opRoCallees p = true)
    (hr : Resumes (evaluateHOLFiniteState s p).1) :
    let post := (evaluateHOLFiniteState s p).2
    EvmInv post ∧ Group10.HeadMemChainWF post ∧ evmChain post = evmChain s ∧
      evmR post = evmR s ∧ LocFrame s post := by
  have hlf := (evaluate_readOnlyProg opRoCallees opRoCallees_good p hp s hc).to_resumes hr
  dsimp only
  have hip : EvmInv (evaluateHOLFiniteState s p).2 := by
    have h := localsFree_evmInv s (evaluateHOLFiniteState s p).2.locals
      (evaluateHOLFiniteState s p).2.clock hi
    rwa [← hlf] at h
  have hm : (evaluateHOLFiniteState s p).2.memory = s.memory := by rw [hlf]
  have hg : (evaluateHOLFiniteState s p).2.globals = s.globals := by rw [hlf]
  exact ⟨hip, headMemChainWF_of_locFrame hw hlf, evmChain_congr hm hg,
    (evm_congr hm hg).2.1, hlf⟩

theorem epsA_htab_get_ro_g10 :
    EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "htab_get") :=
  epsA_of_readOnly 132 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_htab_get rfl opRoCallees opRoCallees_good rfl

theorem ts8_then_readOnly_preserves_g10 {F : Type}
    {s mid post : PanSemStateFiniteExact 64 F}
    (hc : s.code = originalRuntimeCode) (hi : EvmInv s) (hw : Group10.HeadMemChainWF s)
    (keyExp : ExpHOL 64) (cont : ProgHOL 64)
    (hcall : evaluateHOLFiniteState s (.call (some (none, none)) (ofString "htab_set")
      [.load .one (.op .add [.var .global (ofString "ts"), .const 8]), keyExp, .const 1]) = (none, mid))
    (hro : readOnlyProg opRoCallees cont = true)
    (v : ValueHOL 64) (hret : evaluateHOLFiniteState mid cont = (some (.returned v), post)) :
    EvmInv post ∧ Group10.HeadMemChainWF post ∧ evmChain post = evmChain s ∧
      evmR post = evmR s ∧ GlobalsKept ["heap_ptr"] s post := by
  obtain ⟨him, hwm, hch, hR, hg⟩ := ts8_call_preserves_g10 hc hi hw keyExp hcall
  have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata s
    (.call (some (none, none)) (ofString "htab_set")
      [.load .one (.op .add [.var .global (ofString "ts"), .const 8]), keyExp, .const 1])).1
  rw [hcall] at hmeta
  have hp := readOnly_preserves_aligned_g10 mid cont (hmeta.trans hc) him hwm hro
    (Or.inl ⟨v, congrArg Prod.fst hret⟩)
  dsimp only at hp
  rw [hret] at hp
  obtain ⟨hip, hwp, hchp, hRp, hlf⟩ := hp
  change LocFrame mid post at hlf
  refine ⟨hip, hwp, hchp.trans hch, hRp.trans hR, ?_⟩
  intro n hn
  have hgp : post.globals = mid.globals := by rw [hlf]
  rw [hgp]
  exact hg n hn

/-- Boundary for a child-running suffix after the opcode has charged gas.
The suffix may change the chain on return; errors must retain its depth. -/
def ChildContinuationA {F : Type}
    (P : PanSemStateFiniteExact 64 F → Prop) (prog : ProgHOL 64) : Prop :=
  ∀ t : PanSemStateFiniteExact 64 F, t.code = originalRuntimeCode →
    EvmInv t → Group10.HeadMemChainWF t → P t →
    (evaluateHOLFiniteState t prog).1 ≠ some .timeOut →
    let r := (evaluateHOLFiniteState t prog).1
    let post := (evaluateHOLFiniteState t prog).2
    ((∃ v, r = some (.returned v)) →
      (EvmInv post ∧ Group10.HeadMemChainWF post) ∧ evmR post ≤ evmR t) ∧
    (IsEvmErr r → (EvmInv post ∧ Group10.HeadMemChainWF post) ∧
      (evmChain post).length = (evmChain t).length ∧ evmR post ≤ evmR t)

theorem handlerRunA_of_childContinuation_g10 {F : Type}
    (s0 : PanSemStateFiniteExact 64 F) (P : PanSemStateFiniteExact 64 F → Prop)
    (prog : ProgHOL 64) (hchild : ChildContinuationA P prog) :
    HandlerRunA s0 P true prog := by
  intro t hc hi hw hlen hR hp hnt
  have h := hchild t hc hi hw hp hnt
  refine ⟨?_, ?_⟩
  · intro hr
    obtain ⟨hinv, hle⟩ := h.1 hr
    exact ⟨hinv, evmPot_lt_of_evmR_lt hinv.1 (lt_of_le_of_lt hle hR)⟩
  · intro he
    obtain ⟨hinv, hdepth, hle⟩ := h.2 he
    exact ⟨hinv, hdepth.trans hlen, le_trans hle (Nat.le_of_lt hR)⟩

theorem charge_then_childContinuation_g10 {F : Type}
    (s0 : PanSemStateFiniteExact 64 F)
    (P Q : PanSemStateFiniteExact 64 F → Prop) (charged : Bool)
    (amtExp : ExpHOL 64) (cont : ProgHOL 64)
    (hpos : ∀ t (w : BitVec 64),
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) amtExp =
        some (.val (.word w)) → EvmInv t → Group10.HeadMemChainWF t → P t → 0 < w.toNat)
    (hstep : ∀ t cpost,
      EvmInv t → Group10.HeadMemChainWF t → P t →
      EvmInv cpost → Group10.HeadMemChainWF cpost →
      cpost.globals = t.globals → evmChain cpost = evmChain t →
      Q { cpost with locals := t.locals })
    (hchild : ChildContinuationA Q cont) :
    HandlerRunA s0 P charged
      (.seq (.call (some (none, none)) (ofString "charge_gas") [amtExp]) cont) :=
  HandlerRunA.seq_charge_gas hpos hstep
    (handlerRunA_of_childContinuation_g10 s0 Q cont hchild)

/-- Both creation base costs remain positive without word overflow. -/
theorem create_base_cost_positive_g10 (w : BitVec 64) (hw : w.toNat < 2 ^ 59) :
    0 < (12000#64 + 2#64 * w).toNat ∧
    0 < (12000#64 + 6#64 * w + 2#64 * w).toNat := by
  have h2 : 2 * w.toNat < 2 ^ 64 := by omega
  have h6 : 6 * w.toNat < 2 ^ 64 := by omega
  have ha : 12000 + 2 * w.toNat < 2 ^ 64 := by omega
  have hb : 12000 + 6 * w.toNat < 2 ^ 64 := by omega
  have hc : 12000 + 6 * w.toNat + 2 * w.toNat < 2 ^ 64 := by omega
  simp only [BitVec.toNat_add, BitVec.toNat_mul]
  norm_num only [BitVec.toNat_ofNat] at *
  rw [Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h6,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hc]
  omega

/-- The actual saturating cost computation is positive for either creation opcode. -/
theorem create_add_sat_return_positive_g10 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (w memoryCost : BitVec 64)
    (hw : w.toNat < 2 ^ 59) (isCreate2 : Bool)
    (ha : s.locals.lookup (ofString "a") = some (.val (.word
      (if isCreate2 then 12000#64 + 6#64 * w + 2#64 * w else 12000#64 + 2#64 * w))))
    (hb : s.locals.lookup (ofString "b") = some (.val (.word memoryCost)))
    (v : ValueHOL 64)
    (hr : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_add_sat)).1 =
      some (.returned v)) :
    ∃ cost : BitVec 64, v = .val (.word cost) ∧ 0 < cost.toNat := by
  apply Group10.add_sat_return_positive_g10 s ha hb ?_ v hr
  have hp := create_base_cost_positive_g10 w hw
  cases isCreate2 <;> simp_all

def PositiveCostLocal_g10 {F : Type} (name : MlS)
    (s : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ w : BitVec 64, s.locals.lookup name = some (.val (.word w)) ∧ 0 < w.toNat

theorem bound_cost_local_positive_g10 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (name : MlS) (w : BitVec 64)
    (hw : 0 < w.toNat) :
    PositiveCostLocal_g10 name (setVarHOLFinite name (.val (.word w)) s) := by
  refine ⟨w, ?_, hw⟩
  simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]

theorem charge_positive_local_then_child_g10 {F : Type}
    (s0 : PanSemStateFiniteExact 64 F) (name : MlS) (cont : ProgHOL 64)
    (charged : Bool) (hchild : ChildContinuationA (F := F) (PositiveCostLocal_g10 name) cont) :
    HandlerRunA s0 (PositiveCostLocal_g10 name) charged
      (.seq (.call (some (none, none)) (ofString "charge_gas") [.var .local name]) cont) := by
  apply charge_then_childContinuation_g10 s0 (PositiveCostLocal_g10 name)
    (PositiveCostLocal_g10 name) charged (.var .local name) cont
  · intro t w he hi hf hp
    obtain ⟨cw, hc, hpos⟩ := hp
    have he' : t.locals.lookup name = some (.val (.word w)) := he
    rw [hc] at he'
    cases he'
    exact hpos
  · intro t post hi hf hp hpi hpf hg hchain
    exact hp
  · exact hchild

theorem create_cost_binding_then_charge_g10 {F : Type}
    (callee caller s0 : PanSemStateFiniteExact 64 F)
    (w memoryCost : BitVec 64) (hw : w.toNat < 2 ^ 59) (isCreate2 : Bool)
    (ha : callee.locals.lookup (ofString "a") = some (.val (.word
      (if isCreate2 then 12000#64 + 6#64 * w + 2#64 * w else 12000#64 + 2#64 * w))))
    (hb : callee.locals.lookup (ofString "b") = some (.val (.word memoryCost)))
    (v : ValueHOL 64)
    (hr : (evaluateHOLFiniteState callee (sourceFnBody Guest.Software.guestFn_add_sat)).1 =
      some (.returned v))
    (name : MlS) (cont : ProgHOL 64) (charged : Bool)
    (hchild : ChildContinuationA (F := F) (PositiveCostLocal_g10 name) cont) :
    PositiveCostLocal_g10 name (setVarHOLFinite name v caller) ∧
    HandlerRunA s0 (PositiveCostLocal_g10 name) charged
      (.seq (.call (some (none, none)) (ofString "charge_gas") [.var .local name]) cont) := by
  obtain ⟨cost, rfl, hpos⟩ := create_add_sat_return_positive_g10 callee w memoryCost hw isCreate2 ha hb v hr
  exact ⟨bound_cost_local_positive_g10 caller name cost hpos,
    charge_positive_local_then_child_g10 s0 name cont charged hchild⟩

theorem words_shift_return_bound_g10 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (cw : BitVec 64)
    (hc : s.locals.lookup (ofString "c") = some (.val (.word cw)))
    (v : ValueHOL 64)
    (hr : (evaluateHOLFiniteState s
      (.return (.shift .lsr (.var .local (ofString "c")) (.const 5#64)))).1 = some (.returned v)) :
    ∃ w : BitVec 64, v = .val (.word w) ∧ w.toNat < 2 ^ 59 := by
  have h5 : (5#64 : BitVec 64).toNat = 5 := rfl
  have hsh : wordShiftHOL .lsr cw 5 = some (cw >>> (5 : Nat)) := by simp [wordShiftHOL]
  rw [evaluateHOLFiniteState_return] at hr
  have he : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.shift .lsr (.var .local (ofString "c")) (.const 5#64)) =
      some (.val (.word (cw >>> (5 : Nat)))) := by
    simp [evalHOLExact, hc, h5, hsh]
  rw [he] at hr
  dsimp only at hr
  split at hr
  · injection hr with hh
    injection hh with hv
    refine ⟨cw >>> (5 : Nat), hv.symm, ?_⟩
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have := cw.isLt
    omega
  · simp at hr

theorem words_of_return_bound_g10 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (nw : BitVec 64)
    (hcode : s.code = originalRuntimeCode)
    (hn : s.locals.lookup (ofString "n") = some (.val (.word nw)))
    (v : ValueHOL 64)
    (hr : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_words_of)).1 =
      some (.returned v)) :
    ∃ w : BitVec 64, v = .val (.word w) ∧ w.toNat < 2 ^ 59 := by
  have hb : sourceFnBody Guest.Software.guestFn_words_of =
      .decCall (ofString "c") .one (ofString "ceil32") [.var .local (ofString "n")]
        (.return (.shift .lsr (.var .local (ofString "c")) (.const 5#64))) := rfl
  rw [hb, evaluateHOLFiniteState_decCall_fixClockRewrite] at hr
  have ha : evalListHOLFinite s (h := fun x => Classical.propDecidable (s.memaddrs x))
      [.var .local (ofString "n")] = some [.val (.word nw)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hn]
  rw [ha] at hr
  dsimp only at hr
  have hl := pan_one_word_lookup s.code.lookup (ofString "ceil32") (ofString "v")
    (sourceFnBody Guest.Software.guestFn_ceil32) nw
    (by rw [hcode]; exact Group10.lookup_ceil32)
  rw [hl] at hr
  dsimp only at hr
  split at hr
  · simp at hr
  · rcases he : evaluateHOLFiniteState
        (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "v", .val (.word nw))))
        (sourceFnBody Guest.Software.guestFn_ceil32) with ⟨rb, pb⟩
    rw [he] at hr
    cases rb with
    | none => simp at hr
    | some rb =>
      cases rb with
      | returned vb =>
        cases vb with
        | val scalar =>
          cases scalar with
          | word cw =>
            dsimp only at hr
            split at hr
            · apply words_shift_return_bound_g10 _ cw _ v hr
              simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
            · simp at hr
        | _ => simp [shapeOfHOLExact, shapeEqHOL] at hr
      | _ => simp at hr

theorem epsA_refine_return_g10
    {P P' : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {Q Q' : ∀ {F : Type}, PanSemStateFiniteExact 64 F → ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    {fname : MlS} {params : List (MlS × ShapeHOL)} {body : ProgHOL 64} {rs : ShapeHOL}
    (hl : originalRuntimeCode.lookup fname = some (params, body, rs))
    (hf : EvmPreservingSpecA P Q fname)
    (hp : ∀ {F} (s : PanSemStateFiniteExact 64 F), P' s → P s)
    (hq : ∀ {F} (s : PanSemStateFiniteExact 64 F) v post,
      s.code = originalRuntimeCode → P' s → Q s v post →
      (evaluateHOLFiniteState s body).1 = some (.returned v) → Q' s v post) :
    EvmPreservingSpecA P' Q' fname := by
  obtain ⟨params', body', rs', hl', hs⟩ := hf
  rw [hl] at hl'
  cases hl'
  refine ⟨params, body, rs, hl, ?_⟩
  intro F s hc hi hw hpre hlookup hnt
  have h := hs s hc hi hw (hp s hpre) hlookup hnt
  exact ⟨fun v hv => ⟨(h.1 v hv).1, (h.1 v hv).2.1,
    (h.1 v hv).2.2.1, hq s v _ hc hpre (h.1 v hv).2.2.2 hv⟩, h.2⟩

theorem epsA_words_of_bounded_g10 :
    EvmPreservingSpecA
      (fun s => ∃ n : BitVec 64, s.locals.lookup (ofString "n") = some (.val (.word n)))
      (fun s v post => LocFrame s post ∧ ∃ w : BitVec 64, v = .val (.word w) ∧ w.toNat < 2 ^ 59)
      (ofString "words_of") := by
  apply epsA_refine_return_g10 lookup_words_of epsA_words_of (fun _ _ => trivial)
  intro F s v post hc hp hq hr
  obtain ⟨n, hn⟩ := hp
  exact ⟨hq, words_of_return_bound_g10 s n hc hn v hr⟩

def CreateCostArgs_g10 {F : Type} (isCreate2 : Bool)
    (s : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ w memoryCost : BitVec 64, w.toNat < 2 ^ 59 ∧
    s.locals.lookup (ofString "a") = some (.val (.word
      (if isCreate2 then 12000#64 + 6#64 * w + 2#64 * w else 12000#64 + 2#64 * w))) ∧
    s.locals.lookup (ofString "b") = some (.val (.word memoryCost))

theorem epsA_create_add_sat_positive_g10 (isCreate2 : Bool) :
    EvmPreservingSpecA (CreateCostArgs_g10 isCreate2)
      (fun s v post => LocFrame s post ∧ ∃ cost : BitVec 64, v = .val (.word cost) ∧ 0 < cost.toNat)
      (ofString "add_sat") := by
  apply epsA_refine_return_g10 lookup_add_sat epsA_add_sat (fun _ _ => trivial)
  intro F s v post hc hp hq hr
  obtain ⟨w, mc, hw, ha, hb⟩ := hp
  exact ⟨hq, create_add_sat_return_positive_g10 s w mc hw isCreate2 ha hb v hr⟩

theorem create_decCall_charge_then_child_g10 {F : Type}
    (s0 : PanSemStateFiniteExact 64 F) (P : PanSemStateFiniteExact 64 F → Prop)
    (isCreate2 charged : Bool) (name : MlS) (args : List (ExpHOL 64)) (cont : ProgHOL 64)
    (hentry : ∀ t values body callee rs,
      t.code = originalRuntimeCode → EvmInv t → Group10.HeadMemChainWF t → P t →
      evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) args = some values →
      lookupCodeHOLFinite t.code.lookup (ofString "add_sat") values = some (body, callee, rs) →
      CreateCostArgs_g10 isCreate2 (callEntryStateHOLFinite t callee))
    (hchild : ChildContinuationA (F := F) (PositiveCostLocal_g10 name) cont) :
    HandlerRunA s0 P charged
      (.decCall name .one (ofString "add_sat") args
        (.seq (.call (some (none, none)) (ofString "charge_gas") [.var .local name]) cont)) := by
  apply HandlerRunA.decCall (epsA_create_add_sat_positive_g10 isCreate2) hentry
    (Q := PositiveCostLocal_g10 name)
  · intro t values body callee rs v post hi hw hp ha hl hpi hpw hch hq
    obtain ⟨cost, rfl, hpos⟩ := hq.2
    exact bound_cost_local_positive_g10 _ name cost hpos
  · exact charge_positive_local_then_child_g10 s0 name cont charged hchild

def CreateBaseExp_g10 (isCreate2 : Bool) : ExpHOL 64 :=
  if isCreate2 then
    .op .add [.const 12000, .panop .mul [.const 6, .var .local (ofString "w")],
      .panop .mul [.const 2, .var .local (ofString "w")]]
  else .op .add [.const 12000, .panop .mul [.const 2, .var .local (ofString "w")]]

def BoundedWordsLocal_g10 {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ w : BitVec 64, s.locals.lookup (ofString "w") = some (.val (.word w)) ∧ w.toNat < 2 ^ 59

theorem create_base_exp_eval_g10 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (isCreate2 : Bool) (w : BitVec 64)
    (hw : s.locals.lookup (ofString "w") = some (.val (.word w))) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (CreateBaseExp_g10 isCreate2) = some (.val (.word
        (if isCreate2 then 12000#64 + 6#64 * w + 2#64 * w else 12000#64 + 2#64 * w))) := by
  cases isCreate2 <;>
    simp [CreateBaseExp_g10, evalHOLExact, evalListHOLExact, hw, panOpHOL,
      wordOpHOL, wordOp, valueIsWord, valueWord, BitVec.add_assoc]

theorem create_cost_callee_args_g10 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hc : s.code = originalRuntimeCode)
    (isCreate2 : Bool) (hp : BoundedWordsLocal_g10 s) (memoryExp : ExpHOL 64)
    {values : List (ValueHOL 64)} {body : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {rs : ShapeHOL}
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [CreateBaseExp_g10 isCreate2, memoryExp] = some values)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "add_sat") values = some (body, callee, rs)) :
    CreateCostArgs_g10 isCreate2 (callEntryStateHOLFinite s callee) := by
  rw [hc] at hl
  obtain ⟨_, _, aw, bw, rfl, hca, hcb⟩ := two_word_arg_lookup (by decide) lookup_add_sat hl
  obtain ⟨w, hw, hb⟩ := hp
  rw [evalListHOLFinite_eq_toExact] at ha
  simp only [evalListHOLExact, create_base_exp_eval_g10 s isCreate2 w hw] at ha
  cases he : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) memoryExp with
  | none => simp [he] at ha
  | some mv =>
    simp only [he] at ha
    have heq : (if isCreate2 then 12000#64 + 6#64 * w + 2#64 * w else 12000#64 + 2#64 * w) = aw := by
      simpa using congrArg List.head? (Option.some.inj ha)
    exact ⟨w, bw, hb, by simpa [heq, callEntryStateHOLFinite] using hca, hcb⟩

theorem create_cost_sequence_g10 {F : Type}
    (s0 : PanSemStateFiniteExact 64 F) (isCreate2 charged : Bool)
    (memoryExp : ExpHOL 64) (cont : ProgHOL 64)
    (hchild : ChildContinuationA (F := F) (PositiveCostLocal_g10 (ofString "cost")) cont) :
    HandlerRunA s0 BoundedWordsLocal_g10 charged
      (.decCall (ofString "cost") .one (ofString "add_sat")
        [CreateBaseExp_g10 isCreate2, memoryExp]
        (.seq (.call (some (none, none)) (ofString "charge_gas") [.var .local (ofString "cost")]) cont)) := by
  apply create_decCall_charge_then_child_g10 s0 BoundedWordsLocal_g10 isCreate2 charged
    (ofString "cost") _ cont ?_ hchild
  intro t values body callee rs hc hi hw hp ha hl
  exact create_cost_callee_args_g10 t hc isCreate2 hp memoryExp ha hl

theorem words_of_create_cost_sequence_g10 {F : Type}
    (s0 : PanSemStateFiniteExact 64 F) (isCreate2 charged : Bool)
    (sizeExp memoryExp : ExpHOL 64) (cont : ProgHOL 64)
    (hchild : ChildContinuationA (F := F) (PositiveCostLocal_g10 (ofString "cost")) cont) :
    HandlerRunA s0 (fun _ => True) charged
      (.decCall (ofString "w") .one (ofString "words_of") [sizeExp]
        (.decCall (ofString "cost") .one (ofString "add_sat")
          [CreateBaseExp_g10 isCreate2, memoryExp]
          (.seq (.call (some (none, none)) (ofString "charge_gas") [.var .local (ofString "cost")]) cont))) := by
  apply HandlerRunA.decCall epsA_words_of_bounded_g10 (Q := BoundedWordsLocal_g10)
  · intro t values body callee rs hc hi hw hp ha hl
    rw [hc] at hl
    rw [evalListHOLFinite_eq_toExact] at ha
    simp only [evalListHOLExact] at ha
    cases he : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) sizeExp with
    | none => simp [he] at ha
    | some v =>
      simp only [he] at ha
      have hv : values = [v] := (Option.some.inj ha).symm
      subst values
      obtain ⟨_, _, n, _, hn⟩ := one_word_arg_lookup lookup_words_of hl
      exact ⟨n, hn⟩
  · intro t values body callee rs v post hi hw hp ha hl hpi hpw hch hq
    obtain ⟨w, rfl, hb⟩ := hq.2
    exact ⟨w, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE], hb⟩
  · exact create_cost_sequence_g10 s0 isCreate2 charged memoryExp cont hchild

/-- Strip a fixed, syntactically checked handler prefix to name its continuation. -/
def handlerSuffix_g10 : Nat → ProgHOL 64 → ProgHOL 64
  | 0, p => p
  | n + 1, .seq _ p => handlerSuffix_g10 n p
  | n + 1, .decCall _ _ _ _ p => handlerSuffix_g10 n p
  | n + 1, .dec _ _ _ p => handlerSuffix_g10 n p
  | _, p => p

def createChargedSuffix_g10 : ProgHOL 64 :=
  handlerSuffix_g10 9 (sourceFnBody Guest.Software.guestFn_op_create)

def create2ChargedSuffix_g10 : ProgHOL 64 :=
  handlerSuffix_g10 10 (sourceFnBody Guest.Software.guestFn_op_create2)

theorem create_prefix_run_g10 {F : Type} (s0 : PanSemStateFiniteExact 64 F)
    (hchild : ChildContinuationA (F := F) (PositiveCostLocal_g10 (ofString "cost")) createChargedSuffix_g10) :
    HandlerRunA s0 (fun _ => True) false (sourceFnBody Guest.Software.guestFn_op_create) := by
  apply HandlerRunA.seq_call_simple epsA_require_not_static
  apply HandlerRunA.decCall_simple epsA_stack_pop
  apply HandlerRunA.decCall_simple epsA_stack_pop
  apply HandlerRunA.decCall_simple epsA_stack_pop
  apply HandlerRunA.decCall_simple epsA_sat_word
  apply HandlerRunA.decCall_simple epsA_extend_memory_cost1
  exact words_of_create_cost_sequence_g10 s0 false false
    (.var .local (ofString "n")) (.rfield 0 (.var .local (ofString "x")))
    createChargedSuffix_g10 hchild

theorem create2_prefix_run_g10 {F : Type} (s0 : PanSemStateFiniteExact 64 F)
    (hchild : ChildContinuationA (F := F) (PositiveCostLocal_g10 (ofString "cost")) create2ChargedSuffix_g10) :
    HandlerRunA s0 (fun _ => True) false (sourceFnBody Guest.Software.guestFn_op_create2) := by
  apply HandlerRunA.seq_call_simple epsA_require_not_static
  apply HandlerRunA.decCall_simple epsA_stack_pop
  apply HandlerRunA.decCall_simple epsA_stack_pop
  apply HandlerRunA.decCall_simple epsA_stack_pop
  apply HandlerRunA.decCall_simple epsA_stack_pop
  apply HandlerRunA.decCall_simple epsA_sat_word
  apply HandlerRunA.decCall_simple epsA_extend_memory_cost1
  exact words_of_create_cost_sequence_g10 s0 true false
    (.var .local (ofString "n")) (.rfield 0 (.var .local (ofString "x")))
    create2ChargedSuffix_g10 hchild

def MemoryExpansionLocal_g10 {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ cw ebw : BitVec 64,
    s.locals.lookup (ofString "x") = some (.rStruct [.val (.word cw), .val (.word ebw)]) ∧
    (ebw = 0#64 ∨ (memW s (globN s "ev" + 32) + ebw.toNat < 2 ^ 37 ∧
      (memW s (globN s "ev" + 32) + ebw.toNat) % 32 = 0))

theorem memoryExpansionLocal_transport_g10 {F : Type}
    {s t : PanSemStateFiniteExact 64 F} (hp : MemoryExpansionLocal_g10 s)
    (hx : t.locals.lookup (ofString "x") = s.locals.lookup (ofString "x"))
    (he : globN t "ev" = globN s "ev")
    (hm : memW t (globN s "ev" + 32) = memW s (globN s "ev" + 32)) :
    MemoryExpansionLocal_g10 t := by
  obtain ⟨cw, ebw, hl, hb⟩ := hp
  exact ⟨cw, ebw, hx.trans hl, by rwa [he, hm]⟩

theorem memoryExpansionLocal_bind_ro_g10 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} (hp : MemoryExpansionLocal_g10 s)
    (hlf : LocFrame s post) (name : MlS) (v : ValueHOL 64)
    (hne : name ≠ ofString "x") :
    MemoryExpansionLocal_g10 (setVarHOLFinite name v {post with locals := s.locals}) := by
  apply memoryExpansionLocal_transport_g10 hp
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne]
  · change globN post "ev" = globN s "ev"
    unfold globN
    rw [congrArg PanSemStateFiniteExact.globals hlf]
  · change memW post _ = memW s _
    unfold memW
    rw [congrArg PanSemStateFiniteExact.memory hlf]

theorem memoryExpansionLocal_callee_pre_g10 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hc : s.code = originalRuntimeCode)
    (hw : Group10.HeadMemChainWF s) (hp : MemoryExpansionLocal_g10 s)
    {values : List (ValueHOL 64)} {body : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {rs : ShapeHOL}
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.rfield 1 (.var .local (ofString "x"))] = some values)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "extend_memory") values = some (body, callee, rs)) :
    Group10.ExtendMemoryPre (callEntryStateHOLFinite s callee) := by
  obtain ⟨cw, ebw, hx, hb⟩ := hp
  have ha' : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.rfield 1 (.var .local (ofString "x"))] = some [.val (.word ebw)] := by
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact, evalHOLExact, hx]
  rw [ha'] at ha
  have hv := Option.some.inj ha
  subst values
  rw [hc] at hl
  obtain ⟨_, _, ebw', heq, hcal⟩ := one_word_arg_lookup Group10.lookup_extend_memory hl
  cases heq
  refine ⟨ebw, hcal, ?_⟩
  rcases hb with hz | hb
  · exact Or.inl hz
  · exact Or.inr ⟨hb.1, hb.2, hw.2.1⟩

theorem extend_memory_sequence_g10 {F : Type} (s0 : PanSemStateFiniteExact 64 F)
    (charged : Bool) (cont : ProgHOL 64)
    (hcont : HandlerRunA s0 (fun _ => True) charged cont) :
    HandlerRunA s0 MemoryExpansionLocal_g10 charged
      (.seq (.call (some (none, none)) (ofString "extend_memory")
        [.rfield 1 (.var .local (ofString "x"))]) cont) := by
  apply HandlerRunA.seq_call epsA_extend_memory (Q := fun _ => True)
  · intro t values body callee rs hc hi hw hp ha hl
    exact memoryExpansionLocal_callee_pre_g10 t hc hw hp ha hl
  · intros; trivial
  · exact hcont

theorem charge_gas_call_keep32_g10 {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (hc : s.code = originalRuntimeCode) (hi : EvmInv s) (hw : Group10.HeadMemChainWF s)
    (amt : ExpHOL 64)
    (hr : evaluateHOLFiniteState s (.call (some (none, none)) (ofString "charge_gas") [amt]) = (none, post)) :
    post.locals = s.locals ∧ post.globals = s.globals ∧
      memW post (globN s "ev" + 32) = memW s (globN s "ev" + 32) := by
  obtain ⟨values, body, callee, rs, v, cp, ha, hl, hrun, rfl⟩ := call0_returned_inv_g10 hr
  obtain ⟨params, body0, rs0, hl0, hs⟩ := epsA_charge_gas_keep32
  have hb : body = body0 := lookupCodeHOLFinite_installed_body s.code.lookup
    (ofString "charge_gas") params body0 body rs0 rs values callee (by rwa [hc]) hl
  subst body
  have hrs : rs = rs0 := by
    have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some s.code.lookup
      (ofString "charge_gas") values body0 callee rs hl
    rw [hc] at hx
    simp only [Flapjack.lookupCodeHOLExact, hl0] at hx
    split at hx
    · exact (congrArg (fun x => x.2.2) (Option.some.inj hx)).symm
    · cases hx
  subst rs
  have hp := hs (callEntryStateHOLFinite s callee) hc
    (localsFree_evmInv s callee (s.clock - 1) hi)
    (Group10.headMemChainWF_locals s callee (s.clock - 1) hw)
    trivial ⟨values, by rwa [← hc]⟩
  dsimp only at hp
  rw [hrun] at hp
  have hkeep := ((hp (by simp)).1 v rfl).2.2.2
  exact ⟨rfl, hkeep.1, hkeep.2⟩

theorem memoryExpansionLocal_charge_gas_g10 {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (hc : s.code = originalRuntimeCode) (hi : EvmInv s) (hw : Group10.HeadMemChainWF s)
    (hp : MemoryExpansionLocal_g10 s) (amt : ExpHOL 64)
    (hr : evaluateHOLFiniteState s (.call (some (none, none)) (ofString "charge_gas") [amt]) = (none, post)) :
    MemoryExpansionLocal_g10 post := by
  obtain ⟨hl, hg, hm⟩ := charge_gas_call_keep32_g10 hc hi hw amt hr
  apply memoryExpansionLocal_transport_g10 hp
  · rw [hl]
  · unfold globN; rw [hg]
  · exact hm

theorem charge_positive_local_call_decreases_g10 {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (hc : s.code = originalRuntimeCode) (hi : EvmInv s) (hw : Group10.HeadMemChainWF s)
    (name : MlS) (hp : PositiveCostLocal_g10 name s)
    (hr : evaluateHOLFiniteState s (.call (some (none, none)) (ofString "charge_gas")
      [.var .local name]) = (none, post)) :
    EvmInv post ∧ Group10.HeadMemChainWF post ∧ evmChain post = evmChain s ∧ OpDispatchSpec.evmR post < OpDispatchSpec.evmR s := by
  obtain ⟨values, body, callee, rs, v, cp, ha, hl, hrun, rfl⟩ := call0_returned_inv_g10 hr
  obtain ⟨w, hlw, hpos⟩ := hp
  have ha' : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local name] = some [.val (.word w)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hlw]
  rw [ha'] at ha
  have hv := Option.some.inj ha
  subst values
  rw [hc] at hl
  obtain ⟨rfl, rfl, w', heq, hcal⟩ := one_word_arg_lookup M21.lookup_charge_gas hl
  cases heq
  have h := charge_gas_body_exactA (callEntryStateHOLFinite s callee)
    (localsFree_evmInv s callee (s.clock - 1) hi)
    (Group10.headMemChainWF_locals s callee (s.clock - 1) hw) hcal
  dsimp only at h
  rw [hrun] at h
  obtain ⟨⟨hip, hwp⟩, hg, hch, hR⟩ := h.1 v rfl
  refine ⟨localsFree_evmInv cp s.locals cp.clock hip,
    Group10.headMemChainWF_locals cp s.locals cp.clock hwp, ?_, ?_⟩
  · have h1 : evmChain {cp with locals := s.locals} = evmChain cp := evmChain_congr rfl rfl
    have h2 : evmChain (callEntryStateHOLFinite s callee) = evmChain s := evmChain_congr rfl rfl
    exact h1.trans (hch.trans h2)
  · rw [(evm_congr (s := cp) (t := {cp with locals := s.locals}) rfl rfl).2.1]
    have hce : OpDispatchSpec.evmR (callEntryStateHOLFinite s callee) = OpDispatchSpec.evmR s :=
      (evm_congr (s := s) (t := callEntryStateHOLFinite s callee) rfl rfl).2.1
    dsimp only at hR
    rw [hce] at hR
    omega

theorem charge_positive_local_memory_sequence_g10 {F : Type}
    (s0 : PanSemStateFiniteExact 64 F) (name : MlS) (charged : Bool) (cont : ProgHOL 64)
    (hcont : HandlerRunA s0
      (fun s => PositiveCostLocal_g10 name s ∧ MemoryExpansionLocal_g10 s) true cont) :
    HandlerRunA s0 (fun s => PositiveCostLocal_g10 name s ∧ MemoryExpansionLocal_g10 s) charged
      (.seq (.call (some (none, none)) (ofString "charge_gas") [.var .local name]) cont) := by
  intro t hc hi hw hlen hR hp hnt
  let call : ProgHOL 64 := .call (some (none, none)) (ofString "charge_gas") [.var .local name]
  have hfallback : HandlerRunA s0 (PositiveCostLocal_g10 name) charged
      (.seq call (.return (.const 0))) := by
    apply HandlerRunA.seq_charge_gas (Q := fun _ => True)
    · intro u w he hui huw hup
      obtain ⟨w', hl, hpos⟩ := hup
      change u.locals.lookup name = some (.val (.word w)) at he
      rw [hl] at he
      cases he
      exact hpos
    · intros; trivial
    · exact HandlerRunA.ret _
  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
  rcases hr : evaluateHOLFiniteState t call with ⟨r, post⟩
  simp only [call] at hr
  rw [hr] at hnt
  cases r with
  | none =>
    obtain ⟨hip, hwp, hch, hlt⟩ := charge_positive_local_call_decreases_g10 hc hi hw name hp.1 hr
    have hmem := memoryExpansionLocal_charge_gas_g10 hc hi hw hp.2 (.var .local name) hr
    obtain ⟨hl, _, _⟩ := charge_gas_call_keep32_g10 hc hi hw (.var .local name) hr
    have hpos : PositiveCostLocal_g10 name post := by
      obtain ⟨w, hlookup, hpos⟩ := hp.1
      exact ⟨w, by rwa [hl], hpos⟩
    have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata t call).1
    rw [hr] at hmeta
    apply hcont post (hmeta.trans hc) hip hwp (by rw [hch]; exact hlen) ?_ ⟨hpos, hmem⟩ hnt
    cases charged <;> simp only [Bool.false_eq_true, ↓reduceIte] at hR ⊢ <;> omega
  | some r =>
    have hf := hfallback t hc hi hw hlen hR hp.1
    rw [evaluateHOLFiniteState_seq_line780, hr] at hf
    exact hf hnt

theorem create_cost_memory_sequence_g10 {F : Type}
    (s0 : PanSemStateFiniteExact 64 F) (isCreate2 charged : Bool)
    (memoryExp : ExpHOL 64) (cont : ProgHOL 64)
    (hcont : HandlerRunA s0
      (fun s => PositiveCostLocal_g10 (ofString "cost") s ∧ MemoryExpansionLocal_g10 s) true cont) :
    HandlerRunA s0 (fun s => BoundedWordsLocal_g10 s ∧ MemoryExpansionLocal_g10 s) charged
      (.decCall (ofString "cost") .one (ofString "add_sat")
        [CreateBaseExp_g10 isCreate2, memoryExp]
        (.seq (.call (some (none, none)) (ofString "charge_gas") [.var .local (ofString "cost")]) cont)) := by
  apply HandlerRunA.decCall (epsA_create_add_sat_positive_g10 isCreate2)
    (Q := fun s => PositiveCostLocal_g10 (ofString "cost") s ∧ MemoryExpansionLocal_g10 s)
  · intro t values body callee rs hc hi hw hp ha hl
    exact create_cost_callee_args_g10 t hc isCreate2 hp.1 memoryExp ha hl
  · intro t values body callee rs v post hi hw hp ha hl hpi hpw hch hq
    obtain ⟨cost, rfl, hpos⟩ := hq.2
    refine ⟨bound_cost_local_positive_g10 _ _ cost hpos, ?_⟩
    have hlf : LocFrame t post := by
      rw [hq.1]
      rfl
    exact memoryExpansionLocal_bind_ro_g10 hp.2 hlf _ _ (by decide)
  · exact charge_positive_local_memory_sequence_g10 s0 (ofString "cost") charged cont hcont

theorem words_of_create_memory_sequence_g10 {F : Type}
    (s0 : PanSemStateFiniteExact 64 F) (isCreate2 charged : Bool)
    (sizeExp memoryExp : ExpHOL 64) (cont : ProgHOL 64)
    (hcont : HandlerRunA s0
      (fun s => PositiveCostLocal_g10 (ofString "cost") s ∧ MemoryExpansionLocal_g10 s) true cont) :
    HandlerRunA s0 MemoryExpansionLocal_g10 charged
      (.decCall (ofString "w") .one (ofString "words_of") [sizeExp]
        (.decCall (ofString "cost") .one (ofString "add_sat")
          [CreateBaseExp_g10 isCreate2, memoryExp]
          (.seq (.call (some (none, none)) (ofString "charge_gas") [.var .local (ofString "cost")]) cont))) := by
  apply HandlerRunA.decCall epsA_words_of_bounded_g10
    (Q := fun s => BoundedWordsLocal_g10 s ∧ MemoryExpansionLocal_g10 s)
  · intro t values body callee rs hc hi hw hp ha hl
    rw [hc] at hl
    rw [evalListHOLFinite_eq_toExact] at ha
    simp only [evalListHOLExact] at ha
    cases he : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) sizeExp with
    | none => simp [he] at ha
    | some v =>
      simp only [he] at ha
      have hv : values = [v] := (Option.some.inj ha).symm
      subst values
      obtain ⟨_, _, n, _, hn⟩ := one_word_arg_lookup lookup_words_of hl
      exact ⟨n, hn⟩
  · intro t values body callee rs v post hi hw hp ha hl hpi hpw hch hq
    obtain ⟨w, rfl, hb⟩ := hq.2
    refine ⟨⟨w, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE], hb⟩, ?_⟩
    have hlf : LocFrame t post := by
      rw [hq.1]
      rfl
    exact memoryExpansionLocal_bind_ro_g10 hp hlf _ _ (by decide)
  · exact create_cost_memory_sequence_g10 s0 isCreate2 charged memoryExp cont hcont

theorem extend_memory_cost1_bind_sequence_g10 {F : Type}
    (s0 : PanSemStateFiniteExact 64 F) (charged : Bool)
    (args : List (ExpHOL 64)) (cont : ProgHOL 64)
    (hcont : HandlerRunA s0 MemoryExpansionLocal_g10 charged cont) :
    HandlerRunA s0 (fun _ => True) charged
      (.decCall (ofString "x") (.comb [.one, .one]) (ofString "extend_memory_cost1") args cont) := by
  apply HandlerRunA.decCall epsA_extend_memory_cost1_aligned (Q := MemoryExpansionLocal_g10)
  · intros; trivial
  · intro t values body callee rs v post hi hw hp ha hl hpi hpw hch hq
    obtain ⟨hlf, cw, ebw, rfl, hb⟩ := hq
    refine ⟨cw, ebw, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE], ?_⟩
    have hg : post.globals = t.globals := by rw [hlf]; rfl
    have hm : post.memory = t.memory := by rw [hlf]; rfl
    change ebw = 0#64 ∨ (memW post (globN post "ev" + 32) + ebw.toNat < 2 ^ 37 ∧
      (memW post (globN post "ev" + 32) + ebw.toNat) % 32 = 0)
    change ebw = 0#64 ∨ (memW t (globN t "ev" + 32) + ebw.toNat < 2 ^ 37 ∧
      (memW t (globN t "ev" + 32) + ebw.toNat) % 32 = 0) at hb
    simpa only [memW, globN, hg, hm] using hb
  · exact hcont

theorem create_prefix_memory_run_g10 {F : Type} (s0 : PanSemStateFiniteExact 64 F)
    (hcont : HandlerRunA s0
      (fun s => PositiveCostLocal_g10 (ofString "cost") s ∧ MemoryExpansionLocal_g10 s)
      true createChargedSuffix_g10) :
    HandlerRunA s0 (fun _ => True) false (sourceFnBody Guest.Software.guestFn_op_create) := by
  apply HandlerRunA.seq_call_simple epsA_require_not_static
  apply HandlerRunA.decCall_simple epsA_stack_pop
  apply HandlerRunA.decCall_simple epsA_stack_pop
  apply HandlerRunA.decCall_simple epsA_stack_pop
  apply HandlerRunA.decCall_simple epsA_sat_word
  apply extend_memory_cost1_bind_sequence_g10
  exact words_of_create_memory_sequence_g10 s0 false false _ _ _ hcont

theorem create2_prefix_memory_run_g10 {F : Type} (s0 : PanSemStateFiniteExact 64 F)
    (hcont : HandlerRunA s0
      (fun s => PositiveCostLocal_g10 (ofString "cost") s ∧ MemoryExpansionLocal_g10 s)
      true create2ChargedSuffix_g10) :
    HandlerRunA s0 (fun _ => True) false (sourceFnBody Guest.Software.guestFn_op_create2) := by
  apply HandlerRunA.seq_call_simple epsA_require_not_static
  apply HandlerRunA.decCall_simple epsA_stack_pop
  apply HandlerRunA.decCall_simple epsA_stack_pop
  apply HandlerRunA.decCall_simple epsA_stack_pop
  apply HandlerRunA.decCall_simple epsA_stack_pop
  apply HandlerRunA.decCall_simple epsA_sat_word
  apply extend_memory_cost1_bind_sequence_g10
  exact words_of_create_memory_sequence_g10 s0 true false _ _ _ hcont

theorem create_prefix_through_extend_g10 {F : Type} (s0 : PanSemStateFiniteExact 64 F)
    (hcont : HandlerRunA s0 (fun _ => True) true (handlerSuffix_g10 1 createChargedSuffix_g10)) :
    HandlerRunA s0 (fun _ => True) false (sourceFnBody Guest.Software.guestFn_op_create) := by
  apply create_prefix_memory_run_g10
  apply HandlerRunA.weaken (Q := MemoryExpansionLocal_g10)
  · intro t hi hp; exact hp.2
  · exact extend_memory_sequence_g10 s0 true _ hcont

theorem memoryExpansionLocal_heap_update_g10 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (q : BitVec 64)
    (hp : MemoryExpansionLocal_g10 s) :
    MemoryExpansionLocal_g10 {s with globals := s.globals.update (ofString "heap_ptr", .val (.word q))} := by
  apply memoryExpansionLocal_transport_g10 hp rfl
  · simp [globN, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "heap_ptr" ≠ ofString "ev" by decide]
  · rfl

theorem alloc_return_frame_g10 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (p n : BitVec 64)
    (hc : s.code = originalRuntimeCode)
    (hple : p.toNat ≤ InitECandidate.Solver.HeapPotential.cMax.toNat)
    (hp : s.globals.lookup (ofString "heap_ptr") = some (.val (.word p)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hr : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_alloc) = (some (.returned v), post)) :
    v = .val (.word p) ∧ post.memory = s.memory ∧
      post.globals = s.globals.update (ofString "heap_ptr", .val (.word ((p + (n + 7)) &&& (0 - 8)))) := by
  have h := M13.evaluate_alloc_body_general s p n hc hple hp hn v
  rw [hr] at h
  obtain ⟨hv, hg, hm, _⟩ := h rfl
  exact ⟨hv, hm, hg⟩

theorem memoryExpansionLocal_alloc_binding_g10 {F : Type}
    (caller : PanSemStateFiniteExact 64 F) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (p n : BitVec 64) (hc : caller.code = originalRuntimeCode)
    (hple : p.toNat ≤ InitECandidate.Solver.HeapPotential.cMax.toNat)
    (hp : caller.globals.lookup (ofString "heap_ptr") = some (.val (.word p)))
    (hn : callee.lookup (ofString "n") = some (.val (.word n)))
    (hexpand : MemoryExpansionLocal_g10 caller) (name : MlS) (hne : name ≠ ofString "x")
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hr : evaluateHOLFiniteState (callEntryStateHOLFinite caller callee)
      (sourceFnBody Guest.Software.guestFn_alloc) = (some (.returned v), post)) :
    MemoryExpansionLocal_g10 (setVarHOLFinite name v {post with locals := caller.locals}) := by
  obtain ⟨_, hm, hg⟩ := alloc_return_frame_g10 (callEntryStateHOLFinite caller callee) p n hc hple hp hn v post hr
  apply memoryExpansionLocal_transport_g10 hexpand
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne]
  · change globN post "ev" = globN caller "ev"
    simp [globN, hg, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "heap_ptr" ≠ ofString "ev" by decide]
  · change memW post _ = memW caller _
    unfold memW
    rw [hm]
    rfl

theorem aligned_heap_growth_g10 {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (hi : EvmInv s) (hw : Group10.HeadMemChainWF s)
    (ha : ArenaReady post) (hbe : post.be = s.be)
    (hh : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hg : GlobalsKept ["heap_ptr"] s post) (hm : post.memory = s.memory) :
    EvmInv post ∧ Group10.HeadMemChainWF post ∧ evmChain post = evmChain s ∧
      OpDispatchSpec.evmR post = OpDispatchSpec.evmR s := by
  obtain ⟨has, S, hiS⟩ := hi
  obtain ⟨hip, hch, hR⟩ := evmInvAt_of_fresh_heap_step has hiS ha hbe hh hg
    (by intro a hn; rw [hm])
    (by intro b hb hn; unfold memB; rw [hm, hbe])
  have hev : globN post "ev" = globN s "ev" := by
    unfold globN
    rw [← hg (ofString "ev") (by decide)]
  have hfmp : globN post "frame_mem_ptr" = globN s "frame_mem_ptr" := by
    unfold globN
    rw [← hg (ofString "frame_mem_ptr") (by decide)]
  refine ⟨⟨ha, S, hip⟩, ?_, hch, hR⟩
  apply Group10.headMemChainWF_of_agree hw hch ?_ hev hfmp
  intro ec hec
  simp only [memW, hm]
  trivial

theorem aligned_heap_update_g10 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (q : BitVec 64)
    (hi : EvmInv s) (hw : Group10.HeadMemChainWF s)
    (hlo : globN s "heap_ptr" ≤ q.toNat)
    (hhi : q.toNat ≤ InitECandidate.Solver.HeapPotential.cMax.toNat)
    (hal : q.toNat % 8 = 0) :
    let post := {s with globals := s.globals.update (ofString "heap_ptr", .val (.word q))}
    EvmInv post ∧ Group10.HeadMemChainWF post ∧ evmChain post = evmChain s ∧
      OpDispatchSpec.evmR post = OpDispatchSpec.evmR s := by
  let post := {s with globals := s.globals.update (ofString "heap_ptr", .val (.word q))}
  have hq : globN post "heap_ptr" = q.toNat := by simp [post, globN, FUPDATE]
  have hfp : globN post "frame_mem_ptr" = globN s "frame_mem_ptr" := by
    simp [post, globN, FUPDATE, show ofString "heap_ptr" ≠ ofString "frame_mem_ptr" by decide]
  have hsp : globN post "scratch_ptr" = globN s "scratch_ptr" := by
    simp [post, globN, FUPDATE, show ofString "heap_ptr" ≠ ofString "scratch_ptr" by decide]
  have ha : ArenaReady post := by
    refine ⟨guestInv_congr (s := s) rfl rfl rfl rfl hi.1.1, ?_⟩
    obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9⟩ := hi.1.2
    unfold ArenaOK
    rw [hq, hfp, hsp]
    exact ⟨le_trans h1 hlo, hhi, h3, h4, h5, hal, h7, h8,
      globalsWord_update (ofString "heap_ptr") q rfl h9⟩
  have hg : GlobalsKept ["heap_ptr"] s post := by
    intro k hk
    have hne : ofString "heap_ptr" ≠ k := by intro he; subst k; exact hk (by simp)
    simp [post, HolFiniteMapExact.lookup_update, FUPDATE, hne]
  exact aligned_heap_growth_g10 hi hw ha rfl (by rw [hq]; exact hlo) hg rfl

theorem alloc_return_aligned_heap_g10 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (p n : BitVec 64)
    (hi : EvmInv s) (hw : Group10.HeadMemChainWF s)
    (hc : s.code = originalRuntimeCode)
    (hp : s.globals.lookup (ofString "heap_ptr") = some (.val (.word p)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hr : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_alloc) = (some (.returned v), post)) :
    let updated := {s with globals := post.globals}
    EvmInv updated ∧ Group10.HeadMemChainWF updated ∧ evmChain updated = evmChain s ∧
      OpDispatchSpec.evmR updated = OpDispatchSpec.evmR s := by
  have hpn : globN s "heap_ptr" = p.toNat := by unfold globN; rw [hp]
  have hple : p.toNat ≤ InitECandidate.Solver.HeapPotential.cMax.toNat := by
    rw [← hpn]; exact hi.1.2.2.1
  have h := M13.evaluate_alloc_body_general s p n hc hple hp hn v
  rw [hr] at h
  obtain ⟨_, hg, _, hlo, hhi, hal⟩ := h rfl
  dsimp only
  rw [hg]
  apply aligned_heap_update_g10 s _ hi hw ?_ hhi hal
  rw [hpn]
  omega

theorem alloc_return_aligned_g10 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (p n : BitVec 64)
    (hi : EvmInv s) (hw : Group10.HeadMemChainWF s)
    (hc : s.code = originalRuntimeCode)
    (hp : s.globals.lookup (ofString "heap_ptr") = some (.val (.word p)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hr : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_alloc) = (some (.returned v), post)) :
    EvmInv post ∧ Group10.HeadMemChainWF post ∧ evmChain post = evmChain s ∧
      OpDispatchSpec.evmR post = OpDispatchSpec.evmR s := by
  have hpn : globN s "heap_ptr" = p.toNat := by unfold globN; rw [hp]
  have hple : p.toNat ≤ InitECandidate.Solver.HeapPotential.cMax.toNat := by
    rw [← hpn]; exact hi.1.2.2.1
  have h := M13.evaluate_alloc_body_general s p n hc hple hp hn v
  rw [hr] at h
  obtain ⟨_, hg, hm, hlo, _, _⟩ := h rfl
  have hiu := (alloc_return_aligned_heap_g10 s p n hi hw hc hp hn v post hr).1
  have hGp := guestInv_evaluate s (sourceFnBody Guest.Software.guestFn_alloc) hi.1.1
  rw [hr] at hGp
  have ha : ArenaReady post := ⟨hGp, arenaOK_congr rfl hiu.1.2⟩
  have hbe := R16Shards.evaluate_be_eq s (sourceFnBody Guest.Software.guestFn_alloc)
  rw [hr] at hbe
  apply aligned_heap_growth_g10 hi hw ha hbe ?_ ?_ hm
  · unfold globN
    rw [hg, hp]
    simp only [HolFiniteMapExact.lookup_update, FUPDATE, beq_self_eq_true, ite_true]
    omega
  · intro k hk
    have hne : ofString "heap_ptr" ≠ k := by intro he; subst k; exact hk (by simp)
    rw [hg]
    simp [HolFiniteMapExact.lookup_update, FUPDATE, hne]

theorem epsA_alloc_g10 :
    EvmPreservingSpecA (fun _ => True)
      (fun s v post => post.memory = s.memory ∧
        ∃ p : BitVec 64, v = .val (.word p) ∧ p.toNat = globN s "heap_ptr")
      (ofString "alloc") := by
  refine ⟨_, _, _, GuestTrapAndLookup.lookup_alloc, ?_⟩
  intro F s hc hi hw _ ⟨vals, hl⟩ _
  have hlen : ∃ v0, vals = [v0] := by
    have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
      originalRuntimeCode.lookup (ofString "alloc") vals _ _ _ hl
    simp only [Flapjack.lookupCodeHOLExact, GuestTrapAndLookup.lookup_alloc] at hx
    rcases vals with _ | ⟨v0, _ | _⟩ <;> simp at hx
    exact ⟨v0, rfl⟩
  obtain ⟨v0, rfl⟩ := hlen
  obtain ⟨_, _, n, rfl, hn⟩ := one_word_arg_lookup GuestTrapAndLookup.lookup_alloc hl
  obtain ⟨p, hp⟩ := hi.1.2.2.2.2.2.2.2.2.2 "heap_ptr" (by decide)
  change s.globals.lookup (ofString "heap_ptr") = some (.val (.word p)) at hp
  have hpn : p.toNat = globN s "heap_ptr" := by simp [globN, hp]
  have hple : p.toNat ≤ InitECandidate.Solver.HeapPotential.cMax.toNat := by
    rw [hpn]; exact hi.1.2.2.1
  dsimp only
  rcases hr : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_alloc) with ⟨r, post⟩
  refine ⟨fun v hv => ?_, fun herr => ?_⟩
  · have hrun : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_alloc) =
        (some (.returned v), post) := by rw [hr]; exact congrArg (fun r => (r, post)) hv
    obtain ⟨hip, hwp, hch, hR⟩ := alloc_return_aligned_g10 s p n hi hw hc hp hn v post hrun
    obtain ⟨hvret, hm, _⟩ := alloc_return_frame_g10 s p n hc hple hp hn v post hrun
    exact ⟨⟨hip, hwp⟩, hch, le_of_eq hR, hm, p, hvret, hpn⟩
  · have hno := OpHandlers.alloc_body_no_evmErr s hc
    rw [hr] at hno
    exact False.elim (hno herr)

theorem alloc_binding_memory_sequence_g10 {F : Type}
    (s0 : PanSemStateFiniteExact 64 F) (charged : Bool)
    (name : MlS) (hne : name ≠ ofString "x")
    (args : List (ExpHOL 64)) (cont : ProgHOL 64)
    (hcont : HandlerRunA s0 MemoryExpansionLocal_g10 charged cont) :
    HandlerRunA s0 MemoryExpansionLocal_g10 charged
      (.decCall name .one (ofString "alloc") args cont) := by
  apply HandlerRunA.decCall epsA_alloc_g10 (Q := MemoryExpansionLocal_g10)
  · intros; trivial
  · intro t values body callee rs v post hi hw hp ha hl hpi hpw hch hq
    obtain ⟨hm, p, hv, hpn⟩ := hq
    have hev : globN post "ev" = globN t "ev" := by
      have he := congrArg (fun l => l.head?.map Prod.fst) hch
      simpa [evmChain, evmChainFrom, callEntryStateHOLFinite, globN] using he
    apply memoryExpansionLocal_transport_g10 hp
    · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne]
    · exact hev
    · change memW post _ = memW t _
      unfold memW
      rw [hm]
      rfl
  · exact hcont

theorem create2_prefix_through_alloc_g10 {F : Type} (s0 : PanSemStateFiniteExact 64 F)
    (hcont : HandlerRunA s0 MemoryExpansionLocal_g10 true
      (handlerSuffix_g10 1 create2ChargedSuffix_g10)) :
    HandlerRunA s0 (fun _ => True) false (sourceFnBody Guest.Software.guestFn_op_create2) := by
  apply create2_prefix_memory_run_g10
  apply HandlerRunA.weaken (Q := MemoryExpansionLocal_g10)
  · intro t hi hp; exact hp.2
  · exact alloc_binding_memory_sequence_g10 s0 true (ofString "salt") (by decide) _ _ hcont

theorem alloc_return_buffer_bounds_g10 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (p n : BitVec 64)
    (hi : EvmInv s) (hc : s.code = originalRuntimeCode)
    (hp : s.globals.lookup (ofString "heap_ptr") = some (.val (.word p)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hr : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_alloc) = (some (.returned v), post)) :
    v = .val (.word p) ∧ p.toNat = globN s "heap_ptr" ∧ p.toNat % 8 = 0 ∧
      p.toNat + n.toNat ≤ globN post "heap_ptr" ∧
      globN post "heap_ptr" ≤ InitECandidate.Solver.HeapPotential.cMax.toNat ∧
      globN post "heap_ptr" % 8 = 0 := by
  have hpn : globN s "heap_ptr" = p.toNat := by unfold globN; rw [hp]
  have hple : p.toNat ≤ InitECandidate.Solver.HeapPotential.cMax.toNat := by
    rw [← hpn]; exact hi.1.2.2.1
  have h := M13.evaluate_alloc_body_general s p n hc hple hp hn v
  rw [hr] at h
  obtain ⟨hv, hg, _, hlo, hhi, hal⟩ := h rfl
  have hq : globN post "heap_ptr" = ((p + (n + 7)) &&& (0 - 8)).toNat := by
    unfold globN
    rw [hg]
    simp only [HolFiniteMapExact.lookup_update, FUPDATE, beq_self_eq_true, ite_true]
  refine ⟨hv, hpn.symm, ?_, hq ▸ hlo, hq ▸ hhi, hq ▸ hal⟩
  rw [← hpn]
  exact hi.1.2.2.2.2.2.2.1

theorem epsA_alloc_buffer_g10 :
    EvmPreservingSpecA (fun _ => True)
      (fun s v post => post.memory = s.memory ∧
        ∃ p : BitVec 64, v = .val (.word p) ∧ p.toNat = globN s "heap_ptr" ∧
          p.toNat % 8 = 0 ∧ p.toNat + locN s "n" ≤ globN post "heap_ptr")
      (ofString "alloc") := by
  obtain ⟨params, body, rs, hl, hs⟩ := epsA_alloc_g10
  rw [GuestTrapAndLookup.lookup_alloc] at hl
  cases hl
  refine ⟨_, _, _, GuestTrapAndLookup.lookup_alloc, ?_⟩
  intro F s hc hi hw hp hlookup hnt
  have h := hs s hc hi hw hp hlookup hnt
  refine ⟨fun v hv => ?_, h.2⟩
  obtain ⟨hiw, hch, hR, hm, p, hvp, hpn⟩ := h.1 v hv
  obtain ⟨vals, hl⟩ := hlookup
  have hlen : ∃ v0, vals = [v0] := by
    have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
      originalRuntimeCode.lookup (ofString "alloc") vals _ _ _ hl
    simp only [Flapjack.lookupCodeHOLExact, GuestTrapAndLookup.lookup_alloc] at hx
    rcases vals with _ | ⟨v0, _ | _⟩ <;> simp at hx
    exact ⟨v0, rfl⟩
  obtain ⟨v0, rfl⟩ := hlen
  obtain ⟨_, _, n, rfl, hn⟩ := one_word_arg_lookup GuestTrapAndLookup.lookup_alloc hl
  obtain ⟨p0, hp0⟩ := hi.1.2.2.2.2.2.2.2.2.2 "heap_ptr" (by decide)
  change s.globals.lookup (ofString "heap_ptr") = some (.val (.word p0)) at hp0
  have hr : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_alloc) =
      (some (.returned v), (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_alloc)).2) := by
    exact Prod.ext hv rfl
  obtain ⟨hv0, hp0n, hal, hb, _, _⟩ := alloc_return_buffer_bounds_g10 s p0 n hi hc hp0 hn v _ hr
  refine ⟨hiw, hch, hR, hm, p0, hv0, hp0n, hal, ?_⟩
  simpa only [locN, hn] using hb

def SaltBufferLocal_g10 {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ p : BitVec 64, s.locals.lookup (ofString "salt") = some (.val (.word p)) ∧
    p.toNat % 8 = 0 ∧ p.toNat + 32 ≤ globN s "heap_ptr"

theorem alloc_salt_buffer_sequence_g10 {F : Type}
    (s0 : PanSemStateFiniteExact 64 F) (charged : Bool) (cont : ProgHOL 64)
    (hcont : HandlerRunA s0 (fun s => MemoryExpansionLocal_g10 s ∧ SaltBufferLocal_g10 s) charged cont) :
    HandlerRunA s0 MemoryExpansionLocal_g10 charged
      (.decCall (ofString "salt") .one (ofString "alloc") [.const 32] cont) := by
  apply HandlerRunA.decCall epsA_alloc_buffer_g10
    (Q := fun s => MemoryExpansionLocal_g10 s ∧ SaltBufferLocal_g10 s)
  · intros; trivial
  · intro t values body callee rs v post hi hw hp ha hl hpi hpw hch hq
    have hvals : values = [.val (.word (32 : BitVec 64))] := by
      simpa [evalListHOLExact, evalHOLExact] using ha.symm
    subst values
    obtain ⟨_, _, n, hvn, hn⟩ := one_word_arg_lookup GuestTrapAndLookup.lookup_alloc hl
    have hn32 : n = (32 : BitVec 64) := by simpa using hvn.symm
    subst n
    obtain ⟨hm, p, rfl, hpn, hal, hb⟩ := hq
    have hev : globN post "ev" = globN t "ev" := by
      have he := congrArg (fun l => l.head?.map Prod.fst) hch
      simpa [evmChain, evmChainFrom, callEntryStateHOLFinite, globN] using he
    constructor
    · apply memoryExpansionLocal_transport_g10 hp
      · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "salt" ≠ ofString "x" by decide]
      · exact hev
      · change memW post _ = memW t _
        unfold memW
        rw [hm]
        rfl
    · refine ⟨p, ?_, hal, ?_⟩
      · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      · change p.toNat + 32 ≤ globN post "heap_ptr"
        simpa [locN, callEntryStateHOLFinite, hn] using hb
  · exact hcont

theorem salt_buffer_disj_headers_g10 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hi : EvmInv s) (hs : SaltBufferLocal_g10 s) :
    ∀ ec ∈ evmChain s,
      Disj (locN s "salt", 32) (ec.1, 280) ∧
      Disj (locN s "salt", 32) (ec.2, 104) := by
  obtain ⟨p, hp, _, hb⟩ := hs
  have hloc : locN s "salt" = p.toNat := by unfold locN; rw [hp]
  obtain ⟨ha, S, _, _, _, _, hfw, _⟩ := hi
  have hheap := ha.2.2.1
  have hframe := ha.2.2.2.1
  have hscratch := ha.2.2.2.2.1
  have hlim : heapLimit = scratchStart := rfl
  intro ec hec
  have hw := hfw ec hec
  have he : globN s "scratch_ptr" ≤ ec.1 := (hw.1 (ec.1, 280) (by simp)).1.1
  have hc : globN s "scratch_ptr" ≤ ec.2 := (hw.1 (ec.2, 104) (by simp)).1.1
  constructor <;> apply Or.inr ∘ Or.inr ∘ Or.inl
  · change locN s "salt" + 32 ≤ ec.1
    rw [hloc]
    omega
  · change locN s "salt" + 32 ≤ ec.2
    rw [hloc]
    omega

theorem salt_write_head_alignment_g10 {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (hi : EvmInv s) (hw : Group10.HeadMemChainWF s) (hs : SaltBufferLocal_g10 s)
    (hch : evmChain post = evmChain s)
    (heff : ByteRegionEffect s post [(locN s "salt", 32)]) :
    Group10.HeadMemChainWF post := by
  apply headMemChainWF_of_byteRegionEffect hi hw hch heff
  · intro i hi
    simp only [List.mem_singleton] at hi
    subst i
    obtain ⟨p, hp, hal, _⟩ := hs
    simpa only [locN, hp] using hal
  · intro ec hec i hi'
    simp only [List.mem_singleton] at hi'
    subst i
    obtain ⟨he, hc⟩ := salt_buffer_disj_headers_g10 s hi hs ec hec
    constructor
    · right
      unfold Disj at he ⊢
      rcases he with h | h | h | h <;> simp_all
    · right
      unfold Disj at hc ⊢
      rcases hc with h | h | h | h <;> simp_all

theorem heap_frontier_disj_allocated_g10 {F : Type}
    {s : PanSemStateFiniteExact 64 F} (ha : ArenaOK s)
    (p n : Nat) (hp : globN s "heap_ptr" ≤ p) (hb : p + n ≤ heapLimit)
    {i : Ivl} (hi : i.2 = 0 ∨ Allocated s i) : Disj (p, n) i := by
  rcases hi with hz | hh | hsc
  · exact Or.inr (Or.inl hz)
  · exact Or.inr (Or.inr (Or.inr (by have h := hh.2; dsimp; omega)))
  · have hf := ha.2.2.1
    have hs := ha.2.2.2.1
    have hlim : heapLimit = InitE.scratchStart := rfl
    exact Or.inr (Or.inr (Or.inl (by have h := hsc.1; dsimp; omega)))

theorem heap_frontier_disj_world_g10 {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (ha : ArenaOK s) (hw : WorldTypedWith s S Nd)
    (p n : Nat) (hp : globN s "heap_ptr" ≤ p) (hb : p + n ≤ heapLimit) :
    IvlsDisj [(p, n)] (worldTypedIvls s S Nd) := by
  intro j hj i hi
  simp only [List.mem_singleton] at hj
  subst j
  exact heap_frontier_disj_allocated_g10 ha p n hp hb (worldTypedIvls_allocated hw hi)

theorem heap_frontier_disj_frame_g10 {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S : List Nat} {ec : Ivl}
    (ha : ArenaOK s) (hw : FrameWF s S ec)
    (p n : Nat) (hp : globN s "heap_ptr" ≤ p) (hb : p + n ≤ heapLimit) :
    ∀ i ∈ frameObjects s ec, Disj (p, n) i := by
  have hf := ha.2.2.1
  have hs := ha.2.2.2.1
  have hlim : heapLimit = scratchStart := rfl
  have above : ∀ i : Ivl, scratchStart ≤ i.1 → Disj (p,n) i := by
    intro i hi
    exact Or.inr (Or.inr (Or.inl (by dsimp; omega)))
  have below : ∀ i : Ivl, i.1 + i.2 ≤ globN s "heap_ptr" → Disj (p,n) i := by
    intro i hi
    exact Or.inr (Or.inr (Or.inr (by dsimp; omega)))
  obtain ⟨hscr, hmem, _, _, _, _, _, _, _, _, _, _, hlogs, _, hret, hll, _⟩ := hw
  intro i hi
  unfold frameObjects at hi
  rcases List.mem_append.1 hi with hi | hi
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · apply above; have h := (hscr (ec.1,280) (by simp)).1.1; dsimp at h ⊢; omega
    · apply above; have h := (hscr (ec.2,104) (by simp)).1.1; dsimp at h ⊢; omega
    · apply above; have h := (hscr (memW s (ec.1+8),32 * memW s (ec.1+232)) (by simp)).1.1; dsimp at h ⊢; omega
    · exact above _ hmem.1
    · apply above; have h := (hscr (memW s (ec.1+88),24) (by simp)).1.1; dsimp at h ⊢; omega
    · rcases hlogs with h | h
      · exact below _ h.2
      · apply above; have hh := h.1; omega
    · rcases hret with ⟨hz,_⟩ | ⟨h,_⟩
      · exact Or.inr (Or.inl (by simp [frameRet, hz]))
      · exact below _ h.2
  · unfold frameLogObjects at hi
    obtain ⟨idx, hidx, ho⟩ := List.mem_flatMap.1 hi
    rw [List.mem_range] at hidx
    rcases hll with hz | ⟨_,_,_,_,hent⟩
    · have hlo := (hscr (memW s (ec.1+88),24) (by simp)).1.1
      have hpos : 0 < scratchStart := by decide
      dsimp at hlo
      omega
    · have hle := (hent idx hidx).2
      have hr := (List.mem_filter.1 ho).1
      simp only [logRecordIvls, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact below _ hle.2.1.2
      · exact below _ hle.2.2.2.2.1.2
      · exact below _ hle.2.2.2.2.2.1.2
      · exact below _ hle.2.2.2.2.2.2.2

theorem heap_frontier_evm_avoids_g10 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hi : EvmInv s)
    (p n : Nat) (hp : globN s "heap_ptr" ≤ p) (hb : p + n ≤ heapLimit) :
    EvmAvoids (fun _ => [(p,n)]) s := by
  obtain ⟨ha, S, hs⟩ := hi
  obtain ⟨hw, hne, hlen, hlast, hfw, hrest⟩ := hs
  obtain ⟨Nd, htr⟩ := hw.2.2.2
  have hwt : WorldTypedWith s S Nd := ⟨hw.1, hw.2.1, hw.2.2.1, htr⟩
  refine ⟨ha, S, ⟨hw, hne, hlen, hlast, hfw, hrest⟩, Nd, htr, ?_⟩
  intro j hj i hmem
  rcases List.mem_append.1 hmem with hworld | hframes
  · exact heap_frontier_disj_world_g10 ha.2 hwt p n hp hb j hj i hworld
  · simp only [List.mem_singleton] at hj
    subst j
    obtain ⟨objs, hmap, hiobj⟩ := List.mem_flatten.1 hframes
    obtain ⟨ec, hec, rfl⟩ := List.mem_map.1 hmap
    exact heap_frontier_disj_frame_g10 ha.2 (hfw ec hec) p n hp hb i hiobj

theorem alloc_return_prestate_avoids_g10 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (p n : BitVec 64)
    (hi : EvmInv s) (hc : s.code = originalRuntimeCode)
    (hp : s.globals.lookup (ofString "heap_ptr") = some (.val (.word p)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hr : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_alloc) = (some (.returned v), post)) :
    EvmAvoids (fun _ => [(p.toNat, n.toNat)]) s := by
  obtain ⟨_, heq, _, hb, hlim, _⟩ := alloc_return_buffer_bounds_g10 s p n hi hc hp hn v post hr
  apply heap_frontier_evm_avoids_g10 s hi p.toNat n.toNat
  · exact le_of_eq heq.symm
  · exact le_trans hb hlim

theorem world_typed_heap_transport_g10 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (ha : ArenaReady s) (hap : ArenaReady post)
    (hh : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hsc : globN post "scratch_ptr" = globN s "scratch_ptr")
    (hg : ∀ g ∈ coreWorldGlobals, globN post g = globN s g)
    (hm : post.memory = s.memory) (hbe : post.be = s.be)
    (hf : fixedObjects post = fixedObjects s)
    (hw : WorldTypedWith s S Nd) : WorldTypedWith post S Nd := by
  have hcell : SameTypedCells s post S Nd := by
    refine ⟨hbe, hap.1.memaddrs.trans ha.1.memaddrs.symm, ha.1.memaddrs, ?_, ?_, ?_⟩
    · intros; rw [hm]
    · intros; rw [hm]
    · intros; unfold memB; rw [hm, hbe]
  have hfp := fixedTyped_of_eq hap hw.2.2.1 hh (le_of_eq hsc) hf
  exact (worldTypedWith_congr_w1 ha hap hh (le_of_eq hsc) hg hcell hw
    ⟨hfp, fun o ho => Or.inl (hf ▸ ho)⟩).1

theorem heap_step_fixed_objects_g10 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (ha : ArenaReady s) (hap : ArenaReady post) (hw : WorldTypedWith s S Nd)
    (hm : post.memory = s.memory) (hbe : post.be = s.be)
    (hg : GlobalsKept ["heap_ptr"] s post) :
    fixedObjects post = fixedObjects s := by
  have hcell : SameTypedCells s post S Nd := by
    refine ⟨hbe, hap.1.memaddrs.trans ha.1.memaddrs.symm, ha.1.memaddrs, ?_, ?_, ?_⟩
    · intros; rw [hm]
    · intros; rw [hm]
    · intros; unfold memB; rw [hm, hbe]
  have hglob : ∀ nm : String, ofString nm ≠ ofString "heap_ptr" → globN post nm = globN s nm := by
    intro nm hne
    unfold globN
    rw [← hg (ofString nm) (by simp [hne])]
  unfold fixedObjects
  rw [blockOutObjects_eq ha.2 hw.2.2.1 hcell (hglob "bo" (by decide)),
      balObjects_eq ha.2 hw.1 hw.2.2.1 hcell (hglob "bal_accounts" (by decide)),
      hglob "journal" (by decide), hglob "journal_cap" (by decide)]
  congr 3
  apply List.map_congr_left
  intro gn hgn
  have hne : ofString gn.1 ≠ ofString "heap_ptr" := by revert gn hgn; decide
  rw [hglob gn.1 hne]

theorem heap_step_world_typed_g10 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (ha : ArenaReady s) (hap : ArenaReady post) (hw : WorldTypedWith s S Nd)
    (hh : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hm : post.memory = s.memory) (hbe : post.be = s.be)
    (hg : GlobalsKept ["heap_ptr"] s post) : WorldTypedWith post S Nd := by
  have hglob : ∀ nm : String, ofString nm ≠ ofString "heap_ptr" → globN post nm = globN s nm := by
    intro nm hne
    unfold globN
    rw [← hg (ofString nm) (by simp [hne])]
  apply world_typed_heap_transport_g10 ha hap hh (hglob "scratch_ptr" (by decide))
    ?_ hm hbe (heap_step_fixed_objects_g10 ha hap hw hm hbe hg) hw
  intro g hmem
  apply hglob
  revert g hmem
  decide

theorem heap_step_frame_objects_g10 {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (hm : post.memory = s.memory)
    (hg : GlobalsKept ["heap_ptr"] s post) (ec : Ivl) :
    frameObjects post ec = frameObjects s ec := by
  have he : globN post "vm_system_address" = globN s "vm_system_address" := by
    unfold globN
    rw [← hg (ofString "vm_system_address") (by decide)]
  simp only [frameObjects, frameLogs, frameRet, frameLogObjects, logOwnedIvls,
    logRecordIvls, memW, hm, he]
  rfl

theorem heap_step_world_ivls_g10 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {S Nd : List Nat}
    (ha : ArenaReady s) (hap : ArenaReady post) (hw : WorldTypedWith s S Nd)
    (hm : post.memory = s.memory) (hbe : post.be = s.be)
    (hg : GlobalsKept ["heap_ptr"] s post) :
    worldTypedIvls post S Nd = worldTypedIvls s S Nd := by
  have hcell : SameTypedCells s post S Nd := by
    refine ⟨hbe, hap.1.memaddrs.trans ha.1.memaddrs.symm, ha.1.memaddrs, ?_, ?_, ?_⟩
    · intros; rw [hm]
    · intros; rw [hm]
    · intros; unfold memB; rw [hm, hbe]
  have hglob : ∀ nm : String, ofString nm ≠ ofString "heap_ptr" → globN post nm = globN s nm := by
    intro nm hne
    unfold globN
    rw [← hg (ofString nm) (by simp [hne])]
  have ht : S.flatMap (htabFootprint post) = S.flatMap (htabFootprint s) := by
    have hf : htabFootprint post = htabFootprint s := by
      funext t
      simp only [htabFootprint, hdr, memW, hm]
    rw [hf]
  unfold worldTypedIvls
  rw [ht, nodeExtents_eq hw.2.2.2.1 hcell,
    blockOutObjects_eq ha.2 hw.2.2.1 hcell (hglob "bo" (by decide)),
    balObjects_eq ha.2 hw.1 hw.2.2.1 hcell (hglob "bal_accounts" (by decide)),
    hglob "journal" (by decide), hglob "journal_cap" (by decide)]
  congr 5
  apply List.map_congr_left
  intro r hr
  have hne : ofString r.1 ≠ ofString "heap_ptr" := by revert r hr; decide
  rw [hglob r.1 hne]

theorem heap_step_evm_avoids_g10 {F : Type}
    {s post : PanSemStateFiniteExact 64 F} (os : List Ivl)
    (hav : EvmAvoids (fun _ => os) s) (hap : ArenaReady post)
    (hh : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hm : post.memory = s.memory) (hbe : post.be = s.be)
    (hg : GlobalsKept ["heap_ptr"] s post) : EvmAvoids (fun _ => os) post := by
  obtain ⟨ha, S, hi, Nd, htr, hd⟩ := hav
  have hw : WorldTypedWith s S Nd := ⟨hi.1.1, hi.1.2.1, hi.1.2.2.1, htr⟩
  have hwp := heap_step_world_typed_g10 ha hap hw hh hm hbe hg
  obtain ⟨hip, hch, _⟩ := evmInvAt_of_fresh_heap_step ha hi hap hbe hh hg
    (by intro a hn; rw [hm])
    (by intro b hb hn; unfold memB; rw [hm, hbe])
  refine ⟨hap, S, hip, Nd, hwp.2.2.2, ?_⟩
  have hfo : frameObjects post = frameObjects s := by
    funext ec
    exact heap_step_frame_objects_g10 hm hg ec
  simpa only [heap_step_world_ivls_g10 ha hap hw hm hbe hg, hch, hfo] using hd

theorem alloc_return_avoids_g10 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (p n : BitVec 64)
    (hi : EvmInv s) (hw : Group10.HeadMemChainWF s)
    (hc : s.code = originalRuntimeCode)
    (hp : s.globals.lookup (ofString "heap_ptr") = some (.val (.word p)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 F)
    (hr : evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_alloc) = (some (.returned v), post)) :
    EvmAvoids (fun _ => [(p.toNat, n.toNat)]) post := by
  have hav := alloc_return_prestate_avoids_g10 s p n hi hc hp hn v post hr
  have ha := (alloc_return_aligned_g10 s p n hi hw hc hp hn v post hr).1.1
  have hpn : globN s "heap_ptr" = p.toNat := by unfold globN; rw [hp]
  have hple : p.toNat ≤ InitECandidate.Solver.HeapPotential.cMax.toNat := by
    rw [← hpn]; exact hi.1.2.2.1
  have h := M13.evaluate_alloc_body_general s p n hc hple hp hn v
  rw [hr] at h
  obtain ⟨_, hg, hm, hlo, _, _⟩ := h rfl
  have hbe := R16Shards.evaluate_be_eq s (sourceFnBody Guest.Software.guestFn_alloc)
  rw [hr] at hbe
  apply heap_step_evm_avoids_g10 _ hav ha ?_ hm hbe ?_
  · unfold globN
    rw [hg, hp]
    simp only [HolFiniteMapExact.lookup_update, FUPDATE, beq_self_eq_true, ite_true]
    omega
  · intro k hk
    have hne : ofString "heap_ptr" ≠ k := by intro he; subst k; exact hk (by simp)
    rw [hg]
    simp [HolFiniteMapExact.lookup_update, FUPDATE, hne]


/-! ## ChildContinuationA step combinators and head-frame word readers (ccA) -/

/-! ## 1. Head-frame word readers -/

theorem wordAt_ev_off_g10 {F : Type} {s : PanSemStateFiniteExact 64 F} {k : Nat}
    (hInv : EvmInv s) (hk8 : k % 8 = 0) (hk : k + 8 ≤ 280) : WordAt s (globN s "ev" + k) := by
  have hhead_mem : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by
    simp [evmChain, evmChainFrom]
  have hFW0 := hInv.2.choose_spec.2.2.2.2.1 _ hhead_mem
  have hwok := (hFW0.1 (globN s "ev", 280) (by simp)).2
  have hidx : k / 8 < 280 / 8 := by omega
  have hkm : 8 * (k / 8) = k := by omega
  rw [← hkm]
  exact hwok.2.2 (k / 8) hidx

theorem msgOwned_head_g10 {F : Type} {s : PanSemStateFiniteExact 64 F} (hInv : EvmInv s) :
    ∃ S : List Nat, MsgOwned s S (memW s (globN s "ev" + 112)) := by
  have hhead_mem : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by
    simp [evmChain, evmChainFrom]
  have hFW0 := hInv.2.choose_spec.2.2.2.2.1 _ hhead_mem
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hmo⟩ := hFW0
  exact ⟨_, hmo⟩

theorem wordAt_msg_off_g10 {F : Type} {s : PanSemStateFiniteExact 64 F} {k : Nat}
    (hInv : EvmInv s) (hk8 : k % 8 = 0) (hk : k + 8 ≤ 176) :
    WordAt s (memW s (globN s "ev" + 112) + k) := by
  obtain ⟨_, hmo⟩ := msgOwned_head_g10 hInv
  have hwok := hmo.2.1
  have hidx : k / 8 < 176 / 8 := by omega
  have hkm : 8 * (k / 8) = k := by omega
  rw [← hkm]
  exact hwok.2.2 (k / 8) hidx

/-! ## 2. ChildContinuationA step combinator: void callee -/


theorem ccA_seq_call_g10 {F : Type} {P Q : PanSemStateFiniteExact 64 F → Prop}
    {Pc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {Qc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    {fname : MlS} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (hf : EvmPreservingSpecA Pc Qc fname)
    (hentry : ∀ (t : PanSemStateFiniteExact 64 F) (values : List (ValueHOL 64)) (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (rs : ShapeHOL),
      t.code = originalRuntimeCode → EvmInv t → Group10.HeadMemChainWF t → P t →
      evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) args = some values →
      lookupCodeHOLFinite t.code.lookup fname values = some (body, callee, rs) →
      Pc (callEntryStateHOLFinite t callee))
    (hstep : ∀ (t : PanSemStateFiniteExact 64 F) (values : List (ValueHOL 64)) (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (rs : ShapeHOL) (v : ValueHOL 64) (cpost : PanSemStateFiniteExact 64 F),
      EvmInv t → Group10.HeadMemChainWF t → P t →
      EvmInv cpost → Group10.HeadMemChainWF cpost →
      evmChain cpost = evmChain (callEntryStateHOLFinite t callee) →
      Qc (callEntryStateHOLFinite t callee) v cpost →
      Q { cpost with locals := t.locals })
    (hcont : ChildContinuationA Q cont) :
    ChildContinuationA P (.seq (.call (some (none, none)) fname args) cont) := by
  intro t hc hi hw hp hnt
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_call] at hnt ⊢
  rcases hargs : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) args with _ | values
  · refine ⟨fun hv => absurd hv (by rintro ⟨_, h⟩; cases h),
      fun he => absurd he (by rintro ⟨_, h⟩; cases h)⟩
  · simp only [hargs] at hnt ⊢
    rcases hl : lookupCodeHOLFinite t.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · refine ⟨fun hv => absurd hv (by rintro ⟨_, h⟩; cases h),
        fun he => absurd he (by rintro ⟨_, h⟩; cases h)⟩
    · simp only [hl] at hnt ⊢
      by_cases hz : t.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt ⊢
        obtain ⟨params, body, retShape, hlook, hspec⟩ := hf
        have hbody_eq : body' = body :=
          lookupCodeHOLFinite_installed_body t.code.lookup fname params body body'
            retShape ret' values callee (by rw [hc]; exact hlook) hl
        subst body'
        have hret_eq : ret' = retShape := by
          have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
            t.code.lookup fname values body callee ret' hl
          rw [hc] at hx; simp only [Flapjack.lookupCodeHOLExact, hlook] at hx
          split at hx
          · exact (congrArg (fun x => x.2.2) (Option.some.inj hx)).symm
          · cases hx
        subst ret'
        have hi_ce : EvmInv (callEntryStateHOLFinite t callee) :=
          localsFree_evmInv t callee (t.clock - 1) hi
        have hw_ce : Group10.HeadMemChainWF (callEntryStateHOLFinite t callee) :=
          Group10.headMemChainWF_locals t callee (t.clock - 1) hw
        have hPc : Pc (callEntryStateHOLFinite t callee) :=
          hentry t values body callee retShape hc hi hw hp hargs hl
        have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup fname values =
            some (body, callee, retShape) := by rwa [← hc]
        have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata
          (callEntryStateHOLFinite t callee) body).1
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite t callee) body with ⟨res, cpost⟩
        simp only [hrun] at hnt hmeta ⊢
        change cpost.code = t.code at hmeta
        have hc_ce := evm_congr (s := t) (t := callEntryStateHOLFinite t callee) rfl rfl
        have hQ (hsafe : res ≠ some .timeOut) :
            (∀ v, res = some (.returned v) →
              (EvmInv cpost ∧ Group10.HeadMemChainWF cpost) ∧
              evmChain cpost = evmChain (callEntryStateHOLFinite t callee) ∧
              evmR cpost ≤ evmR (callEntryStateHOLFinite t callee) ∧
              Qc (callEntryStateHOLFinite t callee) v cpost) ∧
            (IsEvmErr res →
              (EvmInv cpost ∧ Group10.HeadMemChainWF cpost) ∧
              evmChain cpost = evmChain (callEntryStateHOLFinite t callee) ∧
              evmR cpost ≤ evmR (callEntryStateHOLFinite t callee)) := by
          have hs := hspec (callEntryStateHOLFinite t callee) hc hi_ce hw_ce hPc
            ⟨values, hl_orig⟩ (by rw [hrun]; exact hsafe)
          dsimp only at hs; rw [hrun] at hs; exact hs
        cases res with
        | none => refine ⟨fun hv => absurd hv (by rintro ⟨_, h⟩; cases h),
            fun he => absurd he (by rintro ⟨_, h⟩; cases h)⟩
        | some r0 =>
          cases r0 with
          | timeOut => simp at hnt
          | returned v =>
            by_cases hsh_ok : shapeEqHOL (shapeOfHOLExact v) retShape = true
            · simp only [hsh_ok, ↓reduceIte] at hnt ⊢
              obtain ⟨⟨hi_cp, hw_cp⟩, hch_cp, hR_cp, hQc_cp⟩ := (hQ (by simp)).1 v rfl
              have hQres : Q { cpost with locals := t.locals } :=
                hstep t values body callee retShape v cpost hi hw hp hi_cp hw_cp hch_cp hQc_cp
              have hc_res := evm_congr (s := cpost)
                (t := ({ cpost with locals := t.locals } : PanSemStateFiniteExact 64 F)) rfl rfl
              have hcode_res : (({ cpost with locals := t.locals } :
                  PanSemStateFiniteExact 64 F)).code = originalRuntimeCode := hmeta.trans hc
              have hi_res : EvmInv ({ cpost with locals := t.locals } :
                  PanSemStateFiniteExact 64 F) :=
                localsFree_evmInv cpost t.locals cpost.clock hi_cp
              have hw_res : Group10.HeadMemChainWF ({ cpost with locals := t.locals } :
                  PanSemStateFiniteExact 64 F) :=
                Group10.headMemChainWF_locals cpost t.locals cpost.clock hw_cp
              have hR_cp' : evmR cpost ≤ evmR t := by
                rw [hc_ce.2.1] at hR_cp; exact hR_cp
              have hR_le : evmR ({ cpost with locals := t.locals } :
                  PanSemStateFiniteExact 64 F) ≤ evmR t := by
                rw [hc_res.2.1]; exact hR_cp'
              obtain ⟨hret, herr⟩ := hcont _ hcode_res hi_res hw_res hQres
                (by simpa using hnt)
              refine ⟨fun hr => ?_, fun he => ?_⟩
              · obtain ⟨hinv, hle⟩ := hret hr
                exact ⟨hinv, le_trans hle hR_le⟩
              · obtain ⟨hinv, hdepth, hle⟩ := herr he
                refine ⟨hinv, ?_, le_trans hle hR_le⟩
                rw [hdepth, hc_res.2.2.1, hch_cp, hc_ce.2.2.1]
            · simp only [hsh_ok, Bool.false_eq_true, ↓reduceIte]
              refine ⟨fun hv => absurd hv (by rintro ⟨_, h⟩; cases h),
                fun he => absurd he (by rintro ⟨_, h⟩; cases h)⟩
          | exception eid ev =>
            by_cases heid : eid = ofString "EvmErr"
            · subst heid
              dsimp only
              obtain ⟨⟨hi_cp, hw_cp⟩, hch_cp, hR_cp⟩ := (hQ (by simp)).2 ⟨ev, rfl⟩
              have hi_el : EvmInv cpost.emptyLocalsHOLFinite :=
                localsFree_evmInv cpost _ cpost.clock hi_cp
              have hw_el : Group10.HeadMemChainWF cpost.emptyLocalsHOLFinite :=
                Group10.headMemChainWF_locals cpost _ cpost.clock hw_cp
              have hc_el := evm_congr (s := cpost) (t := cpost.emptyLocalsHOLFinite) rfl rfl
              refine ⟨fun hr => absurd hr (by rintro ⟨_, h⟩; cases h), fun _ => ?_⟩
              exact ⟨⟨hi_el, hw_el⟩, by rw [hc_el.2.2.1, hch_cp, hc_ce.2.2.1],
                by rw [hc_el.2.1]; rw [hc_ce.2.1] at hR_cp; exact hR_cp⟩
            · refine ⟨fun hr => absurd hr (by rintro ⟨_, h⟩; cases h),
                fun he => absurd he ?_⟩
              intro hc
              obtain ⟨_, hv⟩ := hc
              injection hv with h'; injection h' with h1 _
              exact heid h1
          | «break» | «continue» | error | finalFfi _ =>
            dsimp only
            refine ⟨fun hr => absurd hr (by rintro ⟨_, h⟩; cases h),
              fun he => absurd he (by rintro ⟨_, h⟩; cases h)⟩

/-! ## 5. ChildContinuationA step combinators -/

theorem ccA_dec_g10 {F : Type} {P Q : PanSemStateFiniteExact 64 F → Prop}
    {nm : MlS} {sh : ShapeHOL} {init : ExpHOL 64} {body : ProgHOL 64}
    (hinit : ∀ (t : PanSemStateFiniteExact 64 F) (v : ValueHOL 64),
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) init = some v →
      EvmInv t → P t → Q (setVarHOLFinite nm v t))
    (hbody : ChildContinuationA Q body) :
    ChildContinuationA P (.dec nm sh init body) := by
  intro t hc hi hw hp hnt
  rw [evaluateHOLFiniteState_dec_total] at hnt ⊢
  dsimp only at hnt ⊢
  revert hnt
  split
  · intro _; exact ⟨fun hv => absurd hv (by rintro ⟨_, h⟩; cases h),
      fun he => absurd he (by rintro ⟨_, h⟩; cases h)⟩
  · rename_i v hv
    split
    · rename_i hsh
      simp only [hsh, ↓reduceIte] at ⊢
      intro hnt
      have hi1 : EvmInv (setVarHOLFinite nm v t) := localsFree_evmInv t _ t.clock hi
      have hw1 : Group10.HeadMemChainWF (setVarHOLFinite nm v t) := Group10.headMemChainWF_locals t _ t.clock hw
      have hc1 := evm_congr (s := t) (t := (setVarHOLFinite nm v t : PanSemStateFiniteExact 64 F)) rfl rfl
      obtain ⟨hret, herr⟩ := hbody (setVarHOLFinite nm v t) hc hi1 hw1 (hinit t v hv hi hp) hnt
      refine ⟨fun hr => ?_, fun he => ?_⟩
      · obtain ⟨hinv, hle⟩ := hret hr
        have hc2 := evm_congr (s := ((evaluateHOLFiniteState (setVarHOLFinite nm v t) body).2 :
            PanSemStateFiniteExact 64 F))
          (t := ({ (evaluateHOLFiniteState (setVarHOLFinite nm v t) body).2 with
            locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState (setVarHOLFinite nm v t) body).2.locals
              (nm, t.locals.lookup nm) } : PanSemStateFiniteExact 64 F)) rfl rfl
        have hi2 : EvmInv ({ (evaluateHOLFiniteState (setVarHOLFinite nm v t) body).2 with
            locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState (setVarHOLFinite nm v t) body).2.locals
              (nm, t.locals.lookup nm) }) :=
          localsFree_evmInv _ _ _ hinv.1
        have hw2 : Group10.HeadMemChainWF ({ (evaluateHOLFiniteState (setVarHOLFinite nm v t) body).2 with
            locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState (setVarHOLFinite nm v t) body).2.locals
              (nm, t.locals.lookup nm) }) :=
          Group10.headMemChainWF_locals _ _ _ hinv.2
        exact ⟨⟨hi2, hw2⟩, le_trans (le_of_eq hc2.2.1) (le_trans hle (le_of_eq hc1.2.1))⟩
      · obtain ⟨hinv, hdepth, hle⟩ := herr he
        have hc2 := evm_congr (s := ((evaluateHOLFiniteState (setVarHOLFinite nm v t) body).2 :
            PanSemStateFiniteExact 64 F))
          (t := ({ (evaluateHOLFiniteState (setVarHOLFinite nm v t) body).2 with
            locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState (setVarHOLFinite nm v t) body).2.locals
              (nm, t.locals.lookup nm) } : PanSemStateFiniteExact 64 F)) rfl rfl
        have hi2 : EvmInv ({ (evaluateHOLFiniteState (setVarHOLFinite nm v t) body).2 with
            locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState (setVarHOLFinite nm v t) body).2.locals
              (nm, t.locals.lookup nm) }) :=
          localsFree_evmInv _ _ _ hinv.1
        have hw2 : Group10.HeadMemChainWF ({ (evaluateHOLFiniteState (setVarHOLFinite nm v t) body).2 with
            locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState (setVarHOLFinite nm v t) body).2.locals
              (nm, t.locals.lookup nm) }) :=
          Group10.headMemChainWF_locals _ _ _ hinv.2
        refine ⟨⟨hi2, hw2⟩, Eq.trans (Eq.trans hc2.2.2.1 hdepth) hc1.2.2.1,
          le_trans (le_of_eq hc2.2.1) (le_trans hle (le_of_eq hc1.2.1))⟩
    · intro _; exact ⟨fun hv => absurd hv (by rintro ⟨_, h⟩; cases h),
        fun he => absurd he (by rintro ⟨_, h⟩; cases h)⟩

theorem ccA_ret_g10 {F : Type} {P : PanSemStateFiniteExact 64 F → Prop} (e : ExpHOL 64) :
    ChildContinuationA P (.return e) := by
  intro t hc hi hw _ hnt
  rw [evaluateHOLFiniteState_return] at hnt ⊢
  dsimp only at hnt ⊢
  revert hnt
  split
  · intro _; exact ⟨fun hv => absurd hv (by rintro ⟨_, h⟩; cases h),
      fun he => absurd he (by rintro ⟨_, h⟩; cases h)⟩
  · rename_i v hv
    split
    · dsimp only
      have hi' : EvmInv (emptyLocalsHOLFinite t) := localsFree_evmInv t _ t.clock hi
      have hw' : Group10.HeadMemChainWF (emptyLocalsHOLFinite t) := Group10.headMemChainWF_locals t _ t.clock hw
      have hc' := evm_congr (s := t) (t := (emptyLocalsHOLFinite t : PanSemStateFiniteExact 64 F)) rfl rfl
      intro hnt
      refine ⟨fun _ => ⟨⟨hi', hw'⟩, ?_⟩, fun he => absurd he (by rintro ⟨_, h⟩; cases h)⟩
      rw [hc'.2.1]
    · intro _; exact ⟨fun hv => absurd hv (by rintro ⟨_, h⟩; cases h),
        fun he => absurd he (by rintro ⟨_, h⟩; cases h)⟩

theorem ccA_decCall_g10 {F : Type} {P Q : PanSemStateFiniteExact 64 F → Prop}
    {Pc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {Qc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    {nm : MlS} {sh : ShapeHOL} {fname : MlS} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (hf : EvmPreservingSpecA Pc Qc fname)
    (hentry : ∀ (t : PanSemStateFiniteExact 64 F) (values : List (ValueHOL 64)) (body : ProgHOL 64)
      (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret' : ShapeHOL),
      t.code = originalRuntimeCode → EvmInv t → Group10.HeadMemChainWF t → P t →
      evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) args = some values →
      lookupCodeHOLFinite t.code.lookup fname values = some (body, callee, ret') →
      Pc (callEntryStateHOLFinite t callee))
    (hstep : ∀ (t : PanSemStateFiniteExact 64 F) (values : List (ValueHOL 64)) (body : ProgHOL 64)
      (callee : HolFiniteMapExact MlS (ValueHOL 64)) (retShape : ShapeHOL) (v : ValueHOL 64)
      (cpost : PanSemStateFiniteExact 64 F),
      EvmInv t → Group10.HeadMemChainWF t → P t →
      evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) args = some values →
      lookupCodeHOLFinite originalRuntimeCode.lookup fname values = some (body, callee, retShape) →
      EvmInv cpost → Group10.HeadMemChainWF cpost →
      evmChain cpost = evmChain (callEntryStateHOLFinite t callee) →
      Qc (callEntryStateHOLFinite t callee) v cpost →
      Q (setVarHOLFinite nm v { cpost with locals := t.locals }))
    (hcont : ChildContinuationA Q cont) :
    ChildContinuationA P (.decCall nm sh fname args cont) := by
  intro t hc hi hw hp hnt
  obtain ⟨params, body, retShape, hlook, hspec⟩ := hf
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt ⊢
  rcases hargs : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) args with _ | values
  · refine ⟨fun hv => absurd hv (by rintro ⟨_, h⟩; cases h),
      fun he => absurd he (by rintro ⟨_, h⟩; cases h)⟩
  · simp only [hargs] at hnt ⊢
    rcases hl : lookupCodeHOLFinite t.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · refine ⟨fun hv => absurd hv (by rintro ⟨_, h⟩; cases h),
        fun he => absurd he (by rintro ⟨_, h⟩; cases h)⟩
    · simp only [hl] at hnt ⊢
      by_cases hz : t.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt ⊢
        have hbody_eq : body' = body :=
          lookupCodeHOLFinite_installed_body t.code.lookup fname params body body'
            retShape ret' values callee (by rw [hc]; exact hlook) hl
        subst body'
        have hret_eq : ret' = retShape := by
          have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
            t.code.lookup fname values body callee ret' hl
          rw [hc] at hx; simp only [Flapjack.lookupCodeHOLExact, hlook] at hx
          split at hx
          · exact (congrArg (fun x => x.2.2) (Option.some.inj hx)).symm
          · cases hx
        subst ret'
        have hi_ce : EvmInv (callEntryStateHOLFinite t callee) :=
          localsFree_evmInv t callee (t.clock - 1) hi
        have hw_ce : Group10.HeadMemChainWF (callEntryStateHOLFinite t callee) :=
          Group10.headMemChainWF_locals t callee (t.clock - 1) hw
        have hPc : Pc (callEntryStateHOLFinite t callee) := hentry t values body callee retShape hc hi hw hp hargs hl
        have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup fname values =
            some (body, callee, retShape) := by rwa [← hc]
        have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata
          (callEntryStateHOLFinite t callee) body).1
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite t callee) body with ⟨res, cpost⟩
        simp only [hrun] at hnt hmeta ⊢
        change cpost.code = t.code at hmeta
        have hc_ce := evm_congr (s := t) (t := (callEntryStateHOLFinite t callee : PanSemStateFiniteExact 64 F)) rfl rfl
        have hQ (hsafe : res ≠ some .timeOut) :
            (∀ v, res = some (.returned v) →
              (EvmInv cpost ∧ Group10.HeadMemChainWF cpost) ∧
              evmChain cpost = evmChain (callEntryStateHOLFinite t callee) ∧
              evmR cpost ≤ evmR (callEntryStateHOLFinite t callee) ∧
              Qc (callEntryStateHOLFinite t callee) v cpost) ∧
            (IsEvmErr res →
              (EvmInv cpost ∧ Group10.HeadMemChainWF cpost) ∧
              evmChain cpost = evmChain (callEntryStateHOLFinite t callee) ∧
              evmR cpost ≤ evmR (callEntryStateHOLFinite t callee)) := by
          have hs := hspec (callEntryStateHOLFinite t callee) hc hi_ce hw_ce hPc ⟨values, hl_orig⟩
            (by rw [hrun]; exact hsafe)
          dsimp only at hs; rw [hrun] at hs; exact hs
        cases res with
        | none =>
          refine ⟨fun hv => absurd hv (by rintro ⟨_, h⟩; cases h),
            fun he => absurd he (by rintro ⟨_, h⟩; cases h)⟩
        | some r0 =>
          cases r0 with
          | timeOut => simp at hnt
          | returned v =>
            dsimp only at hnt ⊢
            split
            · rename_i hsh_ok
              rw [if_pos hsh_ok] at hnt
              dsimp only at hnt ⊢
              obtain ⟨⟨hi_cp, hw_cp⟩, hch_cp, hR_cp, hQc_cp⟩ := (hQ (by simp)).1 v rfl
              have hQ_res : Q (setVarHOLFinite nm v { cpost with locals := t.locals }) :=
                hstep t values body callee retShape v cpost hi hw hp hargs hl_orig hi_cp hw_cp hch_cp hQc_cp
              have hcode_res : ((setVarHOLFinite nm v { cpost with locals := t.locals } :
                  PanSemStateFiniteExact 64 F)).code = originalRuntimeCode := hmeta.trans hc
              have hi_res : EvmInv (setVarHOLFinite nm v { cpost with locals := t.locals }) :=
                localsFree_evmInv cpost _ cpost.clock hi_cp
              have hw_res : Group10.HeadMemChainWF (setVarHOLFinite nm v { cpost with locals := t.locals }) :=
                Group10.headMemChainWF_locals cpost _ cpost.clock hw_cp
              have hc_res := evm_congr (s := cpost)
                (t := (setVarHOLFinite nm v { cpost with locals := t.locals } :
                  PanSemStateFiniteExact 64 F)) rfl rfl
              have hR_res : evmR (setVarHOLFinite nm v { cpost with locals := t.locals }) ≤
                  evmR t := by
                rw [hc_res.2.1]; rw [hc_ce.2.1] at hR_cp; exact hR_cp
              obtain ⟨hret, herr⟩ := hcont (setVarHOLFinite nm v { cpost with locals := t.locals })
                hcode_res hi_res hw_res hQ_res hnt
              have hc_fin := evm_congr
                (s := ((evaluateHOLFiniteState (setVarHOLFinite nm v { cpost with locals := t.locals }) cont).2 :
                  PanSemStateFiniteExact 64 F))
                (t := ({ (evaluateHOLFiniteState (setVarHOLFinite nm v { cpost with locals := t.locals }) cont).2 with
                  locals := HolFiniteMapExact.resVarEq
                    (evaluateHOLFiniteState (setVarHOLFinite nm v { cpost with locals := t.locals }) cont).2.locals
                    (nm, t.locals.lookup nm) } : PanSemStateFiniteExact 64 F)) rfl rfl
              refine ⟨fun hr => ?_, fun he => ?_⟩
              · obtain ⟨hinv, hle⟩ := hret hr
                refine ⟨⟨?_, ?_⟩, ?_⟩
                · exact localsFree_evmInv _ _ _ hinv.1
                · exact Group10.headMemChainWF_locals _ _ _ hinv.2
                · rw [hc_fin.2.1]; exact le_trans hle hR_res
              · obtain ⟨hinv, hdepth, hle⟩ := herr he
                refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
                · exact localsFree_evmInv _ _ _ hinv.1
                · exact Group10.headMemChainWF_locals _ _ _ hinv.2
                · rw [hc_fin.2.2.1, hdepth, hc_res.2.2.1, hch_cp, hc_ce.2.2.1]
                · rw [hc_fin.2.1]; exact le_trans hle hR_res
            · refine ⟨fun hv => absurd hv (by rintro ⟨_, h⟩; cases h),
                fun he => absurd he (by rintro ⟨_, h⟩; cases h)⟩
          | exception eid ev =>
            by_cases heid : eid = ofString "EvmErr"
            · subst heid
              dsimp only at hnt ⊢
              obtain ⟨⟨hi_cp, hw_cp⟩, hch_cp, hR_cp⟩ := (hQ (by simp)).2 ⟨ev, rfl⟩
              have hi_el : EvmInv cpost.emptyLocalsHOLFinite :=
                localsFree_evmInv cpost _ cpost.clock hi_cp
              have hw_el : Group10.HeadMemChainWF cpost.emptyLocalsHOLFinite :=
                Group10.headMemChainWF_locals cpost _ cpost.clock hw_cp
              have hc_el := evm_congr (s := cpost) (t := (cpost.emptyLocalsHOLFinite : PanSemStateFiniteExact 64 F)) rfl rfl
              refine ⟨fun hr => absurd hr (by rintro ⟨_, h⟩; cases h), fun _ => ?_⟩
              exact ⟨⟨hi_el, hw_el⟩, by rw [hc_el.2.2.1, hch_cp, hc_ce.2.2.1],
                by rw [hc_el.2.1]; rw [hc_ce.2.1] at hR_cp; exact hR_cp⟩
            · refine ⟨fun hr => absurd hr (by rintro ⟨_, h⟩; cases h),
                fun he => absurd he ?_⟩
              intro hc
              obtain ⟨_, hv⟩ := hc
              injection hv with h'; injection h' with h1 _
              exact heid h1
          | «break» | «continue» | error | finalFfi _ =>
            refine ⟨fun hv => absurd hv (by rintro ⟨_, h⟩; cases h),
              fun he => absurd he (by rintro ⟨_, h⟩; cases h)⟩

end InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB
