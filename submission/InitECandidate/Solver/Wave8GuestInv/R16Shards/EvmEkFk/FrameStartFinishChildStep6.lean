import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.FrameStartFinishChildStep1
import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.FrameStartFinishChildStep23
import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.FrameStartFinishChildStep4b
import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.FrameStartFinishChildStep6b
import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.StorageCreateFinish
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.HeadMemAlignedBridge

set_option Elab.async false
set_option autoImplicit false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8Contracts.M23 (EvmStep EvmKeeps EvmAvoids GlobalsKept)
open InitECandidate.Solver.Wave8GuestInv.R11Shards

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

private noncomputable abbrev evalAt6c {F : Type} (t : PanSemStateFiniteExact 64 F)
    (e : ExpHOL 64) : Option (ValueHOL 64) :=
  @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) e

theorem fcPreludeRel_pop_logs_self_disj {F : Type}
    {s0 s post : PanSemStateFiniteExact 64 F}
    (h : PreludeRel s0 s)
    (hne : memW s (globN s "cur_cont" + 16) ≠ 0)
    (hm : post.memory = s.memory)
    (hvmsa : globN post "vm_system_address" = globN s "vm_system_address") :
    FcLogsSelfDisj s0 post := by
  have hmw : ∀ a, memW post a = memW s a := fun a => by
    unfold memW; rw [hm]
  have hhead := congrArg List.head? h.chain_eq
  rw [evmChain_cons, evmChain_cons] at hhead
  simp only [List.head?_cons, Option.some.injEq, Prod.mk.injEq] at hhead
  have hev_s : globN s "ev" = globN s0 "ev" := hhead.1
  have hcur : globN s "cur_cont" = globN s0 "cur_cont" := hhead.2
  have hcons := evmChain_cons_of_cont_ne_zero hne
  have hcons0 : evmChain s = (globN s0 "ev", globN s0 "cur_cont") :: (evmChain s).tail := by
    conv_lhs => rw [hcons]
    conv_rhs => rw [hcons]
    simp [hev_s, hcur]
  obtain ⟨S, hI⟩ := h.inv.2
  have hFO_pw_s := hI.2.2.2.2.2.2.2.1
  rw [hcons0, List.map_cons, List.flatten_cons, List.pairwise_append] at hFO_pw_s
  have hpw_fo : (frameObjects s (globN s0 "ev", globN s0 "cur_cont")).Pairwise Disj :=
    hFO_pw_s.1
  unfold frameObjects at hpw_fo
  rw [List.pairwise_append] at hpw_fo
  have hfl_eq : ∀ ec, frameLogs post ec = frameLogs s ec := fun ec => by
    unfold frameLogs; simp only [hmw]
  have hflo_eq : ∀ ec, frameLogObjects post ec = frameLogObjects s ec := fun ec => by
    unfold frameLogObjects logOwnedIvls logRecordIvls; simp only [hmw, hvmsa]
  intro o ho
  rw [hfl_eq]
  rw [hflo_eq] at ho
  exact hpw_fo.2.2 (frameLogs s (globN s0 "ev", globN s0 "cur_cont")) (by simp) o ho

theorem fcLogsSelfDisj_setVar {F : Type}
    {s0 st : PanSemStateFiniteExact 64 F}
    (h : FcLogsSelfDisj s0 st) (nm : MlS) (v : ValueHOL 64) :
    FcLogsSelfDisj s0 (setVarHOLFinite nm v st) := by
  have hmw : ∀ a, memW (setVarHOLFinite nm v st) a = memW st a := fun _ => rfl
  have hvmsa : globN (setVarHOLFinite nm v st) "vm_system_address" =
      globN st "vm_system_address" := rfl
  have hfl : ∀ ec, frameLogs (setVarHOLFinite nm v st) ec = frameLogs st ec := fun ec => by
    unfold frameLogs; simp only [hmw]
  have hflo : ∀ ec, frameLogObjects (setVarHOLFinite nm v st) ec = frameLogObjects st ec :=
    fun ec => by
      unfold frameLogObjects logOwnedIvls logRecordIvls; simp only [hmw, hvmsa]
  intro o ho
  rw [hfl]
  rw [hflo] at ho
  exact h o ho

private theorem eval_load_local_off_6c {F : Type} (s : PanSemStateFiniteExact 64 F)
    {lname : String} {base sz off : Nat}
    (hlk : s.locals.lookup (ofString lname) = some (.val (.word (BitVec.ofNat 64 base))))
    (_hdom : s.memaddrs = ordinaryDomain)
    (hwok : WordsOK s (base, sz))
    (hbnd : base + sz ≤ 2 ^ 64)
    (hoff : off + 8 ≤ sz) (hoff8 : off % 8 = 0) :
    evalAt6c s
      (.load .one (.op .add [.var .local (ofString lname), .const (BitVec.ofNat 64 off)])) =
      some (.val (.word (BitVec.ofNat 64 (memW s (base + off))))) := by
  have hadd_eq : BitVec.ofNat 64 base + BitVec.ofNat 64 off = BitVec.ofNat 64 (base + off) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show base < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show off < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show base + off < 2 ^ 64 by omega)]
  have hwa : WordAt s (base + off) := hwok.2.2 (off / 8) (by omega)
    |> fun h => by rwa [show base + 8 * (off / 8) = base + off by omega] at h
  obtain ⟨w, hmem_dom, hmem_eq⟩ := hwa
  have hadd0 : BitVec.ofNat 64 base + (BitVec.ofNat 64 off + (0 : BitVec 64)) =
      BitVec.ofNat 64 (base + off) := by
    change BitVec.ofNat 64 base + (BitVec.ofNat 64 off + 0#64) = _
    rw [BitVec.add_zero, hadd_eq]
  simp only [evalAt6c, evalHOLExact, evalListHOLExact, hlk, isWfShapeExactHOL, memLoadHOLExact,
    ↓reduceIte, valueIsWord, valueWord, wordOpHOL, wordOp, List.all, List.map, Option.map,
    List.foldr, Bool.and_self]
  rw [hadd0]
  simp only [hmem_dom, ↓reduceIte, hmem_eq, Option.some.injEq, ValueHOL.val.injEq,
    HolWordLab.word.injEq]
  unfold memW
  rw [hmem_eq]; simp

private theorem eval_cmp_equal_word_6c {F : Type} (s : PanSemStateFiniteExact 64 F)
    (e1 e2 : ExpHOL 64) (w1 w2 : BitVec 64)
    (h1 : evalAt6c s e1 = some (.val (.word w1)))
    (h2 : evalAt6c s e2 = some (.val (.word w2))) :
    evalAt6c s (.cmp .equal e1 e2) =
      some (.val (.word (if w1 = w2 then 1#64 else 0#64))) := by
  simp only [evalAt6c, evalHOLExact] at h1 h2 ⊢
  simp only [h1, h2, Compiler.Encoders.Asm.wordCmpHOL]
  by_cases h : w1 = w2 <;> simp [h]

private theorem eval_var_local_word_6c {F : Type} (s : PanSemStateFiniteExact 64 F)
    {nm : String} {w : BitVec 64}
    (hlk : s.locals.lookup (ofString nm) = some (.val (.word w))) :
    evalAt6c s (.var .local (ofString nm)) = some (.val (.word w)) := by
  simp [evalAt6c, evalHOLExact, hlk]

private theorem eval_var_global_word_6c {F : Type} (s : PanSemStateFiniteExact 64 F)
    {gn : String} {w : BitVec 64}
    (hlk : s.globals.lookup (ofString gn) = some (.val (.word w))) :
    evalAt6c s (.var .global (ofString gn)) = some (.val (.word w)) := by
  simp [evalAt6c, evalHOLExact, hlk]

private theorem eval_cmp_notEqual_word_6c {F : Type} (s : PanSemStateFiniteExact 64 F)
    (e1 e2 : ExpHOL 64) (w1 w2 : BitVec 64)
    (h1 : evalAt6c s e1 = some (.val (.word w1)))
    (h2 : evalAt6c s e2 = some (.val (.word w2))) :
    evalAt6c s (.cmp .notEqual e1 e2) =
      some (.val (.word (if w1 ≠ w2 then 1#64 else 0#64))) := by
  simp only [evalAt6c, evalHOLExact] at h1 h2 ⊢
  simp only [h1, h2, Compiler.Encoders.Asm.wordCmpHOL]
  by_cases h : w1 = w2 <;> simp [h]

private theorem fcPoppedChild_setVar_6c {F : Type}
    {s0 st : PanSemStateFiniteExact 64 F} {S : List Nat}
    (h : FcPoppedChild s0 st S) (nm : MlS) (v : ValueHOL 64) :
    FcPoppedChild s0 (setVarHOLFinite nm v st) S := by
  have hbr : setVarHOLFinite nm v st =
      { st with locals := (setVarHOLFinite nm v st).locals, clock := st.clock } := rfl
  rw [hbr]
  exact fcPoppedChild_with_locals_clock h _ st.clock

private theorem fcBranchState_setVar_6c {F : Type}
    {s0 st : PanSemStateFiniteExact 64 F} {S : List Nat}
    (h : FcBranchState s0 st S) (nm : MlS) (v : ValueHOL 64)
    (hfresh : nm ≠ ofString "rec") (hfresh2 : nm ≠ ofString "child")
    (hfresh3 : nm ≠ ofString "parent") (hfresh4 : nm ≠ ofString "kind")
    (hfresh5 : nm ≠ ofString "msg") (hfresh6 : nm ≠ ofString "new_account_charged")
    (hfresh7 : nm ≠ ofString "child_mark") (hfresh8 : nm ≠ ofString "child_mem_mark")
    (hfresh9 : nm ≠ ofString "out_start") (hfresh10 : nm ≠ ofString "out_size")
    (hfresh11 : nm ≠ ofString "contract_address") :
    FcBranchState s0 (setVarHOLFinite nm v st) S := by
  have hbr : setVarHOLFinite nm v st =
      { st with locals := (setVarHOLFinite nm v st).locals, clock := st.clock } := rfl
  rw [hbr]
  exact fcBranchState_congr_locals_clock _ st.clock h
    (fcEntryLocals_setVar hfresh hfresh2 hfresh3 hfresh4 hfresh5 hfresh6 hfresh7
      hfresh8 hfresh9 hfresh10 hfresh11 h.locals_ok)

private theorem wordsOK_of_arena_mem_6c {F : Type}
    {s t : PanSemStateFiniteExact 64 F} {a sz : Nat}
    (hAs : ArenaReady s) (hAt : ArenaReady t) (hw : WordsOK s (a, sz))
    (hmem : ∀ k, k < sz / 8 →
      t.memory (BitVec.ofNat 64 (a + 8 * k)) = s.memory (BitVec.ofNat 64 (a + 8 * k))) :
    WordsOK t (a, sz) := by
  obtain ⟨h1, h2, h3⟩ := hw
  refine ⟨h1, h2, fun k hk => ?_⟩
  obtain ⟨w, hdom, hm2⟩ := h3 k hk
  refine ⟨w, ?_, ?_⟩
  · rw [hAt.1.memaddrs, ← hAs.1.memaddrs]; exact hdom
  · rw [hmem k hk]; exact hm2

private theorem fc_bv64_ne_6c {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : a ≠ b) :
    BitVec.ofNat 64 a ≠ BitVec.ofNat 64 b := by
  intro he
  refine h ?_
  have h1 := congrArg BitVec.toNat he
  rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h1

private theorem fc_mem_eq_of_memW_6c {F : Type} {s t : PanSemStateFiniteExact 64 F} {a : Nat}
    {w : BitVec 64} (hst : s.memory (BitVec.ofNat 64 a) = .word w)
    (heq : memW t a = memW s a) : t.memory (BitVec.ofNat 64 a) = .word w := by
  unfold memW at heq
  rw [hst] at heq
  cases hpm : t.memory (BitVec.ofNat 64 a) with
  | word w' =>
    rw [hpm] at heq
    have hw' : w' = w := BitVec.eq_of_toNat_eq heq
    rw [hw']

private theorem wordsOK_of_memW_6c {F : Type}
    {s t : PanSemStateFiniteExact 64 F} {a sz : Nat}
    (hAs : ArenaReady s) (hAt : ArenaReady t) (hw : WordsOK s (a, sz))
    (hmem : ∀ off : Nat, off + 8 ≤ sz → memW t (a + off) = memW s (a + off)) :
    WordsOK t (a, sz) := by
  obtain ⟨h1, h2, h3⟩ := hw
  refine ⟨h1, h2, fun k hk => ?_⟩
  obtain ⟨w, hdom, hm2⟩ := h3 k hk
  refine ⟨w, ?_, fc_mem_eq_of_memW_6c hm2 (hmem (8 * k) (by omega))⟩
  rw [hAt.1.memaddrs, ← hAs.1.memaddrs]; exact hdom

private theorem fc_child_cell_ne_parent_6c {F : Type}
    {s0 t : PanSemStateFiniteExact 64 F}
    (hdisj : Disj (globN s0 "ev", 280) (globN t "ev", 280))
    (hb : globN s0 "ev" + 280 ≤ 2 ^ 64)
    (hg : globN t "ev" + 280 ≤ 2 ^ 64)
    (off : Nat) (hoff : off + 8 ≤ 280) :
    BitVec.ofNat 64 (globN s0 "ev" + off) ≠ BitVec.ofNat 64 (globN t "ev" + 64) ∧
    BitVec.ofNat 64 (globN s0 "ev" + off) ≠ BitVec.ofNat 64 (globN t "ev" + 72) ∧
    BitVec.ofNat 64 (globN s0 "ev" + off) ≠ BitVec.ofNat 64 (globN t "ev" + 192) := by
  have hne : ∀ x : Nat, x = 64 ∨ x = 72 ∨ x = 192 →
      globN s0 "ev" + off ≠ globN t "ev" + x := by
    intro x hx
    unfold Disj at hdisj
    rcases hdisj with h | h | h | h <;> omega
  exact ⟨fc_bv64_ne_6c (by omega) (by omega) (hne 64 (by omega)),
    fc_bv64_ne_6c (by omega) (by omega) (hne 72 (by omega)),
    fc_bv64_ne_6c (by omega) (by omega) (hne 192 (by omega))⟩

private theorem globN_congr_6c {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (h : t.globals = s.globals) : globN t = globN s := by
  funext a; simp [globN, h]

private theorem seq_hnt_6c {F : Type} {s : PanSemStateFiniteExact 64 F} {p1 p2 : ProgHOL 64}
    (hnt : (evaluateHOLFiniteState s (.seq p1 p2)).1 ≠ some .timeOut) :
    (evaluateHOLFiniteState s p1).1 ≠ some .timeOut ∧
    ((evaluateHOLFiniteState s p1).1 = none →
      (evaluateHOLFiniteState (evaluateHOLFiniteState s p1).2 p2).1 ≠ some .timeOut) := by
  rw [evaluateHOLFiniteState_seq_line780] at hnt
  cases hr1 : evaluateHOLFiniteState s p1 with
  | mk r1 m =>
    rw [hr1] at hnt
    dsimp only at hnt
    cases r1 with
    | none =>
      dsimp only at hnt ⊢
      exact ⟨fun hbad => absurd hbad (by simp), fun _ => hnt⟩
    | some r =>
      dsimp only at hnt ⊢
      exact ⟨fun hbad => hnt hbad, fun hnone => absurd hnone (by simp)⟩

private theorem seq_step_6c {F : Type} {s : PanSemStateFiniteExact 64 F} {p1 p2 : ProgHOL 64}
    {Q R : PanSemStateFiniteExact 64 F → Prop}
    (hnt : (evaluateHOLFiniteState s (.seq p1 p2)).1 ≠ some .timeOut)
    (h1 : (∀ u, (evaluateHOLFiniteState s p1).1 ≠ some (.returned u)) ∧
      ¬ OpDispatchSpec.IsEvmErr (evaluateHOLFiniteState s p1).1 ∧
      ((evaluateHOLFiniteState s p1).1 = none → Q (evaluateHOLFiniteState s p1).2))
    (h2 : ∀ u, Q u → (evaluateHOLFiniteState u p2).1 ≠ some .timeOut →
      (∀ v, (evaluateHOLFiniteState u p2).1 ≠ some (.returned v)) ∧
      ¬ OpDispatchSpec.IsEvmErr (evaluateHOLFiniteState u p2).1 ∧
      ((evaluateHOLFiniteState u p2).1 = none → R (evaluateHOLFiniteState u p2).2)) :
    (∀ u, (evaluateHOLFiniteState s (.seq p1 p2)).1 ≠ some (.returned u)) ∧
    ¬ OpDispatchSpec.IsEvmErr (evaluateHOLFiniteState s (.seq p1 p2)).1 ∧
    ((evaluateHOLFiniteState s (.seq p1 p2)).1 = none →
      R (evaluateHOLFiniteState s (.seq p1 p2)).2) := by
  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
  cases hr1 : evaluateHOLFiniteState s p1 with
  | mk r1 m =>
    rw [hr1] at hnt h1
    dsimp only at hnt h1 ⊢
    cases r1 with
    | none =>
      dsimp only at hnt h1 ⊢
      obtain ⟨n1, e1, q1⟩ := h1
      obtain ⟨n2, e2, q2⟩ := h2 m (q1 rfl) hnt
      exact ⟨n2, e2, q2⟩
    | some r =>
      dsimp only at h1 ⊢
      obtain ⟨n1, e1, q1⟩ := h1
      exact ⟨n1, e1, fun hnone => absurd hnone (by simp)⟩

private theorem ite_hnt_6c {F : Type} {s : PanSemStateFiniteExact 64 F} {c : ExpHOL 64}
    {p1 p2 : ProgHOL 64} {w : BitVec 64}
    (hc : evalAt6c s c = some (.val (.word w)))
    (hnt : (evaluateHOLFiniteState s (.ite c p1 p2)).1 ≠ some .timeOut) :
    (w = 0 → (evaluateHOLFiniteState s p2).1 ≠ some .timeOut) ∧
    (w ≠ 0 → (evaluateHOLFiniteState s p1).1 ≠ some .timeOut) := by
  have hc' : @evalHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a)) c = some (.val (.word w)) := hc
  rw [evaluateHOLFiniteState_ite, hc'] at hnt
  dsimp only at hnt
  by_cases hw : w = 0
  · rw [if_pos hw] at hnt
    exact ⟨fun _ => hnt, fun hw' => absurd hw hw'⟩
  · rw [if_neg hw] at hnt
    exact ⟨fun hw' => absurd hw' hw, fun _ => hnt⟩

private theorem ite_step_6c {F : Type} {s : PanSemStateFiniteExact 64 F} {c : ExpHOL 64}
    {p1 p2 : ProgHOL 64} {w : BitVec 64} {Q : PanSemStateFiniteExact 64 F → Prop}
    (hc : evalAt6c s c = some (.val (.word w)))
    (h1 : w ≠ 0 → (∀ u, (evaluateHOLFiniteState s p1).1 ≠ some (.returned u)) ∧
      ¬ OpDispatchSpec.IsEvmErr (evaluateHOLFiniteState s p1).1 ∧
      ((evaluateHOLFiniteState s p1).1 = none → Q (evaluateHOLFiniteState s p1).2))
    (h2 : w = 0 → (∀ u, (evaluateHOLFiniteState s p2).1 ≠ some (.returned u)) ∧
      ¬ OpDispatchSpec.IsEvmErr (evaluateHOLFiniteState s p2).1 ∧
      ((evaluateHOLFiniteState s p2).1 = none → Q (evaluateHOLFiniteState s p2).2)) :
    (∀ u, (evaluateHOLFiniteState s (.ite c p1 p2)).1 ≠ some (.returned u)) ∧
    ¬ OpDispatchSpec.IsEvmErr (evaluateHOLFiniteState s (.ite c p1 p2)).1 ∧
    ((evaluateHOLFiniteState s (.ite c p1 p2)).1 = none →
      Q (evaluateHOLFiniteState s (.ite c p1 p2)).2) := by
  have hc' : @evalHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a)) c = some (.val (.word w)) := hc
  rw [evaluateHOLFiniteState_ite, hc']
  dsimp only
  by_cases hw : w = 0
  · rw [if_pos hw]; exact h2 hw
  · rw [if_neg hw]; exact h1 hw

private def fcErrPathInv1_6c {F : Type} (s0 t : PanSemStateFiniteExact 64 F) (S : List Nat) :
    PanSemStateFiniteExact 64 F → Prop := fun u =>
    FcBranchState s0 u S ∧ u.locals = t.locals ∧
    globN u "scratch_ptr" = globN t "scratch_ptr" ∧ globN u "ev" = globN t "ev" ∧
    evmChain u = evmChain t ∧
    OpDispatchSpec.evmR u = OpDispatchSpec.evmR t ∧
    Inside (globN s0 "ev", 280) (globN u "scratch_ptr") scratchEnd ∧
    WordsOK u (globN s0 "ev", 280) ∧
    (∀ off : Nat, off + 8 ≤ 280 → off % 8 = 0 →
      memW u (globN s0 "ev" + off) = memW t (globN s0 "ev" + off)) ∧
    (∀ ec ∈ evmChain u, ∀ o ∈ frameObjects u ec, Disj (globN s0 "ev", 280) o) ∧
    memW u (globN t "ev" + 16) = memW t (globN t "ev" + 16) ∧
    memW u (globN t "ev" + 40) = memW t (globN t "ev" + 40) ∧
    memW u (globN t "ev" + 232) = memW t (globN t "ev" + 232)

private def fcErrPathInv2_6c {F : Type} (s0 t : PanSemStateFiniteExact 64 F) (S : List Nat) :
    PanSemStateFiniteExact 64 F → Prop := fun u =>
    FcBranchState s0 u S ∧ u.locals = t.locals ∧
    globN u "scratch_ptr" = globN t "scratch_ptr" ∧ globN u "ev" = globN t "ev" ∧
    evmChain u = evmChain t ∧
    Inside (globN s0 "ev", 280) (globN u "scratch_ptr") scratchEnd ∧
    WordsOK u (globN s0 "ev", 280) ∧
    memW u (globN t "ev" + 16) = memW t (globN t "ev" + 16) ∧
    memW u (globN t "ev" + 40) = memW t (globN t "ev" + 40) ∧
    memW u (globN t "ev" + 232) = memW t (globN t "ev" + 232)

private def fcErrPathInv3_6c {F : Type} (s0 t : PanSemStateFiniteExact 64 F) (S : List Nat) :
    PanSemStateFiniteExact 64 F → Prop := fun u =>
    FcBranchState s0 u S ∧
    memW u (globN t "ev" + 16) = memW t (globN t "ev" + 16) ∧
    memW u (globN t "ev" + 232) = memW t (globN t "ev" + 232)

private theorem fcPathErr_step_6c {F : Type}
    (hSR : FcSetRetdataStepW_local) (hSP : FcStackPushStepW_sc)
    {s0 t : PanSemStateFiniteExact 64 F} {S : List Nat}
    (hBS : FcBranchState s0 t S) (hPC : FcPoppedChild s0 t S)
    (hgas : OpDispatchSpec.evmR t +
        (memW t (globN s0 "ev" + 64) + memW t (globN s0 "ev" + 192)) ≤
      OpDispatchSpec.evmR s0)
    (hgas2 : OpDispatchSpec.evmR t +
        (memW t (globN s0 "ev" + 64) + memW t (globN s0 "ev" + 192)) + 1 < 2 ^ 64)
    (hnt : (evaluateHOLFiniteState t fcPathErr).1 ≠ some .timeOut) :
    (∀ u, (evaluateHOLFiniteState t fcPathErr).1 ≠ some (.returned u)) ∧
    ¬ OpDispatchSpec.IsEvmErr (evaluateHOLFiniteState t fcPathErr).1 ∧
    ((evaluateHOLFiniteState t fcPathErr).1 = none →
      FcBranchState s0 (evaluateHOLFiniteState t fcPathErr).2 S) := by
  have hse : scratchEnd = 2965299200 := rfl
  have hbnd_child : globN s0 "ev" + 280 ≤ 2 ^ 64 := by
    have hse : scratchEnd = 2965299200 := rfl
    have h := hPC.child_scr.1.2; omega
  have hbnd_gev : globN t "ev" + 280 ≤ 2 ^ 64 :=
    (ev_head_facts_6a hBS.arena hBS.inv).1
  have hhead_mem : (globN t "ev", globN t "cur_cont") ∈ evmChain t := by
    rw [evmChain_cons]; exact List.mem_cons_self
  have hdisj : Disj (globN s0 "ev", 280) (globN t "ev", 280) :=
    hPC.child_disj_fo _ hhead_mem (globN t "ev", 280) (by simp [frameObjects])
  have hPE : fcPathErr =
      .seq (.call (some (none, none)) (ofString "rollback_child_access")
          [.var .local (ofString "child")])
        (.seq (.call (some (none, none)) (ofString "incorporate_child_on_error")
            [.var .local (ofString "child")])
          (.seq (.ite (.cmp .notEqual (.var .local (ofString "new_account_charged"))
                (.const 0#64))
                (.call (some (none, none)) (ofString "credit_state_gas_refund")
                  [.const 183600#64])
                .skip)
            (.seq (.call (some (none, none)) (ofString "set_retdata")
                [.load .one (.op .add [.var .local (ofString "child"), .const 120#64]),
                 .load .one (.op .add [.var .local (ofString "child"), .const 128#64])])
              (.call (some (none, none)) (ofString "stack_push")
                [.rstruct [.const 0#64, .const 0#64, .const 0#64, .const 0#64]])))) := rfl
  rw [hPE] at hnt ⊢
  refine seq_step_6c (Q := fcErrPathInv1_6c s0 t S) (R := fun u => FcBranchState s0 u S) hnt ?_ ?_
  · obtain ⟨hntA, _⟩ := seq_hnt_6c hnt
    obtain ⟨nA, eA, qA⟩ := rollback_child_access_step hBS hPC.child_scr hPC.rec_scr
      hPC.child_disj_ht hPC.rec_disj_ht hPC.child_disj_fix hPC.child_disj_fo
      hPC.addr_table_ok hPC.key_table_ok hntA
    refine ⟨nA, eA, fun hnone => ?_⟩
    obtain ⟨hBSu, hlocu, hscru, hevu, hchu, hRu, hinsu, hwoku, _, _, hdfou, hcellu, hchcu⟩ :=
      qA hnone
    have hcells_head := hchcu _ hhead_mem
    exact ⟨hBSu, hlocu, hscru, hevu, hchu, hRu, hinsu, hwoku, hcellu, hdfou,
      hcells_head.1, hcells_head.2.1, hcells_head.2.2⟩
  · intro u hQ hntRest
    obtain ⟨hBSu, hlocu, hscru, hevu, hchu, hRu, hinsu, hwoku, hcellu, hdfou, hc16, hc40,
      hc232⟩ := hQ
    obtain ⟨hntI, _⟩ := seq_hnt_6c hntRest
    have h64u : memW u (globN s0 "ev" + 64) = memW t (globN s0 "ev" + 64) :=
      hcellu 64 (by omega) (by omega)
    have hr_sum : OpDispatchSpec.evmR u + memW u (globN s0 "ev" + 64) ≤
        OpDispatchSpec.evmR s0 := by omega
    have hgas_sum : OpDispatchSpec.evmR u + memW u (globN s0 "ev" + 64) + 1 < 2 ^ 64 := by
      omega
    obtain ⟨nI, eI, qI⟩ := incorporate_child_on_error_fc_step hBSu hwoku hbnd_child hdfou
      hr_sum hgas_sum hntI
    refine seq_step_6c (Q := fcErrPathInv2_6c s0 t S) (R := fun u => FcBranchState s0 u S)
      hntRest ?_ ?_
    · refine ⟨nI, eI, fun hnone => ?_⟩
      obtain ⟨hBSv, hlocv, hglobv, hchv, hRv, hcellv, hcv16, hcv40, hcv232⟩ := qI hnone
      have hgp := globN_congr_6c hglobv
      refine ⟨hBSv, hlocv.trans hlocu, (congrFun hgp _).trans hscru,
        (congrFun hgp _).trans hevu, hchv.trans hchu, ?_, ?_, ?_, ?_, ?_⟩
      · rw [congrFun hgp "scratch_ptr"]; exact hinsu
      · exact wordsOK_of_memW_6c hBSu.arena hBSv.arena hwoku hcellv
      · have he1 : globN (evaluateHOLFiniteState u
            (.call (some (none, none)) (ofString "incorporate_child_on_error")
              [.var .local (ofString "child")])).2 "ev" = globN t "ev" :=
          (congrFun hgp "ev").trans hevu
        rw [he1, hevu] at hcv16
        exact hcv16.trans hc16
      · have he1 : globN (evaluateHOLFiniteState u
            (.call (some (none, none)) (ofString "incorporate_child_on_error")
              [.var .local (ofString "child")])).2 "ev" = globN t "ev" :=
          (congrFun hgp "ev").trans hevu
        rw [he1, hevu] at hcv40
        exact hcv40.trans hc40
      · have he1 : globN (evaluateHOLFiniteState u
            (.call (some (none, none)) (ofString "incorporate_child_on_error")
              [.var .local (ofString "child")])).2 "ev" = globN t "ev" :=
          (congrFun hgp "ev").trans hevu
        rw [he1, hevu] at hcv232
        exact hcv232.trans hc232
    · intro u2 hQ2 hntRest3
      obtain ⟨hBS2, hloc2, hscr2, hev2, hch2, hins2, hwok2, hc216, hc240, hc2232⟩ := hQ2
      obtain ⟨hntIte, _⟩ := seq_hnt_6c hntRest3
      have hlk_nac : u2.locals.lookup (ofString "new_account_charged") =
          some (.val (.word (BitVec.ofNat 64 (memW s0 (globN s0 "cur_cont" + 64))))) := by
        rw [hloc2]; exact hBS.locals_ok.nac_lk
      refine seq_step_6c (Q := fcErrPathInv2_6c s0 t S) (R := fun u => FcBranchState s0 u S)
        hntRest3 ?_ ?_
      · by_cases hzc : BitVec.ofNat 64 (memW s0 (globN s0 "cur_cont" + 64)) = 0#64
        · have hc : evalAt6c u2
              (.cmp .notEqual (.var .local (ofString "new_account_charged"))
                (.const 0#64)) = some (.val (.word 0#64)) := by
            simp [evalAt6c, evalHOLExact, Compiler.Encoders.Asm.wordCmpHOL, hlk_nac, hzc]
          have hskip : (∀ u, (evaluateHOLFiniteState u2 .skip).1 ≠ some (.returned u)) ∧
              ¬ OpDispatchSpec.IsEvmErr (evaluateHOLFiniteState u2 .skip).1 ∧
              ((evaluateHOLFiniteState u2 .skip).1 = none →
                fcErrPathInv2_6c s0 t S (evaluateHOLFiniteState u2 .skip).2) := by
            rw [evaluateHOLFiniteState_skip]
            refine ⟨fun u hu => absurd hu (by simp),
              by simp [OpDispatchSpec.IsEvmErr], fun _ => ?_⟩
            exact ⟨hBS2, hloc2, hscr2, hev2, hch2, hins2, hwok2, hc216, hc240, hc2232⟩
          exact ite_step_6c hc (fun h => absurd h (by simp)) (fun _ => hskip)
        · have hc : evalAt6c u2
              (.cmp .notEqual (.var .local (ofString "new_account_charged"))
                (.const 0#64)) = some (.val (.word 1#64)) := by
            simp [evalAt6c, evalHOLExact, Compiler.Encoders.Asm.wordCmpHOL, hlk_nac, hzc]
          have hntC : (evaluateHOLFiniteState u2
              (.call (some (none, none)) (ofString "credit_state_gas_refund")
                [.const 183600#64])).1 ≠ some .timeOut := by
            have hbr := ite_hnt_6c hc hntIte
            exact hbr.2 (by decide)
          obtain ⟨nC, eC, qC⟩ := credit_state_gas_refund_fc_step hBS2 hntC
          refine ite_step_6c hc (fun _ => ⟨nC, eC, fun hnone => ?_⟩)
            (fun h => absurd h (by simp))
          obtain ⟨hBSc, hlocc, hglobc, hbec, hchc, hRc, hmemc, hcc16, hcc40, hcc232⟩ :=
            qC hnone
          have hgpc := globN_congr_6c hglobc
          refine ⟨hBSc, hlocc.trans hloc2, (congrFun hgpc _).trans hscr2,
            (congrFun hgpc _).trans hev2, hchc.trans hch2, ?_, ?_, ?_, ?_, ?_⟩
          · rw [congrFun hgpc "scratch_ptr"]; exact hins2
          · refine wordsOK_of_arena_mem_6c hBS2.arena hBSc.arena hwok2 ?_
            intro k hk
            have hcell := fc_child_cell_ne_parent_6c hdisj hbnd_child hbnd_gev (8 * k) (by omega)
            rw [← hev2] at hcell
            exact hmemc _ hcell.1 hcell.2.1 hcell.2.2
          · have he1 : globN (evaluateHOLFiniteState u2
                (.call (some (none, none)) (ofString "credit_state_gas_refund")
                  [.const 183600#64])).2 "ev" = globN t "ev" :=
              (congrFun hgpc "ev").trans hev2
            rw [he1, hev2] at hcc16
            exact hcc16.trans hc216
          · have he1 : globN (evaluateHOLFiniteState u2
                (.call (some (none, none)) (ofString "credit_state_gas_refund")
                  [.const 183600#64])).2 "ev" = globN t "ev" :=
              (congrFun hgpc "ev").trans hev2
            rw [he1, hev2] at hcc40
            exact hcc40.trans hc240
          · have he1 : globN (evaluateHOLFiniteState u2
                (.call (some (none, none)) (ofString "credit_state_gas_refund")
                  [.const 183600#64])).2 "ev" = globN t "ev" :=
              (congrFun hgpc "ev").trans hev2
            rw [he1, hev2] at hcc232
            exact hcc232.trans hc2232
      · intro u3 hQ3 hntRest4
        obtain ⟨hBS3, hloc3, hscr3, hev3, hch3, hins3, hwok3, hc316, hc340, hc3323⟩ := hQ3
        obtain ⟨hntS, _⟩ := seq_hnt_6c hntRest4
        refine seq_step_6c (Q := fcErrPathInv3_6c s0 t S) (R := fun u => FcBranchState s0 u S)
          hntRest4 ?_ ?_
        · have hlk_child : u3.locals.lookup (ofString "child") =
              some (.val (.word (BitVec.ofNat 64 (globN s0 "ev")))) := by
            rw [hloc3]; exact hBS.locals_ok.child_lk
          have hp : evalAt u3
              (.load .one (.op .add [.var .local (ofString "child"), .const 120#64])) =
              some (.val (.word (BitVec.ofNat 64 (memW u3 (globN s0 "ev" + 120))))) :=
            eval_load_local_off_6c u3 hlk_child hBS3.arena.1.memaddrs hwok3 hbnd_child
              (by omega) (by omega)
          have hn : evalAt u3
              (.load .one (.op .add [.var .local (ofString "child"), .const 128#64])) =
              some (.val (.word (BitVec.ofNat 64 (memW u3 (globN s0 "ev" + 128))))) :=
            eval_load_local_off_6c u3 hlk_child hBS3.arena.1.memaddrs hwok3 hbnd_child
              (by omega) (by omega)
          obtain ⟨nS, eS, qS⟩ := hSR hBS3 hins3 hwok3 _ _ _ _ hp hn hntS
          refine ⟨nS, eS, fun hnone => ?_⟩
          obtain ⟨hBSw, hlocw, hglobw, hchw, hRw, hcw16, hcw40, hcw232⟩ := qS hnone
          have he1 : globN (evaluateHOLFiniteState u3
              (.call (some (none, none)) (ofString "set_retdata")
                [.load .one (.op .add [.var .local (ofString "child"), .const 120#64]),
                 .load .one (.op .add [.var .local (ofString "child"), .const 128#64])])).2
              "ev" = globN t "ev" := (hglobw "ev" (by decide)).trans hev3
          refine ⟨hBSw, ?_, ?_⟩
          · rw [he1, hev3] at hcw16
            exact hcw16.trans hc316
          · rw [he1, hev3] at hcw232
            exact hcw232.trans hc3323
        · intro u4 hQ4 hntP
          obtain ⟨hBS4, hc416, hc4232⟩ := hQ4
          have hev4 : globN u4 "ev" = globN t "ev" := hBS4.ev_eq.trans hBS.ev_eq.symm
          have hroom : memW u4 (globN u4 "ev" + 16) + 1 ≤ memW u4 (globN u4 "ev" + 232) := by
            rw [hev4, hc416, hc4232]
            exact hPC.parent_room
          have hv : evalAt u4
              (.rstruct [.const 0#64, .const 0#64, .const 0#64, .const 0#64]) =
              some (.rStruct [.val (.word 0#64), .val (.word 0#64), .val (.word 0#64),
                .val (.word 0#64)]) := by
            simp [evalAt, evalHOLExact, evalListHOLExact]
          have hsh : shapeEqHOL (.comb [.one, .one, .one, .one])
              (shapeOfHOLExact (.rStruct [.val (.word 0#64), .val (.word 0#64),
                .val (.word 0#64), .val (.word 0#64)])) = true := by
            simp only [shapeOfHOLExact, shapeEqHOL, List.map]
            simp [shapeEqHOL.shapeEqListHOL, shapeEqHOL]
          obtain ⟨nP, eP, qP⟩ := hSP hBS4 hroom _ _ hv hsh hntP
          exact ⟨nP, eP, fun hn => (qP hn).1⟩

private def fcOkPathInv_6c {F : Type} (s0 t : PanSemStateFiniteExact 64 F) :
    PanSemStateFiniteExact 64 F → Prop := fun u =>
    ∃ S', FcBranchState s0 u S' ∧ u.locals = t.locals ∧
      GlobalsKept ["heap_ptr"] t u ∧
      evmChain u = evmChain t ∧
      Inside (globN s0 "ev", 280) (globN u "scratch_ptr") scratchEnd ∧
      WordsOK u (globN s0 "ev", 280) ∧
      memW u (globN u "ev" + 16) = memW t (globN t "ev" + 16) ∧
      memW u (globN u "ev" + 40) = memW t (globN t "ev" + 40) ∧
      memW u (globN u "ev" + 232) = memW t (globN t "ev" + 232)

private theorem fcPathNe2Ok_step_6c {F : Type}
    (hSR : FcSetRetdataStepW_local) (hSP : FcStackPushStepW_sc) (hIS : FcIncorpSuccessStepW')
    {s0 t : PanSemStateFiniteExact 64 F} {S : List Nat}
    (hBS : FcBranchState s0 t S) (hPC : FcPoppedChild s0 t S) (hLSD : FcLogsSelfDisj s0 t)
    (hgas : OpDispatchSpec.evmR t +
        (memW t (globN s0 "ev" + 64) + memW t (globN s0 "ev" + 192)) ≤
      OpDispatchSpec.evmR s0)
    (hgas2 : OpDispatchSpec.evmR t +
        (memW t (globN s0 "ev" + 64) + memW t (globN s0 "ev" + 192)) + 1 < 2 ^ 64)
    (hnt : (evaluateHOLFiniteState t fcPathNe2Ok).1 ≠ some .timeOut) :
    (∀ u, (evaluateHOLFiniteState t fcPathNe2Ok).1 ≠ some (.returned u)) ∧
    ¬ OpDispatchSpec.IsEvmErr (evaluateHOLFiniteState t fcPathNe2Ok).1 ∧
    ((evaluateHOLFiniteState t fcPathNe2Ok).1 = none →
      ∃ S'', FcBranchState s0 (evaluateHOLFiniteState t fcPathNe2Ok).2 S'') := by
  have hbnd_child : globN s0 "ev" + 280 ≤ 2 ^ 64 := by
    have hse : scratchEnd = 2965299200 := rfl
    have h := hPC.child_scr.1.2; omega
  have hPE : fcPathNe2Ok =
      .seq (.call (some (none, none)) (ofString "incorporate_child_on_success")
          [.var .local (ofString "child")])
        (.seq (.call (some (none, none)) (ofString "set_retdata")
            [.load .one (.op .add [.var .local (ofString "child"), .const 120#64]),
             .load .one (.op .add [.var .local (ofString "child"), .const 128#64])])
          (.call (some (none, none)) (ofString "stack_push")
            [.rstruct [.const 1#64, .const 0#64, .const 0#64, .const 0#64]])) := rfl
  rw [hPE] at hnt ⊢
  refine seq_step_6c (Q := fcOkPathInv_6c s0 t) (R := fun u => ∃ S'', FcBranchState s0 u S'')
    hnt ?_ ?_
  · obtain ⟨hntI, _⟩ := seq_hnt_6c hnt
    obtain ⟨nI, eI, qI⟩ := hIS hBS hPC hLSD hgas hgas2 hntI
    refine ⟨nI, eI, fun hnone => ?_⟩
    obtain ⟨S', hBSi, hloci, hglobi, hchi, _, hinsi, hwoki, hci16, hci40, hci232⟩ := qI hnone
    exact ⟨S', hBSi, hloci, hglobi, hchi, hinsi, hwoki, hci16, hci40, hci232⟩
  · intro u hQ hntRest
    obtain ⟨S', hBS', hloc', hglob', hch', hins', hwok', hc16', hc40', hc232'⟩ := hQ
    obtain ⟨hntS, _⟩ := seq_hnt_6c hntRest
    refine seq_step_6c (Q := fun v => FcBranchState s0 v S' ∧ v.locals = t.locals ∧
        memW v (globN v "ev" + 16) = memW t (globN t "ev" + 16) ∧
        memW v (globN v "ev" + 232) = memW t (globN t "ev" + 232))
      (R := fun v => ∃ S'', FcBranchState s0 v S'') hntRest ?_ ?_
    · have hlk_child : u.locals.lookup (ofString "child") =
          some (.val (.word (BitVec.ofNat 64 (globN s0 "ev")))) := by
        rw [hloc']; exact hBS.locals_ok.child_lk
      have hp : evalAt u
          (.load .one (.op .add [.var .local (ofString "child"), .const 120#64])) =
          some (.val (.word (BitVec.ofNat 64 (memW u (globN s0 "ev" + 120))))) :=
        eval_load_local_off_6c u hlk_child hBS'.arena.1.memaddrs hwok' hbnd_child
          (by omega) (by omega)
      have hn : evalAt u
          (.load .one (.op .add [.var .local (ofString "child"), .const 128#64])) =
          some (.val (.word (BitVec.ofNat 64 (memW u (globN s0 "ev" + 128))))) :=
        eval_load_local_off_6c u hlk_child hBS'.arena.1.memaddrs hwok' hbnd_child
          (by omega) (by omega)
      obtain ⟨nS, eS, qS⟩ := hSR hBS' hins' hwok' _ _ _ _ hp hn hntS
      refine ⟨nS, eS, fun hnone => ?_⟩
      obtain ⟨hBSw, hlocw, hglobw, hchw, hRw, hcw16, hcw40, hcw232⟩ := qS hnone
      exact ⟨hBSw, hlocw.trans hloc', hcw16.trans hc16', hcw232.trans hc232'⟩
    · intro u4 hQ4 hntP
      obtain ⟨hBS4, hloc4, hc416, hc4232⟩ := hQ4
      have hroom : memW u4 (globN u4 "ev" + 16) + 1 ≤ memW u4 (globN u4 "ev" + 232) := by
        rw [hc416, hc4232]
        exact hPC.parent_room
      have hv : evalAt u4
          (.rstruct [.const 1#64, .const 0#64, .const 0#64, .const 0#64]) =
          some (.rStruct [.val (.word 1#64), .val (.word 0#64), .val (.word 0#64),
            .val (.word 0#64)]) := by
        simp [evalAt, evalHOLExact, evalListHOLExact]
      have hsh : shapeEqHOL (.comb [.one, .one, .one, .one])
          (shapeOfHOLExact (.rStruct [.val (.word 1#64), .val (.word 0#64),
            .val (.word 0#64), .val (.word 0#64)])) = true := by
        simp only [shapeOfHOLExact, shapeEqHOL, List.map]
        simp [shapeEqHOL.shapeEqListHOL, shapeEqHOL]
      obtain ⟨nP, eP, qP⟩ := hSP hBS4 hroom _ _ hv hsh hntP
      exact ⟨nP, eP, fun hn => ⟨S', (qP hn).1⟩⟩

private theorem fcPathKind2Ok_step_6c {F : Type}
    (hSR : FcSetRetdataStepW_local) (hA2 : FcAddrToU256StepW_sc) (hIS : FcIncorpSuccessStepW')
    {s0 t : PanSemStateFiniteExact 64 F} {S : List Nat}
    (hBS : FcBranchState s0 t S) (hPC : FcPoppedChild s0 t S) (hLSD : FcLogsSelfDisj s0 t)
    (hlk_empty : ∃ ew, t.locals.lookup (ofString "empty") = some (.val (.word ew)))
    (hgas : OpDispatchSpec.evmR t +
        (memW t (globN s0 "ev" + 64) + memW t (globN s0 "ev" + 192)) ≤
      OpDispatchSpec.evmR s0)
    (hgas2 : OpDispatchSpec.evmR t +
        (memW t (globN s0 "ev" + 64) + memW t (globN s0 "ev" + 192)) + 1 < 2 ^ 64)
    (hnt : (evaluateHOLFiniteState t fcPathKind2Ok).1 ≠ some .timeOut) :
    (∀ u, (evaluateHOLFiniteState t fcPathKind2Ok).1 ≠ some (.returned u)) ∧
    ¬ OpDispatchSpec.IsEvmErr (evaluateHOLFiniteState t fcPathKind2Ok).1 ∧
    ((evaluateHOLFiniteState t fcPathKind2Ok).1 = none →
      ∃ S'', FcBranchState s0 (evaluateHOLFiniteState t fcPathKind2Ok).2 S'') := by
  have hPE : fcPathKind2Ok =
      .seq (.call (some (none, none)) (ofString "incorporate_child_on_success")
          [.var .local (ofString "child")])
        (.seq (.call (some (none, none)) (ofString "set_retdata")
            [.var .local (ofString "empty"), .const 0#64])
          (.decCall (ofString "av") (.comb [.one, .one, .one, .one]) (ofString "address_to_u256")
            [.var .local (ofString "contract_address")]
            (.call (some (none, none)) (ofString "stack_push") [.var .local (ofString "av")]))) := rfl
  rw [hPE] at hnt ⊢
  refine seq_step_6c (Q := fcOkPathInv_6c s0 t) (R := fun u => ∃ S'', FcBranchState s0 u S'')
    hnt ?_ ?_
  · obtain ⟨hntI, _⟩ := seq_hnt_6c hnt
    obtain ⟨nI, eI, qI⟩ := hIS hBS hPC hLSD hgas hgas2 hntI
    refine ⟨nI, eI, fun hnone => ?_⟩
    obtain ⟨S', hBSi, hloci, hglobi, hchi, _, hinsi, hwoki, hci16, hci40, hci232⟩ := qI hnone
    exact ⟨S', hBSi, hloci, hglobi, hchi, hinsi, hwoki, hci16, hci40, hci232⟩
  · intro u hQ hntRest
    obtain ⟨S', hBS', hloc', hglob', hch', hins', hwok', hc16', hc40', hc232'⟩ := hQ
    obtain ⟨hntS, _⟩ := seq_hnt_6c hntRest
    refine seq_step_6c (Q := fun v => FcBranchState s0 v S' ∧ v.locals = t.locals ∧
        memW v (globN v "ev" + 16) = memW t (globN t "ev" + 16) ∧
        memW v (globN v "ev" + 232) = memW t (globN t "ev" + 232))
      (R := fun v => ∃ S'', FcBranchState s0 v S'') hntRest ?_ ?_
    · obtain ⟨ew, hlk_ew⟩ := hlk_empty
      have hlk_empty' : u.locals.lookup (ofString "empty") = some (.val (.word ew)) := by
        rw [hloc']; exact hlk_ew
      have hp : evalAt u (.var .local (ofString "empty")) = some (.val (.word ew)) :=
        eval_var_local_word_6c u hlk_empty'
      have hn : evalAt u (.const 0#64) = some (.val (.word 0#64)) := rfl
      obtain ⟨nS, eS, qS⟩ := hSR hBS' hins' hwok' _ _ _ _ hp hn hntS
      refine ⟨nS, eS, fun hnone => ?_⟩
      obtain ⟨hBSw, hlocw, hglobw, hchw, hRw, hcw16, hcw40, hcw232⟩ := qS hnone
      exact ⟨hBSw, hlocw.trans hloc', hcw16.trans hc16', hcw232.trans hc232'⟩
    · intro u4 hQ4 hntP
      obtain ⟨hBS4, hloc4, hc416, hc4232⟩ := hQ4
      have hroom : memW u4 (globN u4 "ev" + 16) + 1 ≤ memW u4 (globN u4 "ev" + 232) := by
        rw [hc416, hc4232]
        exact hPC.parent_room
      have hlk_ca : u4.locals.lookup (ofString "contract_address") =
          some (.val (.word (BitVec.ofNat 64 (memW s0 (globN s0 "cur_cont" + 88))))) := by
        rw [hloc4]; exact hBS.locals_ok.ca_lk
      have hca : evalAt u4 (.var .local (ofString "contract_address")) =
          some (.val (.word (BitVec.ofNat 64 (memW s0 (globN s0 "cur_cont" + 88))))) :=
        eval_var_local_word_6c u4 hlk_ca
      obtain ⟨nA, eA, qA⟩ := hA2 hBS4 hroom _ _ hca hntP
      exact ⟨nA, eA, fun hn => ⟨S', (qA hn).1⟩⟩

def FcBranchWalk' : Prop :=
  ∀ {F : Type} {s0 st : PanSemStateFiniteExact 64 F} {S : List Nat},
    FcBranchState s0 st S → FcPoppedChild s0 st S → FcLogsSelfDisj s0 st →
    OpDispatchSpec.evmR st + (memW st (globN s0 "ev" + 64) + memW st (globN s0 "ev" + 192)) ≤
      OpDispatchSpec.evmR s0 →
    OpDispatchSpec.evmR st + (memW st (globN s0 "ev" + 64) + memW st (globN s0 "ev" + 192)) + 1 <
      2 ^ 64 →
    (evaluateHOLFiniteState st (.seq fcBranches fcCleanup)).1 ≠ some .timeOut →
    FinishPost s0 (evaluateHOLFiniteState st (.seq fcBranches fcCleanup)).1
      (evaluateHOLFiniteState st (.seq fcBranches fcCleanup)).2

theorem fcBranchWalk'_of_leaves (hSR : FcSetRetdataStepW_local) (hSP : FcStackPushStepW_sc)
    (hA2 : FcAddrToU256StepW_sc) (hIS : FcIncorpSuccessStepW') (hMT : FcMinTailStepW_sc) :
    FcBranchWalk' := by
  intro F s0 st S hBS hPC hLSD hgas hgas2 hnt
  have hbnd_child : globN s0 "ev" + 280 ≤ 2 ^ 64 := by
    have hse : scratchEnd = 2965299200 := rfl
    have h := hPC.child_scr.1.2; omega
  have hnr_call : ∀ (fn : MlS) (args : List (ExpHOL 64)) {F : Type}
      (t : PanSemStateFiniteExact 64 F) (u : ValueHOL 64),
      (evaluateHOLFiniteState t (.call (some (none, none)) fn args)).1 ≠
        some (.returned u) := by
    intro fn args _ t u
    exact call0_ne_returned_fc t fn args u
  have hnr_skip : ∀ {F : Type} (t : PanSemStateFiniteExact 64 F) (u : ValueHOL 64),
      (evaluateHOLFiniteState t ProgHOL.skip).1 ≠ some (.returned u) := by
    intro t u; simp [evaluateHOLFiniteState_skip]
  have hnr_pathErr : ∀ {F : Type} (t : PanSemStateFiniteExact 64 F) (u : ValueHOL 64),
      (evaluateHOLFiniteState t fcPathErr).1 ≠ some (.returned u) :=
    fun t u => seq_ne_returned (hnr_call _ _) (seq_ne_returned (hnr_call _ _)
      (seq_ne_returned (ite_ne_returned_fc (hnr_call _ _) hnr_skip)
        (seq_ne_returned (hnr_call _ _) (hnr_call _ _)))) t u
  have hnr_kind2 : ∀ {F : Type} (t : PanSemStateFiniteExact 64 F) (u : ValueHOL 64),
      (evaluateHOLFiniteState t fcPathKind2Ok).1 ≠ some (.returned u) :=
    fun t u => seq_ne_returned (hnr_call _ _) (seq_ne_returned (hnr_call _ _)
      (decCall_ne_returned_fc (hnr_call _ _))) t u
  have hnr_ne2ok : ∀ {F : Type} (t : PanSemStateFiniteExact 64 F) (u : ValueHOL 64),
      (evaluateHOLFiniteState t fcPathNe2Ok).1 ≠ some (.returned u) :=
    fun t u => seq_ne_returned (hnr_call _ _) (seq_ne_returned (hnr_call _ _)
      (hnr_call _ _)) t u
  have hnr_minTail : ∀ {F : Type} (t : PanSemStateFiniteExact 64 F) (u : ValueHOL 64),
      (evaluateHOLFiniteState t fcMinTail).1 ≠ some (.returned u) :=
    fun t u => decCall_ne_returned_fc
      (ite_ne_returned_fc (hnr_call _ _) hnr_skip) t u
  rw [fcBranches_eq] at hnt ⊢
  have hlk_kind : st.locals.lookup (ofString "kind") =
      some (.val (.word (BitVec.ofNat 64 (memW s0 (globN s0 "cur_cont" + 16))))) :=
    hBS.locals_ok.kind_lk
  have hkind : evalAt6c st (.var .local (ofString "kind")) =
      some (.val (.word (BitVec.ofNat 64 (memW s0 (globN s0 "cur_cont" + 16))))) :=
    eval_var_local_word_6c st hlk_kind
  have hc2 : evalAt6c st (.const 2#64) = some (.val (.word 2#64)) := rfl
  have hc_kind : evalAt6c st (.cmp .equal (.var .local (ofString "kind")) (.const 2#64)) =
      some (.val (.word (if (BitVec.ofNat 64 (memW s0 (globN s0 "cur_cont" + 16))) = 2#64
        then 1#64 else 0#64))) :=
    eval_cmp_equal_word_6c st _ _ _ _ hkind hc2
  refine seq_finishPost
    (fun u => ite_ne_returned_fc (dec_ne_returned_fc (ite_ne_returned_fc hnr_pathErr hnr_kind2))
      (seq_ne_returned (ite_ne_returned_fc hnr_pathErr hnr_ne2ok) hnr_minTail) st u) ?_ hnt
  intro hntB
  have hkind2arm : (if (BitVec.ofNat 64 (memW s0 (globN s0 "cur_cont" + 16))) = 2#64
      then 1#64 else 0#64) ≠ 0 →
      (∀ u, (evaluateHOLFiniteState st
          (.dec (ofString "empty") .one (.var .global (ofString "evm_empty"))
            (.ite (.cmp .notEqual
                (.load .one (.op .add [.var .local (ofString "child"), .const 160#64]))
                (.const 0#64))
              fcPathErr fcPathKind2Ok))).1 ≠ some (.returned u)) ∧
      ¬ OpDispatchSpec.IsEvmErr (evaluateHOLFiniteState st
          (.dec (ofString "empty") .one (.var .global (ofString "evm_empty"))
            (.ite (.cmp .notEqual
                (.load .one (.op .add [.var .local (ofString "child"), .const 160#64]))
                (.const 0#64))
              fcPathErr fcPathKind2Ok))).1 ∧
      ((evaluateHOLFiniteState st
          (.dec (ofString "empty") .one (.var .global (ofString "evm_empty"))
            (.ite (.cmp .notEqual
                (.load .one (.op .add [.var .local (ofString "child"), .const 160#64]))
                (.const 0#64))
              fcPathErr fcPathKind2Ok))).1 = none →
        ∃ S'', FcBranchState s0 (evaluateHOLFiniteState st
          (.dec (ofString "empty") .one (.var .global (ofString "evm_empty"))
            (.ite (.cmp .notEqual
                (.load .one (.op .add [.var .local (ofString "child"), .const 160#64]))
                (.const 0#64))
              fcPathErr fcPathKind2Ok))).2 S'') := by
    intro hw
    have hntDec : (evaluateHOLFiniteState st
        (.dec (ofString "empty") .one (.var .global (ofString "evm_empty"))
          (.ite (.cmp .notEqual
              (.load .one (.op .add [.var .local (ofString "child"), .const 160#64]))
              (.const 0#64))
            fcPathErr fcPathKind2Ok))).1 ≠ some .timeOut :=
      (ite_hnt_6c hc_kind hntB).2 hw
    obtain ⟨ew, hew⟩ := hBS.arena.2.2.2.2.2.2.2.2.2 "evm_empty" (by decide)
    have hev : evalAt6c st (.var .global (ofString "evm_empty")) =
        some (.val (.word ew)) :=
      eval_var_global_word_6c st hew
    have hsh : shapeEqHOL .one (shapeOfHOLExact (.val (.word ew))) = true := by
      simp [shapeEqHOL, shapeOfHOLExact]
    have hBS' : FcBranchState s0
        (setVarHOLFinite (ofString "empty") (.val (.word ew)) st) S :=
      fcBranchState_setVar_6c hBS (ofString "empty") (.val (.word ew))
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
    have hPC' : FcPoppedChild s0
        (setVarHOLFinite (ofString "empty") (.val (.word ew)) st) S :=
      fcPoppedChild_setVar_6c hPC (ofString "empty") (.val (.word ew))
    have hLSD' : FcLogsSelfDisj s0
        (setVarHOLFinite (ofString "empty") (.val (.word ew)) st) :=
      fcLogsSelfDisj_setVar hLSD (ofString "empty") (.val (.word ew))
    have hlk_empty : ∃ ew2, (setVarHOLFinite (ofString "empty") (.val (.word ew)) st).locals.lookup
        (ofString "empty") = some (.val (.word ew2)) := by
      refine ⟨ew, ?_⟩
      simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hbr : setVarHOLFinite (ofString "empty") (.val (.word ew)) st =
        { st with
          locals := (setVarHOLFinite (ofString "empty") (.val (.word ew)) st).locals
          clock := st.clock } := rfl
    have hevR' : OpDispatchSpec.evmR
        (setVarHOLFinite (ofString "empty") (.val (.word ew)) st) =
        OpDispatchSpec.evmR st := by
      rw [hbr]; exact evmR_lc_fc st _ st.clock
    have hmw' : ∀ a, memW (setVarHOLFinite (ofString "empty") (.val (.word ew)) st) a =
        memW st a := fun _ => rfl
    have hgas' : OpDispatchSpec.evmR
          (setVarHOLFinite (ofString "empty") (.val (.word ew)) st) +
        (memW (setVarHOLFinite (ofString "empty") (.val (.word ew)) st) (globN s0 "ev" + 64) +
          memW (setVarHOLFinite (ofString "empty") (.val (.word ew)) st)
            (globN s0 "ev" + 192)) ≤
      OpDispatchSpec.evmR s0 := by
      rw [hevR', hmw', hmw']; exact hgas
    have hgas2' : OpDispatchSpec.evmR
          (setVarHOLFinite (ofString "empty") (.val (.word ew)) st) +
        (memW (setVarHOLFinite (ofString "empty") (.val (.word ew)) st) (globN s0 "ev" + 64) +
          memW (setVarHOLFinite (ofString "empty") (.val (.word ew)) st)
            (globN s0 "ev" + 192)) + 1 < 2 ^ 64 := by
      rw [hevR', hmw', hmw']; exact hgas2
    have hev' : @evalHOLExact 64 F _ st.toExact
        (fun a => Classical.propDecidable (st.memaddrs a))
        (.var .global (ofString "evm_empty")) = some (.val (.word ew)) := hev
    have hntBody : (evaluateHOLFiniteState
          (setVarHOLFinite (ofString "empty") (.val (.word ew)) st)
          (.ite (.cmp .notEqual
              (.load .one (.op .add [.var .local (ofString "child"), .const 160#64]))
              (.const 0#64))
            fcPathErr fcPathKind2Ok)).1 ≠ some .timeOut := by
      rw [evaluateHOLFiniteState_dec_total] at hntDec
      dsimp only at hntDec
      rw [hev'] at hntDec
      dsimp only at hntDec
      rw [if_pos hsh] at hntDec
      dsimp only at hntDec
      exact hntDec
    have hlk_child' : (setVarHOLFinite (ofString "empty") (.val (.word ew)) st).locals.lookup
        (ofString "child") = some (.val (.word (BitVec.ofNat 64 (globN s0 "ev")))) :=
      hBS'.locals_ok.child_lk
    have hcond : evalAt6c (setVarHOLFinite (ofString "empty") (.val (.word ew)) st)
        (.load .one (.op .add [.var .local (ofString "child"), .const 160#64])) =
        some (.val (.word (BitVec.ofNat 64
          (memW (setVarHOLFinite (ofString "empty") (.val (.word ew)) st)
            (globN s0 "ev" + 160))))) :=
      eval_load_local_off_6c _ hlk_child' hBS'.arena.1.memaddrs hPC'.child_scr.2 hbnd_child
        (by omega) (by omega)
    have hbody : (∀ u, (evaluateHOLFiniteState
            (setVarHOLFinite (ofString "empty") (.val (.word ew)) st)
            (.ite (.cmp .notEqual
                (.load .one (.op .add [.var .local (ofString "child"), .const 160#64]))
                (.const 0#64))
              fcPathErr fcPathKind2Ok)).1 ≠ some (.returned u)) ∧
        ¬ OpDispatchSpec.IsEvmErr (evaluateHOLFiniteState
            (setVarHOLFinite (ofString "empty") (.val (.word ew)) st)
            (.ite (.cmp .notEqual
                (.load .one (.op .add [.var .local (ofString "child"), .const 160#64]))
                (.const 0#64))
              fcPathErr fcPathKind2Ok)).1 ∧
        ((evaluateHOLFiniteState
            (setVarHOLFinite (ofString "empty") (.val (.word ew)) st)
            (.ite (.cmp .notEqual
                (.load .one (.op .add [.var .local (ofString "child"), .const 160#64]))
                (.const 0#64))
              fcPathErr fcPathKind2Ok)).1 = none →
          ∃ S'', FcBranchState s0 (evaluateHOLFiniteState
              (setVarHOLFinite (ofString "empty") (.val (.word ew)) st)
              (.ite (.cmp .notEqual
                  (.load .one (.op .add [.var .local (ofString "child"), .const 160#64]))
                  (.const 0#64))
                fcPathErr fcPathKind2Ok)).2 S'') := by
      have hcI : evalAt6c (setVarHOLFinite (ofString "empty") (.val (.word ew)) st)
          (.cmp .notEqual
              (.load .one (.op .add [.var .local (ofString "child"), .const 160#64]))
              (.const 0#64)) =
          some (.val (.word (if (BitVec.ofNat 64
              (memW (setVarHOLFinite (ofString "empty") (.val (.word ew)) st)
                (globN s0 "ev" + 160))) ≠ 0#64 then 1#64 else 0#64))) :=
        eval_cmp_notEqual_word_6c _ _ _ _ _ hcond rfl
      refine ite_step_6c (Q := fun post => ∃ S'', FcBranchState s0 post S'') hcI
        (fun hw2 => ?_) (fun hw2 => ?_)
      · have hntE := (ite_hnt_6c hcI hntBody).2 hw2
        obtain ⟨nE, eE, qE⟩ := fcPathErr_step_6c hSR hSP hBS' hPC' hgas' hgas2' hntE
        exact ⟨nE, eE, fun hn => ⟨S, qE hn⟩⟩
      · have hntK := (ite_hnt_6c hcI hntBody).1 hw2
        exact fcPathKind2Ok_step_6c hSR hA2 hIS hBS' hPC' hLSD' hlk_empty hgas' hgas2' hntK
    refine ⟨dec_ne_returned_fc
        (ite_ne_returned_fc hnr_pathErr hnr_kind2) st, ?_, ?_⟩
    · rw [evaluateHOLFiniteState_dec_total]
      dsimp only
      rw [hev']
      dsimp only
      rw [if_pos hsh]
      dsimp only
      exact hbody.2.1
    · intro hnone
      rw [evaluateHOLFiniteState_dec_total] at hnone
      dsimp only at hnone
      rw [hev'] at hnone
      dsimp only at hnone
      rw [if_pos hsh] at hnone
      dsimp only at hnone
      rw [evaluateHOLFiniteState_dec_total]
      dsimp only
      rw [hev']
      dsimp only
      rw [if_pos hsh]
      dsimp only
      obtain ⟨S'', hBSb⟩ := hbody.2.2 hnone
      refine ⟨S'', fcBranchState_congr_locals_clock _ _ hBSb ?_⟩
      exact fcEntryLocals_resVarEq (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) hBSb.locals_ok
  have hne2arm : (if (BitVec.ofNat 64 (memW s0 (globN s0 "cur_cont" + 16))) = 2#64
      then 1#64 else 0#64) = 0 →
      (∀ u, (evaluateHOLFiniteState st
          (.seq
            (.ite (.cmp .notEqual
                (.load .one (.op .add [.var .local (ofString "child"), .const 160#64]))
                  (.const 0#64))
              fcPathErr fcPathNe2Ok)
            fcMinTail)).1 ≠ some (.returned u)) ∧
      ¬ OpDispatchSpec.IsEvmErr (evaluateHOLFiniteState st
          (.seq
            (.ite (.cmp .notEqual
                (.load .one (.op .add [.var .local (ofString "child"), .const 160#64]))
                  (.const 0#64))
              fcPathErr fcPathNe2Ok)
            fcMinTail)).1 ∧
      ((evaluateHOLFiniteState st
          (.seq
            (.ite (.cmp .notEqual
                (.load .one (.op .add [.var .local (ofString "child"), .const 160#64]))
                  (.const 0#64))
              fcPathErr fcPathNe2Ok)
            fcMinTail)).1 = none →
        ∃ S'', FcBranchState s0 (evaluateHOLFiniteState st
          (.seq
            (.ite (.cmp .notEqual
                (.load .one (.op .add [.var .local (ofString "child"), .const 160#64]))
                  (.const 0#64))
              fcPathErr fcPathNe2Ok)
            fcMinTail)).2 S'') := by
    intro hw
    have hntArm : (evaluateHOLFiniteState st
        (.seq
          (.ite (.cmp .notEqual
              (.load .one (.op .add [.var .local (ofString "child"), .const 160#64]))
              (.const 0#64))
            fcPathErr fcPathNe2Ok)
          fcMinTail)).1 ≠ some .timeOut :=
      (ite_hnt_6c hc_kind hntB).1 hw
    obtain ⟨hntIte, _⟩ := seq_hnt_6c hntArm
    have hlk_child : st.locals.lookup (ofString "child") =
        some (.val (.word (BitVec.ofNat 64 (globN s0 "ev")))) :=
      hBS.locals_ok.child_lk
    have hcond : evalAt6c st
        (.load .one (.op .add [.var .local (ofString "child"), .const 160#64])) =
        some (.val (.word (BitVec.ofNat 64 (memW st (globN s0 "ev" + 160))))) :=
      eval_load_local_off_6c st hlk_child hBS.arena.1.memaddrs hPC.child_scr.2 hbnd_child
        (by omega) (by omega)
    have hcI : evalAt6c st
        (.cmp .notEqual
            (.load .one (.op .add [.var .local (ofString "child"), .const 160#64]))
            (.const 0#64)) =
        some (.val (.word (if (BitVec.ofNat 64 (memW st (globN s0 "ev" + 160))) ≠ 0#64
          then 1#64 else 0#64))) :=
      eval_cmp_notEqual_word_6c _ _ _ _ _ hcond rfl
    refine seq_step_6c (Q := fun u => ∃ S'', FcBranchState s0 u S'')
      (R := fun u => ∃ S'', FcBranchState s0 u S'') hntArm ?_ ?_
    · refine ite_step_6c (Q := fun post => ∃ S'', FcBranchState s0 post S'') hcI
        (fun hw2 => ?_) (fun hw2 => ?_)
      · have hntE := (ite_hnt_6c hcI hntIte).2 hw2
        obtain ⟨nE, eE, qE⟩ := fcPathErr_step_6c hSR hSP hBS hPC hgas hgas2 hntE
        exact ⟨nE, eE, fun hn => ⟨S, qE hn⟩⟩
      · have hntK := (ite_hnt_6c hcI hntIte).1 hw2
        exact fcPathNe2Ok_step_6c hSR hSP hIS hBS hPC hLSD hgas hgas2 hntK
    · intro u hQ hntMT
      obtain ⟨S'', hBS''⟩ := hQ
      have hhead_u : (globN u "ev", globN u "cur_cont") ∈ evmChain u := by
        rw [evmChain_cons]; exact List.mem_cons_self
      have hhead_st : (globN st "ev", globN st "cur_cont") ∈ evmChain st := by
        rw [evmChain_cons]; exact List.mem_cons_self
      have hev_u : globN u "ev" = globN st "ev" := hBS''.ev_eq.trans hBS.ev_eq.symm
      have hc40_u : memW u (globN u "ev" + 40) = memW s0 (globN u "ev" + 40) :=
        (hBS''.cells _ hhead_u).2.2.1
      have hc40_st : memW st (globN st "ev" + 40) = memW s0 (globN st "ev" + 40) :=
        (hBS.cells _ hhead_st).2.2.1
      have hmid : memW s0 (globN u "ev" + 40) = memW s0 (globN st "ev" + 40) := by
        rw [hev_u]
      have heu40 : memW u (globN u "ev" + 40) = memW st (globN st "ev" + 40) :=
        hc40_u.trans (hmid.trans hc40_st.symm)
      have hne2 : memW s0 (globN s0 "cur_cont" + 16) ≠ 2 := by
        intro h2
        rw [h2] at hw
        have h2v : BitVec.ofNat 64 2 = 2#64 := rfl
        rw [h2v] at hw
        simp at hw
      have hwin : memW s0 (globN s0 "cur_cont" + 80) = 0 ∨
          memW s0 (globN s0 "cur_cont" + 72) + memW s0 (globN s0 "cur_cont" + 80) ≤
            memW u (globN u "ev" + 40) := by
        rcases hPC.out_win_ok hne2 with h0 | hle
        · exact Or.inl h0
        · exact Or.inr (hle.trans (Nat.le_of_eq heu40.symm))
      obtain ⟨nM, eM, qM⟩ := hMT hBS'' hwin hntMT
      exact ⟨nM, eM, fun hn => ⟨S'', (qM hn).1⟩⟩
  have htriple : (∀ u, (evaluateHOLFiniteState st
          (.ite (.cmp .equal (.var .local (ofString "kind")) (.const 2#64))
            (.dec (ofString "empty") .one (.var .global (ofString "evm_empty"))
              (.ite (.cmp .notEqual
                  (.load .one (.op .add [.var .local (ofString "child"), .const 160#64]))
                  (.const 0#64))
                fcPathErr fcPathKind2Ok))
            (.seq
              (.ite (.cmp .notEqual
                  (.load .one (.op .add [.var .local (ofString "child"), .const 160#64]))
                  (.const 0#64))
                fcPathErr fcPathNe2Ok)
              fcMinTail))).1 ≠ some (.returned u)) ∧
      ¬ OpDispatchSpec.IsEvmErr (evaluateHOLFiniteState st
          (.ite (.cmp .equal (.var .local (ofString "kind")) (.const 2#64))
            (.dec (ofString "empty") .one (.var .global (ofString "evm_empty"))
              (.ite (.cmp .notEqual
                  (.load .one (.op .add [.var .local (ofString "child"), .const 160#64]))
                  (.const 0#64))
                fcPathErr fcPathKind2Ok))
            (.seq
              (.ite (.cmp .notEqual
                  (.load .one (.op .add [.var .local (ofString "child"), .const 160#64]))
                  (.const 0#64))
                fcPathErr fcPathNe2Ok)
              fcMinTail))).1 ∧
      ((evaluateHOLFiniteState st
          (.ite (.cmp .equal (.var .local (ofString "kind")) (.const 2#64))
            (.dec (ofString "empty") .one (.var .global (ofString "evm_empty"))
              (.ite (.cmp .notEqual
                  (.load .one (.op .add [.var .local (ofString "child"), .const 160#64]))
                  (.const 0#64))
                fcPathErr fcPathKind2Ok))
            (.seq
              (.ite (.cmp .notEqual
                  (.load .one (.op .add [.var .local (ofString "child"), .const 160#64]))
                  (.const 0#64))
                fcPathErr fcPathNe2Ok)
              fcMinTail))).1 = none →
        ∃ S'', FcBranchState s0 (evaluateHOLFiniteState st
          (.ite (.cmp .equal (.var .local (ofString "kind")) (.const 2#64))
            (.dec (ofString "empty") .one (.var .global (ofString "evm_empty"))
              (.ite (.cmp .notEqual
                  (.load .one (.op .add [.var .local (ofString "child"), .const 160#64]))
                  (.const 0#64))
                fcPathErr fcPathKind2Ok))
            (.seq
              (.ite (.cmp .notEqual
                  (.load .one (.op .add [.var .local (ofString "child"), .const 160#64]))
                  (.const 0#64))
                fcPathErr fcPathNe2Ok)
              fcMinTail))).2 S'') :=
    ite_step_6c (Q := fun post => ∃ S'', FcBranchState s0 post S'') hc_kind hkind2arm hne2arm
  refine ⟨?_, ?_⟩
  · intro hnone hntCleanup
    obtain ⟨S'', hBS''⟩ := htriple.2.2 hnone
    exact fcBranchState_cleanup hBS'' hntCleanup
  · intro herr
    exact absurd herr htriple.2.1

theorem fcAfterPrelude_pop' {F : Type}
    {s0 s2 : PanSemStateFiniteExact 64 F}
    (hRel : PreludeRel s0 s2)
    (hne : memW s0 (globN s0 "cur_cont" + 16) ≠ 0)
    (hBranch : FcBranchWalk')
    (hnt : (evaluateHOLFiniteState s2 fcAfterPrelude).1 ≠ some .timeOut) :
    FinishPost s0 (evaluateHOLFiniteState s2 fcAfterPrelude).1
      (evaluateHOLFiniteState s2 fcAfterPrelude).2 := by
  obtain ⟨hne2, hparent, _⟩ := fcPrelude_parent hRel hne
  have hAp := fcPop_arena hRel.inv.1
    (BitVec.ofNat 64 (memW s0 (globN s0 "cur_cont")))
    (BitVec.ofNat 64 (memW s2 (globN s2 "cur_cont" + 8)))
  have hg := fcPop_other_global s2
    (BitVec.ofNat 64 (memW s0 (globN s0 "cur_cont")))
    (BitVec.ofNat 64 (memW s2 (globN s2 "cur_cont" + 8)))
  have hev : globN (setGlobalHOLFinite (ofString "cur_cont")
      (.val (.word (BitVec.ofNat 64 (memW s2 (globN s2 "cur_cont" + 8)))))
      (setGlobalHOLFinite (ofString "ev")
        (.val (.word (BitVec.ofNat 64 (memW s0 (globN s0 "cur_cont"))))) s2)) "ev" =
      memW s2 (globN s2 "cur_cont") := by
    rw [← hparent]
    simp only [globN, setGlobalHOLFinite, HolFiniteMapExact.update, FUPDATE,
      if_neg (show ofString "cur_cont" ≠ ofString "ev" from by decide),
      if_pos rfl, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (OpDispatchSpec.memW_lt s2 _)
  have hcc : globN (setGlobalHOLFinite (ofString "cur_cont")
      (.val (.word (BitVec.ofNat 64 (memW s2 (globN s2 "cur_cont" + 8)))))
      (setGlobalHOLFinite (ofString "ev")
        (.val (.word (BitVec.ofNat 64 (memW s0 (globN s0 "cur_cont"))))) s2)) "cur_cont" =
      memW s2 (globN s2 "cur_cont" + 8) := by
    simp only [globN, setGlobalHOLFinite, HolFiniteMapExact.update, FUPDATE,
      if_pos rfl, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (OpDispatchSpec.memW_lt s2 _)
  have hvmsa : globN (setGlobalHOLFinite (ofString "cur_cont")
      (.val (.word (BitVec.ofNat 64 (memW s2 (globN s2 "cur_cont" + 8)))))
      (setGlobalHOLFinite (ofString "ev")
        (.val (.word (BitVec.ofNat 64 (memW s0 (globN s0 "cur_cont"))))) s2)) "vm_system_address" =
      globN s2 "vm_system_address" :=
    hg "vm_system_address" (by decide) (by decide)
  have hLSD : FcLogsSelfDisj s0 (setGlobalHOLFinite (ofString "cur_cont")
      (.val (.word (BitVec.ofNat 64 (memW s2 (globN s2 "cur_cont" + 8)))))
      (setGlobalHOLFinite (ofString "ev")
        (.val (.word (BitVec.ofNat 64 (memW s0 (globN s0 "cur_cont"))))) s2)) :=
    fcPreludeRel_pop_logs_self_disj hRel hne2 rfl hvmsa
  obtain ⟨S, hBS, hPC, hR1, hR2⟩ :=
    fcPreludeRel_pop_full hRel hne2 hAp rfl rfl rfl hev hcc hg rfl hparent
  rw [fcPop_step hRel] at hnt ⊢
  exact hBranch hBS hPC hLSD hR1 hR2 hnt

theorem fcCore_step' (hCF : CreateFinishSpecs) {F : Type}
    {s0 s1 : PanSemStateFiniteExact 64 F}
    (hInv : EvmInv s0)
    (hm : s1.memory = s0.memory) (hg : s1.globals = s0.globals)
    (hd : s1.memaddrs = s0.memaddrs) (hb : s1.be = s0.be)
    (hsh : s1.shMemaddrs = s0.shMemaddrs) (hc : s1.code = s0.code)
    (hba : s1.baseAddr = s0.baseAddr)
    (hlocs : FcEntryLocals s0 s1)
    (hne : memW s0 (globN s0 "cur_cont" + 16) ≠ 0)
    (hBranch : FcBranchWalk')
    (hnt : (evaluateHOLFiniteState s1 fcCore).1 ≠ some .timeOut) :
    FinishPost s0 (evaluateHOLFiniteState s1 fcCore).1
      (evaluateHOLFiniteState s1 fcCore).2 := by
  have hRel1 : PreludeRel s0 s1 := preludeRel_refl hInv hm hg hd hb hsh hc hba hlocs
  rw [fcCore_eq]
  refine seq_finishPost (fcPrelude_ne_returned s1) ?_ hnt
  intro hnt_pre
  refine ⟨?_, ?_⟩
  · rintro hn hnt2
    have hRel2 := (fcPrelude_step hCF hRel1 hnt_pre).1 hn
    exact fcAfterPrelude_pop' hRel2 hne hBranch hnt2
  · intro herr
    exact absurd herr (fcPrelude_no_err hCF hRel1 hnt_pre)

theorem ek_create_finish_m23 :
    EvmKeeps (EvmAvoids createBuffers)
      ["heap_ptr", "journal_n", "scratch_ptr"] (ofString "create_finish") := by
  obtain ⟨ps, body, rt, hl, hr⟩ := «ek_create_finish»
  exact ⟨ps, body, rt, hl, fun s hc hAv hex hnt hres => hr s hc hAv hex hnt hres⟩

theorem createFinishSpecs_of_gmc
    (hgmc : FunSpec (EvmAvoids createBuffers)
      (fun s r post => InitECandidate.Solver.Wave8Contracts.M23.Resumes r →
        OpDispatchSpec.evmR post ≤ OpDispatchSpec.evmR s ∧
        memW post (globN s "cur_cont" + 48) = memW s (globN s "cur_cont" + 48) ∧
        ChainCellsAgree s post)
      (ofString "create_finish")) :
    CreateFinishSpecs :=
  ⟨ek_create_finish_m23, hgmc⟩

theorem finish_child_finishPost_of (hCF : CreateFinishSpecs) (hBranch : FcBranchWalk') :
    FunSpec FinishReady FinishPost (ofString "finish_child") := by
  refine ⟨[], _, _, lookup_finish_child, ?_⟩
  intro F s hcode hP hex hnt
  obtain ⟨hInv, _, hne⟩ := hP
  have hCore : ∀ (s1 : PanSemStateFiniteExact 64 F),
      s1.memory = s.memory → s1.globals = s.globals →
      s1.memaddrs = s.memaddrs → s1.be = s.be →
      s1.shMemaddrs = s.shMemaddrs → s1.structs = s.structs →
      s1.eshapes = s.eshapes → s1.code = s.code →
      s1.baseAddr = s.baseAddr → s1.topAddr = s.topAddr →
      s1.clock = s.clock →
      FcEntryLocals s s1 →
      (evaluateHOLFiniteState s1 fcCore).1 ≠ some .timeOut →
      FinishPost s (evaluateHOLFiniteState s1 fcCore).1
        (evaluateHOLFiniteState s1 fcCore).2 := by
    intro s1 hm hg' hd hb hsh hst hes hc hba hta hclk hlocs hnt1
    exact fcCore_step' hCF hInv hm hg' hd hb hsh hc hba hlocs hne hBranch hnt1
  exact finish_child_decls_step s hInv hCore hnt

theorem finish_child_finishPost :
    FunSpec FinishReady FinishPost (ofString "finish_child") :=
  finish_child_finishPost_of create_finish_specs
    (fcBranchWalk'_of_leaves fcSetRetdataStepW fcStackPushStepW fcAddrToU256StepW
      incorporate_child_on_success_fc_step fcMinTailStepW)

theorem finish_child_finishPost_aligned_of
    (hf : FunSpec FinishReady FinishPost (ofString "finish_child")) :
    FunSpec FinishReadyA FinishPost (ofString "finish_child") := by
  obtain ⟨ps, body, rt, hl, hr⟩ := hf
  exact ⟨ps, body, rt, hl, fun s hc hs hex hnt => hr s hc ⟨hs.1.1, hs.2.1, hs.2.2⟩ hex hnt⟩

theorem finish_child_finishPost_aligned :
    FunSpec FinishReadyA FinishPost (ofString "finish_child") :=
  finish_child_finishPost_aligned_of finish_child_finishPost

theorem finishChildMemSpec_of
    (hf : FunSpec FinishReady FinishPost (ofString "finish_child")) :
    FinishChildMemSpec := by
  obtain ⟨ps, body, rt, hl, hr⟩ := finish_child_finishPost_aligned_of hf
  refine ⟨ps, body, rt, hl, fun s hc hs hex hnt hres => ?_⟩
  obtain ⟨_, _, _, hchain, hcells, hev, hfmp⟩ := hr s hc hs hex hnt hres
  exact ⟨hchain, hcells, hev, hfmp⟩

theorem finishChildMemSpec : FinishChildMemSpec :=
  finishChildMemSpec_of finish_child_finishPost

theorem finishChildSpecU_of
    (hf : FunSpec FinishReady FinishPost (ofString "finish_child")) :
    FinishChildSpecU := by
  obtain ⟨ps, body, rt, hl, hr⟩ := hf
  refine ⟨ps, body, rt, hl, fun s hc hs hex hnt hres => ?_⟩
  obtain ⟨hi, hlen, hgas, _⟩ := hr s hc hs hex hnt hres
  exact ⟨hi, hlen, hgas⟩

theorem finishChildSpecU : FinishChildSpecU :=
  finishChildSpecU_of finish_child_finishPost

theorem finish_child_spec :
    FunSpec (fun s => EvmInv s ∧ EvmDone s ∧ memW s (globN s "cur_cont" + 16) ≠ 0)
      (fun s r post => ((∃ v, r = some (.returned v)) ∨ OpDispatchSpec.IsEvmErr r) →
        EvmInv post ∧ (evmChain post).length + 1 = (evmChain s).length ∧
        OpDispatchSpec.evmR post ≤ OpDispatchSpec.evmR s)
      (ofString "finish_child") :=
  finishChildSpecU

theorem finish_child_spec_c00_of
    (hf : FunSpec FinishReady FinishPost (ofString "finish_child")) :
    InitECandidate.Solver.Wave8GuestInv.FunSpec
      (fun s => EvmInv s ∧ EvmDone s ∧ memW s (globN s "cur_cont" + 16) ≠ 0)
      (fun s r post =>
        ((∃ v, r = some (.returned v)) ∨ InitECandidate.Solver.Wave8GuestInv.IsEvmErr r) →
          EvmInv post ∧ (evmChain post).length + 1 = (evmChain s).length ∧
          InitECandidate.Solver.Wave8GuestInv.evmR post ≤
            InitECandidate.Solver.Wave8GuestInv.evmR s)
      (ofString "finish_child") := by
  obtain ⟨ps, body, rt, hl, hr⟩ := finishChildSpecU_of hf
  exact ⟨ps, body, rt, hl, fun s hc hs hex hnt hres => hr s hc hs hex hnt hres⟩

theorem finish_child_spec_c00 :
    InitECandidate.Solver.Wave8GuestInv.FunSpec
      (fun s => EvmInv s ∧ EvmDone s ∧ memW s (globN s "cur_cont" + 16) ≠ 0)
      (fun s r post =>
        ((∃ v, r = some (.returned v)) ∨ InitECandidate.Solver.Wave8GuestInv.IsEvmErr r) →
          EvmInv post ∧ (evmChain post).length + 1 = (evmChain s).length ∧
          InitECandidate.Solver.Wave8GuestInv.evmR post ≤
            InitECandidate.Solver.Wave8GuestInv.evmR s)
      (ofString "finish_child") :=
  finish_child_spec_c00_of finish_child_finishPost

theorem headMemBridge_finishChildMemSpec :
    OpHandlersB.HeadMemBridge.FinishChildMemSpec :=
  OpHandlersB.HeadMemBridge.finishChildMemSpec_of_leaf finishChildMemSpec

theorem headMemBridge_finishChildSpecU :
    OpHandlersB.HeadMemBridge.FinishChildSpecU := by
  apply OpHandlersB.HeadMemBridge.finishChildSpecU_of_finishPost
  obtain ⟨ps, body, rt, hl, hr⟩ := finish_child_finishPost
  exact ⟨ps, body, rt, hl, fun s hc hs hex hnt => hr s hc hs hex hnt⟩

theorem ek_frame_start_c08_of
    (hek_prologue : EvmKeeps (EvmAvoids frameStartAvoids) frameStartGw
      (ofString "frame_prologue")) :
    InitECandidate.Solver.Wave8GuestInv.EvmKeeps
      (InitECandidate.Solver.Wave8GuestInv.EvmAvoids (fun s =>
        [(globN s "b2_v", if globN s "b2_v" = 0 then 0 else 128),
         (globN s "bn_expw", if globN s "bn_expw" = 0 then 0 else 352),
         (globN s "bn_gamma", if globN s "bn_gamma" = 0 then 0 else 384),
         (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
         (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
         (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64),
         (globN s "pre_hdr_buf", if globN s "pre_hdr_buf" = 0 then 0 else 96),
         (globN s "rmd_h", if globN s "rmd_h" = 0 then 0 else 40),
         (globN s "rmd_pad", if globN s "rmd_pad" = 0 then 0 else 128),
         (globN s "rmd_x", if globN s "rmd_x" = 0 then 0 else 128),
         (globN s "sha_pad", if globN s "sha_pad" = 0 then 0 else 128),
         (globN s "sha_st", if globN s "sha_st" = 0 then 0 else 64),
         (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52),
         (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)]))
      ["bn_expw", "bn_gamma", "heap_ptr", "journal_n", "scratch_ptr"]
      (ofString "frame_start") := by
  obtain ⟨ps, body, rt, hl, hr⟩ := ek_frame_start_of hek_prologue
  exact ⟨ps, body, rt, hl, fun s hc hAv hex hnt hres => hr s hc hAv hex hnt hres⟩

end InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk
