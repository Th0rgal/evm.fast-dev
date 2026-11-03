import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxCuts
import InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_PtxPhase5
set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody.R10
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded

namespace FastPhase4
open Phase1 FastPhase5

theorem lookup_lst_new :
    originalRuntimeCode.lookup (ofString "lst_new") =
      some ((sourceFunctionEntry Guest.Software.guestFn_lst_new).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 408 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_lst_new) rfl

theorem lookup_lst_push :
    originalRuntimeCode.lookup (ofString "lst_push") =
      some ((sourceFunctionEntry Guest.Software.guestFn_lst_push).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 410 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_lst_push) rfl

theorem lookup_encode_receipt :
    originalRuntimeCode.lookup (ofString "encode_receipt") =
      some ((sourceFunctionEntry Guest.Software.guestFn_encode_receipt).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 836 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_encode_receipt) rfl

theorem callee_param_four {F : Type} (state : PanSemStateFiniteExact 64 F) (fname p1 p2 p3 p4 : MlS)
    (s1 s2 s3 s4 : ShapeHOL) (body : ProgHOL 64) (ret : ShapeHOL)
    (hl : state.code.lookup fname = some ([(p1, s1), (p2, s2), (p3, s3), (p4, s4)], body, ret))
    (e1 e2 e3 e4 : ExpHOL 64) (v1 v2 v3 v4 : ValueHOL 64)
    (values : List (ValueHOL 64)) (body' : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret' : ShapeHOL)
    (he1 : evalAt state e1 = some v1) (he2 : evalAt state e2 = some v2)
    (he3 : evalAt state e3 = some v3) (he4 : evalAt state e4 = some v4)
    (hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [e1, e2, e3, e4] = some values)
    (hlook : lookupCodeHOLFinite state.code.lookup fname values = some (body', callee, ret')) :
    callee.lookup p4 = some v4 := by
  rw [evalListHOLFinite_eq_toExact] at hargs
  simp only [evalListHOLExact, he1, he2, he3, he4, Option.some.injEq] at hargs
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
      simp [List.zip, List.foldl]
    · cases raw

theorem params_four_fourth {F : Type} (s : PanSemStateFiniteExact 64 F)
    (fname p1 p2 p3 p4 : MlS) (sh1 sh2 sh3 sh4 : ShapeHOL) (body : ProgHOL 64) (ret : ShapeHOL)
    (hi : s.code.lookup fname = some ([(p1, sh1), (p2, sh2), (p3, sh3), (p4, sh4)], body, ret))
    (e1 e2 e3 e4 : ExpHOL 64) (vs : List (ValueHOL 64)) (body' : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret' : ShapeHOL)
    (ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [e1,e2,e3,e4] = some vs)
    (hl : lookupCodeHOLFinite s.code.lookup fname vs = some (body', callee, ret')) :
    ∃ v4, evalAt s e4 = some v4 ∧ callee.lookup p4 = some v4 := by
  have ha' := ha
  rw [evalListHOLFinite_eq_toExact] at ha'
  rcases h1 : evalAt s e1 with _ | v1
  · simp only [evalListHOLExact, h1] at ha'; cases ha'
  rcases h2 : evalAt s e2 with _ | v2
  · simp only [evalListHOLExact, h1, h2] at ha'; cases ha'
  rcases h3 : evalAt s e3 with _ | v3
  · simp only [evalListHOLExact, h1, h2, h3] at ha'; cases ha'
  rcases h4 : evalAt s e4 with _ | v4
  · simp only [evalListHOLExact, h1, h2, h3, h4] at ha'; cases ha'
  exact ⟨v4, rfl, callee_param_four s fname p1 p2 p3 p4 sh1 sh2 sh3 sh4 body ret hi
    e1 e2 e3 e4 v1 v2 v3 v4 vs body' callee ret' h1 h2 h3 h4 ha hl⟩

theorem evalAt_local {F : Type} (s : PanSemStateFiniteExact 64 F) (name : String) (x : BitVec 64)
    (h : evalAt s (.var .local (ofString name)) = some (.val (.word x))) :
    x.toNat = locN s name := by
  simp only [evalAt, evalHOLExact] at h
  simp [locN, h]

theorem evalAt_loadL {F : Type} (t : PanSemStateFiniteExact 64 F) (l : String) (k : BitVec 64)
    (v : ValueHOL 64)
    (h : evalAt t (.load .one (.op .add [.var .local (ofString l), .const k])) = some v) :
    ∃ a : BitVec 64, v = .val (.word a) ∧ a.toNat = memW t ((locN t l + k.toNat) % 2 ^ 64) := by
  simp [evalAt, evalHOLExact, evalListHOLExact] at h
  rcases hl : t.locals.lookup (ofString l) with _ | w
  · simp [hl] at h
  · rcases w with x | fs | ⟨nm, fs⟩
    · cases x with
      | word x =>
        simp [hl, valueIsWord, valueWord, wordOpHOL, wordOp, memLoadHOLExact] at h
        rcases hm : t.memory (x + k) with ⟨y⟩
        refine ⟨y, by rw [← h.2, hm], ?_⟩
        have hadd : BitVec.ofNat 64 ((x.toNat + k.toNat) % 2 ^ 64) = x + k := by
          apply BitVec.eq_of_toNat_eq
          simp [BitVec.toNat_add]
        simp only [locN, memW, hl, hadd, h.2, hm]
    · simp [hl, valueIsWord] at h
    · simp [hl, valueIsWord] at h

theorem eval_add_global_const {F : Type} {s : PanSemStateFiniteExact 64 F}
    {g : String} {k x : BitVec 64}
    (hx : evalAt s (.op .add [.var .global (ofString g), .const k]) = some (.val (.word x))) :
    x.toNat = (globN s g + k.toNat) % 2 ^ 64 := by
  simp only [evalAt, evalHOLExact, evalListHOLExact] at hx
  rcases hg : s.globals.lookup (ofString g) with _ | vg
  · simp [hg] at hx
  · rcases vg with wg | _ | _
    · cases wg with
      | word gw =>
        simp only [hg, valueIsWord, valueWord, wordOpHOL, wordOp, List.all, List.map,
          Option.map, Bool.and_self, ↓reduceIte, List.foldr, Option.some.injEq,
          ValueHOL.val.injEq, HolWordLab.word.injEq] at hx
        have hgn : globN s g = gw.toNat := by simp [globN, hg]
        have hx' : x = gw + (k + 0) := hx.symm
        have hz0 : (0 : BitVec 64).toNat = 0 := by decide
        rw [hx', BitVec.toNat_add, BitVec.toNat_add, hz0, Nat.add_zero, Nat.add_mod_mod, hgn]
    · simp [hg, valueIsWord] at hx
    · simp [hg, valueIsWord] at hx

theorem eval_is_word_op {F : Type} {s : PanSemStateFiniteExact 64 F} {bop : BinOp}
    {es : List (ExpHOL 64)} {v : ValueHOL 64} (h : evalAt s (.op bop es) = some v) :
    ∃ w : HolWordLab 64, v = .val w := by
  simp only [evalAt, evalHOLExact] at h
  split at h
  · split at h
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨w, _, rfl⟩ := h
      exact ⟨.word w, rfl⟩
    · cases h
  · cases h

theorem eval_is_word_load_one {F : Type} {s : PanSemStateFiniteExact 64 F} {e : ExpHOL 64}
    {v : ValueHOL 64} (h : evalAt s (.load .one e) = some v) :
    ∃ w : HolWordLab 64, v = .val w := by
  simp only [evalAt, evalHOLExact] at h
  split at h
  · split at h
    · unfold memLoadHOLExact at h
      split at h
      · simp only [Option.some.injEq] at h; exact ⟨_, h.symm⟩
      · cases h
    · cases h
  · cases h

theorem localsOnly_txWorld : LocalsOnly ["index"] TxWorld := by
  intro F s locals k hl ⟨hWO, henv⟩
  exact ⟨localsFree_worldOK s locals k hWO, txEnv_with_locals s locals k (hl "index" (by simp)) henv⟩

theorem txWorld_guestInv {F : Type} (s : PanSemStateFiniteExact 64 F) (h : TxWorld s) :
    GuestInv s := h.1.1.1

theorem pushBo40Loop_bound (h : PtxCallees) :
    let body : ProgHOL 64 :=
      .decCall (ofString "slot") .one (ofString "lst_push")
        [.load .one (.op .add [.var .global (ofString "bo"), .const 40]), .const 8]
        (.seq
          (.store (.var .local (ofString "slot"))
            (.load .one (.op .add [.var .local (ofString "lp"),
              .panop .mul [.var .local (ofString "i"), .const 8]])))
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])))
    TerminatingProgBoundedOn GuestInv
      (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nl"))) body)
      ((2 ^ 64 + 1) * ((K.«lst_push» + 1) + 1)) := by
  intro body
  have hbody : TerminatingProgBoundedOn GuestInv body (K.«lst_push» + 1) := by
    have hb : TerminatingProgBoundedOn GuestInv body (K.«lst_push» + (0 + 0) + 1) := by
      unfold body
      exact TerminatingProgBoundedOn.decCall_guestInv h.fb_lst_push (ofString "slot") .one _
        (TerminatingProgBoundedOn.seq_guestInv
          (bound_of_clock (fun s => clock_store s _ _))
          (bound_of_clock (fun s => clock_assign s .local (ofString "i") _)))
    intro F s hc hg
    simpa only [Nat.add_zero] using hb s hc hg
  have hinc : IncrBody (ofString "i") body := by
    unfold body
    exact IncrBody.decCall _ _ _ _ (by decide) (IncrBody.seq _ rfl rfl IncrBody.incr)
  intro F s hc hg
  exact while_less_guestInv (ofString "i") (.var .local (ofString "nl")) hbody hinc s hc hg

theorem copyLogsLoop_bound :
    let body : ProgHOL 64 :=
      .seq
        (.store
          (.op .add [.var .local (ofString "stable_lp"),
            .panop .mul [.var .local (ofString "i"), .const 8]])
          (.load .one (.op .add [.var .local (ofString "lp"),
            .panop .mul [.var .local (ofString "i"), .const 8]])))
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1]))
    TerminatingProgBoundedOn GuestInv
      (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nl"))) body)
      ((2 ^ 64 + 1) * (0 + 1)) := by
  intro body
  have hbody : TerminatingProgBoundedOn GuestInv body 0 := by
    have hb : TerminatingProgBoundedOn GuestInv body (0 + 0) := by
      unfold body
      exact TerminatingProgBoundedOn.seq_guestInv
        (bound_of_clock (fun s => clock_store s _ _))
        (bound_of_clock (fun s => clock_assign s .local (ofString "i") _))
    intro F s hc hg
    exact hb s hc hg
  have hinc : IncrBody (ofString "i") body := by
    unfold body
    exact IncrBody.seq _ rfl rfl IncrBody.incr
  intro F s hc hg
  exact while_less_guestInv (ofString "i") (.var .local (ofString "nl")) hbody hinc s hc hg

def phase4Budget (b : Nat) : Nat :=
  let s6 := K.«lst_push» + (0 + b) + 1
  let s5 := ((2 ^ 64 + 1) * (0 + 1)) + s6
  let s4 := Nat.max 0 0 + (K.«lst_new» + (0 + (0 + s5)) + 1)
  let s3 := 0 + (0 + (0 + (((2 ^ 64 + 1) * ((K.«lst_push» + 1) + 1)) + s4)))
  let s2 := Nat.max (K.«lst_new» + 1) 0 + (Nat.max 0 0 + (K.«encode_receipt» + s3 + 1))
  let s1 := Nat.max 0 0 + (K.«max» + (0 + (0 + (0 + (0 + (0 + s2))))) + 1)
  let s0 := (K.«create_ether» + 1) + ((K.«create_ether» + 1) + s1)
  K.«udiv_small5» + (K.«min» + (K.«max» + (K.«fee_mul» + (K.«u256_sub» + (K.«fee_mul» + s0 + 1) + 1) + 1) + 1) + 1) + 1

theorem phase4Budget_eq (b : Nat) : phase4Budget b = ptxCost4 + b := by
  unfold phase4Budget ptxCost4
  simp only [Nat.add_zero, Nat.zero_add, Nat.max_self, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Constructive GuestInv spine bound for all 40 HOL continuation steps of `ptxPhase4`. -/
theorem phase4_guestInv_cut (h : PtxCallees) {tail : ProgHOL 64} {b : Nat}
    (htail : TerminatingProgBoundedOn GuestInv tail b) :
    TerminatingProgBoundedOn GuestInv (ptxPhase4 tail) (ptxCost4 + b) := by
  have hb : TerminatingProgBoundedOn GuestInv (ptxPhase4 tail) (phase4Budget b) := by
    unfold phase4Budget ptxPhase4 ptxCode
    refine TerminatingProgBoundedOn.dec_on localsFree_guestInv _ _ _ ?_
    refine TerminatingProgBoundedOn.decCall_guestInv h.fb_udiv_small5 _ _ _ ?_
    refine TerminatingProgBoundedOn.decCall_guestInv h.fb_min _ _ _ ?_
    refine TerminatingProgBoundedOn.dec_on localsFree_guestInv _ _ _ ?_
    refine TerminatingProgBoundedOn.decCall_guestInv h.fb_max _ _ _ ?_
    refine TerminatingProgBoundedOn.dec_on localsFree_guestInv _ _ _ ?_
    refine TerminatingProgBoundedOn.decCall_guestInv h.fb_fee_mul _ _ _ ?_
    refine TerminatingProgBoundedOn.decCall_guestInv h.fb_u256_sub _ _ _ ?_
    refine TerminatingProgBoundedOn.decCall_guestInv h.fb_fee_mul _ _ _ ?_
    refine TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.call_guestInv h.fb_create_ether none _) ?_
    refine TerminatingProgBoundedOn.seq_guestInv (TerminatingProgBoundedOn.call_guestInv h.fb_create_ether none _) ?_
    refine TerminatingProgBoundedOn.dec_on localsFree_guestInv _ _ _ ?_
    refine TerminatingProgBoundedOn.dec_on localsFree_guestInv _ _ _ ?_
    refine TerminatingProgBoundedOn.seq_guestInv
      (TerminatingProgBoundedOn.ite_on
        (bound_of_clock (fun s => clock_assign s .local _ _))
        (bound_of_clock clock_skip)) ?_
    refine TerminatingProgBoundedOn.decCall_guestInv h.fb_max _ _ _ ?_
    refine TerminatingProgBoundedOn.seq_guestInv (bound_of_clock (fun s => clock_store s _ _)) ?_
    refine TerminatingProgBoundedOn.seq_guestInv (bound_of_clock (fun s => clock_store s _ _)) ?_
    refine TerminatingProgBoundedOn.seq_guestInv (bound_of_clock (fun s => clock_store s _ _)) ?_
    refine TerminatingProgBoundedOn.seq_guestInv (bound_of_clock (fun s => clock_store s _ _)) ?_
    refine TerminatingProgBoundedOn.seq_guestInv (bound_of_clock clock_skip) ?_
    refine TerminatingProgBoundedOn.dec_on localsFree_guestInv _ _ _ ?_
    refine TerminatingProgBoundedOn.seq_guestInv
      (TerminatingProgBoundedOn.ite_on
        (TerminatingProgBoundedOn.call_guestInv h.fb_lst_new (some (.local, ofString "logs")) _)
        (bound_of_clock clock_skip)) ?_
    refine TerminatingProgBoundedOn.dec_on localsFree_guestInv _ _ _ ?_
    refine TerminatingProgBoundedOn.seq_guestInv
      (TerminatingProgBoundedOn.ite_on
        (bound_of_clock (fun s => clock_assign s .local _ _))
        (bound_of_clock clock_skip)) ?_
    refine TerminatingProgBoundedOn.decCall_guestInv h.fb_encode_receipt _ _ _ ?_
    refine TerminatingProgBoundedOn.seq_guestInv (bound_of_clock (fun s => clock_store s _ _)) ?_
    refine TerminatingProgBoundedOn.seq_guestInv (bound_of_clock (fun s => clock_store s _ _)) ?_
    refine TerminatingProgBoundedOn.dec_on localsFree_guestInv _ _ _ ?_
    refine TerminatingProgBoundedOn.dec_on localsFree_guestInv _ _ _ ?_
    refine TerminatingProgBoundedOn.seq_guestInv (bound_of_clock (fun s => clock_assign s .local _ _)) ?_
    refine TerminatingProgBoundedOn.seq_guestInv (pushBo40Loop_bound h) ?_
    refine TerminatingProgBoundedOn.dec_on localsFree_guestInv _ _ _ ?_
    refine TerminatingProgBoundedOn.seq_guestInv
      (TerminatingProgBoundedOn.ite_on
        (bound_of_clock (fun s => clock_assign s .local _ _))
        (bound_of_clock clock_skip)) ?_
    refine TerminatingProgBoundedOn.decCall_guestInv h.fb_lst_new _ _ _ ?_
    refine TerminatingProgBoundedOn.seq_guestInv (bound_of_clock (fun s => clock_store s _ _)) ?_
    refine TerminatingProgBoundedOn.dec_on localsFree_guestInv _ _ _ ?_
    refine TerminatingProgBoundedOn.seq_guestInv (bound_of_clock (fun s => clock_assign s .local _ _)) ?_
    refine TerminatingProgBoundedOn.seq_guestInv copyLogsLoop_bound ?_
    refine TerminatingProgBoundedOn.decCall_guestInv h.fb_lst_push _ _ _ ?_
    exact TerminatingProgBoundedOn.seq_guestInv (bound_of_clock (fun s => clock_store s _ _)) htail
  rw [← phase4Budget_eq b]
  intro F s hc hg
  exact hb s hc hg

end FastPhase4

end InitECandidate.Solver.Wave8GuestInv.GuardedBody.R10
