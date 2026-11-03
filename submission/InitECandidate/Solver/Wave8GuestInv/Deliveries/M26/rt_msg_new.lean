import InitECandidate.Solver.Wave8GuestInv.Deliveries.M26.Common

/-! Return-typing contract `rt_msg_new` for micro-shard `m26` (`wave8/contracts-m26`),
checked against frozen revision 9 (`8a79d9f28`, tag `wave8-spec-frozen-r9`).

`msg_new` (AST line 15344, index 465): returns a fresh zeroed 176-byte message record
(`alloc(176)`, `memzero`).
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1500000
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

private theorem lookup_msg_new :
    originalRuntimeCode.lookup (ofString "msg_new") =
      some ([], sourceFnBody Guest.Software.guestFn_msg_new, .one) :=
  lookup_of_guestAst_getElem 465 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_msg_new) rfl

private theorem eval_while_false {F : Type} (s : PanSemStateFiniteExact 64 F)
    (cond : ExpHOL 64) (body : ProgHOL 64)
    (hcond : ev s cond = some (.val (.word 0))) :
    evaluateHOLFiniteState s (.while cond body) = (none, s) := by
  rw [evaluateHOLFiniteState_while_total, evalHOLFinite_eq_toExact]
  simp only [ev] at hcond
  rw [hcond]
  rfl

private theorem eval_store0_step {F : Type} (s : PanSemStateFiniteExact 64 F)
    (dst_e : ExpHOL 64) (a : BitVec 64) (rest : ProgHOL 64)
    (ha : ev s dst_e = some (.val (.word a)))
    (hdom : s.memaddrs a) :
    evaluateHOLFiniteState s (.seq (.store dst_e (.const 0)) rest) =
      evaluateHOLFiniteState { s with memory := updW s.memory a 0 } rest := by
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_store]
  simp only [ev] at ha
  have hc0 : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x))
      (.const 0) = some (.val (.word 0)) := rfl
  rw [ha, hc0]
  simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL, hdom, ↓reduceIte]
  rfl

private def mzLoop1 : ProgHOL 64 :=
  .while (.cmp .notLower (.var .local (ofString "n"))
      (.op .add [.var .local (ofString "i"), .const 32]))
    (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) (.const 0))
      (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 8]) (.const 0))
        (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 16]) (.const 0))
          (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 24]) (.const 0))
            (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 32]))))))

private def mzLoop2 : ProgHOL 64 :=
  .while (.cmp .notLower (.var .local (ofString "n"))
      (.op .add [.var .local (ofString "i"), .const 8]))
    (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) (.const 0))
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 8])))

private def mzLoop3 : ProgHOL 64 :=
  .while (.cmp .notLower (.var .local (ofString "n"))
      (.op .add [.var .local (ofString "i"), .const 8]))
    (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) (.const 0))
      (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 1]) (.const 0))
        (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 2]) (.const 0))
          (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 3]) (.const 0))
            (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 4]) (.const 0))
              (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 5]) (.const 0))
                (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 6]) (.const 0))
                  (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 7]) (.const 0))
                    (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 8]))))))))))

private def mzLoop4 : ProgHOL 64 :=
  .while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n")))
    (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) (.const 0))
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])))

private theorem add3_eq (a b c : BitVec 64) : a + (b + (c + 0)) = a + b + c := by
  simp [BitVec.add_assoc]

private theorem add2_eq (a b : BitVec 64) : a + (b + 0) = a + b := by
  simp

private theorem mzLoop1_step {F : Type} (s : PanSemStateFiniteExact 64 F)
    (dst iv : BitVec 64)
    (hdst : s.locals.lookup (ofString "dst") = some (.val (.word dst)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word 176)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iv)))
    (hlt : iv.toNat + 32 ≤ 176)
    (hdom0 : s.memaddrs (dst + iv))
    (hdom8 : s.memaddrs (dst + iv + 8))
    (hdom16 : s.memaddrs (dst + iv + 16))
    (hdom24 : s.memaddrs (dst + iv + 24))
    (hnt : (evaluateHOLFiniteState s mzLoop1).1 ≠ some .timeOut) :
    ∃ s' : PanSemStateFiniteExact 64 F,
      s'.globals = s.globals ∧ s'.code = s.code ∧ s'.memaddrs = s.memaddrs ∧
      s'.shMemaddrs = s.shMemaddrs ∧ s'.baseAddr = s.baseAddr ∧
      s'.locals.lookup (ofString "dst") = some (.val (.word dst)) ∧
      s'.locals.lookup (ofString "n") = some (.val (.word 176)) ∧
      s'.locals.lookup (ofString "i") = some (.val (.word (iv + 32))) ∧
      s'.memory = updW (updW (updW (updW s.memory (dst + iv) 0) (dst + iv + 8) 0)
        (dst + iv + 16) 0) (dst + iv + 24) 0 ∧
      evaluateHOLFiniteState s mzLoop1 = evaluateHOLFiniteState s' mzLoop1 := by
  unfold mzLoop1 at hnt ⊢
  rw [evaluateHOLFiniteState_while_total, evalHOLFinite_eq_toExact] at hnt ⊢
  have hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .notLower (.var .local (ofString "n"))
        (.op .add [.var .local (ofString "i"), .const 32])) = some (.val (.word 1)) := by
    have hsum : (iv + 32#64).toNat = iv.toNat + 32 := by
      rw [BitVec.toNat_add]
      change (iv.toNat + 32) % 2 ^ 64 = iv.toNat + 32
      omega
    have hi32 : ¬ (176#64 < iv + 32#64) := by
      rw [BitVec.lt_def, hsum]
      change ¬ (176 < iv.toNat + 32)
      omega
    have hi32' : ¬ ((176 : BitVec 64) < iv + 32) := hi32
    simp only [evalHOLExact, evalListHOLExact, hn, hi, valueIsWord, valueWord, wordOpHOL, wordOp,
      List.all, List.map, Option.map, List.foldr, Bool.and_self, ↓reduceIte, add2_eq,
      Compiler.Encoders.Asm.wordCmpHOL, hi32, hi32', decide_false, Bool.not_false]
  rw [hcond] at hnt ⊢
  have h1ne0 : (1 : BitVec 64) ≠ 0 := by decide
  simp only [h1ne0, ↓reduceIte] at hnt ⊢
  by_cases hz : s.clock = 0
  · simp [hz] at hnt
  · simp only [hz, ↓reduceIte, fixClockHOLFinite_evaluateState]
    set d := decClockHOLFinite s
    have hd_dst : d.locals.lookup (ofString "dst") = some (.val (.word dst)) := hdst
    have hd_i : d.locals.lookup (ofString "i") = some (.val (.word iv)) := hi
    have he0 : ev d (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) =
        some (.val (.word (dst + iv))) := by
      simp [ev, evalHOLExact, evalListHOLExact, hd_dst, hd_i, valueIsWord, valueWord, wordOpHOL, wordOp]
    rw [eval_store0_step d _ (dst + iv) _ he0 hdom0]
    set d1 := { d with memory := updW d.memory (dst + iv) 0 }
    have he8 : ev d1 (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 8]) =
        some (.val (.word (dst + iv + 8))) := by
      simp only [ev, evalHOLExact, evalListHOLExact, d1, hd_dst, hd_i, valueIsWord, valueWord,
        wordOpHOL, wordOp, List.all, List.map, Option.map, List.foldr, Bool.and_self, ↓reduceIte]
      exact congrArg (fun w => some (ValueHOL.val (HolWordLab.word w))) (add3_eq dst iv 8)
    rw [eval_store0_step d1 _ (dst + iv + 8) _ he8 hdom8]
    set d2 := { d1 with memory := updW d1.memory (dst + iv + 8) 0 }
    have he16 : ev d2 (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 16]) =
        some (.val (.word (dst + iv + 16))) := by
      simp only [ev, evalHOLExact, evalListHOLExact, d2, d1, hd_dst, hd_i, valueIsWord, valueWord,
        wordOpHOL, wordOp, List.all, List.map, Option.map, List.foldr, Bool.and_self, ↓reduceIte]
      exact congrArg (fun w => some (ValueHOL.val (HolWordLab.word w))) (add3_eq dst iv 16)
    rw [eval_store0_step d2 _ (dst + iv + 16) _ he16 hdom16]
    set d3 := { d2 with memory := updW d2.memory (dst + iv + 16) 0 }
    have he24 : ev d3 (.op .add [.var .local (ofString "dst"), .var .local (ofString "i"), .const 24]) =
        some (.val (.word (dst + iv + 24))) := by
      simp only [ev, evalHOLExact, evalListHOLExact, d3, d2, d1, hd_dst, hd_i, valueIsWord, valueWord,
        wordOpHOL, wordOp, List.all, List.map, Option.map, List.foldr, Bool.and_self, ↓reduceIte]
      exact congrArg (fun w => some (ValueHOL.val (HolWordLab.word w))) (add3_eq dst iv 24)
    rw [eval_store0_step d3 _ (dst + iv + 24) _ he24 hdom24]
    set d4 := { d3 with memory := updW d3.memory (dst + iv + 24) 0 }
    have hasgn : evaluateHOLFiniteState d4
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 32])) =
        (none, setVarHOLFinite (ofString "i") (.val (.word (iv + 32))) d4) := by
      rw [evaluateHOLFiniteState_assign]
      have hd4_i : d4.locals.lookup (ofString "i") = some (.val (.word iv)) := hi
      simp [evalHOLExact, evalListHOLExact, hd4_i, valueIsWord, valueWord, wordOpHOL, wordOp,
        add2_eq, isValidValueHOLExact, lookupKvarHOLExact, shapeOfHOLExact, shapeEqHOL,
        setKvarHOLFinite]
    rw [hasgn]
    dsimp only
    refine ⟨setVarHOLFinite (ofString "i") (.val (.word (iv + 32))) d4, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, rfl, rfl⟩
    · simp [setVarHOLFinite, d4, d3, d2, d1, d, decClockHOLFinite, HolFiniteMapExact.lookup_update,
        FUPDATE, show ofString "i" ≠ ofString "dst" by decide, hdst]
    · simp [setVarHOLFinite, d4, d3, d2, d1, d, decClockHOLFinite, HolFiniteMapExact.lookup_update,
        FUPDATE, show ofString "i" ≠ ofString "n" by decide, hn]
    · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]

private theorem mzLoop2_step {F : Type} (s : PanSemStateFiniteExact 64 F)
    (dst iv : BitVec 64)
    (hdst : s.locals.lookup (ofString "dst") = some (.val (.word dst)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word 176)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iv)))
    (hlt : iv.toNat + 8 ≤ 176)
    (hdom0 : s.memaddrs (dst + iv))
    (hnt : (evaluateHOLFiniteState s mzLoop2).1 ≠ some .timeOut) :
    ∃ s' : PanSemStateFiniteExact 64 F,
      s'.globals = s.globals ∧ s'.code = s.code ∧ s'.memaddrs = s.memaddrs ∧
      s'.shMemaddrs = s.shMemaddrs ∧ s'.baseAddr = s.baseAddr ∧
      s'.locals.lookup (ofString "dst") = some (.val (.word dst)) ∧
      s'.locals.lookup (ofString "n") = some (.val (.word 176)) ∧
      s'.locals.lookup (ofString "i") = some (.val (.word (iv + 8))) ∧
      s'.memory = updW s.memory (dst + iv) 0 ∧
      evaluateHOLFiniteState s mzLoop2 = evaluateHOLFiniteState s' mzLoop2 := by
  unfold mzLoop2 at hnt ⊢
  rw [evaluateHOLFiniteState_while_total, evalHOLFinite_eq_toExact] at hnt ⊢
  have hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .notLower (.var .local (ofString "n"))
        (.op .add [.var .local (ofString "i"), .const 8])) = some (.val (.word 1)) := by
    have hsum : (iv + 8#64).toNat = iv.toNat + 8 := by
      rw [BitVec.toNat_add]
      change (iv.toNat + 8) % 2 ^ 64 = iv.toNat + 8
      omega
    have hi8 : ¬ (176#64 < iv + 8#64) := by
      rw [BitVec.lt_def, hsum]
      change ¬ (176 < iv.toNat + 8)
      omega
    have hi8' : ¬ ((176 : BitVec 64) < iv + 8) := hi8
    simp only [evalHOLExact, evalListHOLExact, hn, hi, valueIsWord, valueWord, wordOpHOL, wordOp,
      List.all, List.map, Option.map, List.foldr, Bool.and_self, ↓reduceIte, add2_eq,
      Compiler.Encoders.Asm.wordCmpHOL, hi8, hi8', decide_false, Bool.not_false]
  rw [hcond] at hnt ⊢
  have h1ne0 : (1 : BitVec 64) ≠ 0 := by decide
  simp only [h1ne0, ↓reduceIte] at hnt ⊢
  by_cases hz : s.clock = 0
  · simp [hz] at hnt
  · simp only [hz, ↓reduceIte, fixClockHOLFinite_evaluateState]
    set d := decClockHOLFinite s
    have hd_dst : d.locals.lookup (ofString "dst") = some (.val (.word dst)) := hdst
    have hd_i : d.locals.lookup (ofString "i") = some (.val (.word iv)) := hi
    have he0 : ev d (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) =
        some (.val (.word (dst + iv))) := by
      simp [ev, evalHOLExact, evalListHOLExact, hd_dst, hd_i, valueIsWord, valueWord, wordOpHOL, wordOp]
    rw [eval_store0_step d _ (dst + iv) _ he0 hdom0]
    set d1 := { d with memory := updW d.memory (dst + iv) 0 }
    have hasgn : evaluateHOLFiniteState d1
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 8])) =
        (none, setVarHOLFinite (ofString "i") (.val (.word (iv + 8))) d1) := by
      rw [evaluateHOLFiniteState_assign]
      have hd1_i : d1.locals.lookup (ofString "i") = some (.val (.word iv)) := hi
      simp [evalHOLExact, evalListHOLExact, hd1_i, valueIsWord, valueWord, wordOpHOL, wordOp,
        add2_eq, isValidValueHOLExact, lookupKvarHOLExact, shapeOfHOLExact, shapeEqHOL,
        setKvarHOLFinite]
    rw [hasgn]
    dsimp only
    refine ⟨setVarHOLFinite (ofString "i") (.val (.word (iv + 8))) d1, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, rfl, rfl⟩
    · simp [setVarHOLFinite, d1, d, decClockHOLFinite, HolFiniteMapExact.lookup_update,
        FUPDATE, show ofString "i" ≠ ofString "dst" by decide, hdst]
    · simp [setVarHOLFinite, d1, d, decClockHOLFinite, HolFiniteMapExact.lookup_update,
        FUPDATE, show ofString "i" ≠ ofString "n" by decide, hn]
    · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]

private theorem memzero_176_run {F : Type}
    (state : PanSemStateFiniteExact 64 F) (dst : BitVec 64)
    (hdst_al : dst.toNat % 8 = 0)
    (hdom : ∀ k : Nat, k < 22 → state.memaddrs (dst + BitVec.ofNat 64 (8 * k)))
    (hdst : state.locals.lookup (ofString "dst") = some (.val (.word dst)))
    (hn : state.locals.lookup (ofString "n") = some (.val (.word 176)))
    (retVal : ValueHOL 64)
    (hret : (evaluateHOLFiniteState state (sourceFnBody Guest.Software.guestFn_memzero)).1 =
      some (.returned retVal)) :
    let post := (evaluateHOLFiniteState state (sourceFnBody Guest.Software.guestFn_memzero)).2
    post.globals = state.globals ∧
    ∀ k : Nat, k < 22 → post.memory (dst + BitVec.ofNat 64 (8 * k)) = .word 0 := by
  dsimp only
  have hbody : sourceFnBody Guest.Software.guestFn_memzero =
      .dec (ofString "i") .one (.const 0)
        (.seq
          (.ite (.cmp .equal (.op .and [.var .local (ofString "dst"), .const 7]) (.const 0))
            (.seq mzLoop1 mzLoop2)
            .skip)
          (.seq mzLoop3 (.seq mzLoop4 (.return (.const 0))))) := rfl
  rw [hbody, evaluateHOLFiniteState_dec_total] at hret ⊢
  have hev0 : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a)) (.const 0) = some (.val (.word 0)) := rfl
  dsimp only at hret ⊢
  rw [hev0] at hret ⊢
  have hsh0 : shapeEqHOL .one (shapeOfHOLExact (.val (.word (0 : BitVec 64)))) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  dsimp only at hret ⊢
  rw [if_pos hsh0] at hret ⊢
  dsimp only at hret ⊢
  set s0 := setVarHOLFinite (ofString "i") (.val (.word 0)) state
  have hs0_dst : s0.locals.lookup (ofString "dst") = some (.val (.word dst)) := by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "i" ≠ ofString "dst" by decide, hdst]
  have hs0_n : s0.locals.lookup (ofString "n") = some (.val (.word 176)) := by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "i" ≠ ofString "n" by decide, hn]
  have hs0_i : s0.locals.lookup (ofString "i") = some (.val (.word 0)) := by
    simp [s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  -- Evaluate aligned check `dst & 7 == 0` -> true (`1`)
  have hand7 : dst &&& 7 = 0 := by
    have h1 : dst &&& ((0 : BitVec 64) - 8) = dst := by
      apply BitVec.eq_of_toNat_eq
      rw [and_neg8_toNat]
      omega
    rw [← h1, BitVec.and_assoc]
    have h2 : (((0 : BitVec 64) - 8) &&& 7) = 0 := by decide
    rw [h2]
    simp
  rw [evaluateHOLFiniteState_seq_line780] at hret ⊢
  have hite_eq : evaluateHOLFiniteState s0
      (.ite (.cmp .equal (.op .and [.var .local (ofString "dst"), .const 7]) (.const 0))
        (.seq mzLoop1 mzLoop2) .skip) =
      evaluateHOLFiniteState s0 (.seq mzLoop1 mzLoop2) := by
    rw [evaluateHOLFiniteState_ite]
    have hcond : @evalHOLExact 64 F _ s0.toExact
        (fun a => Classical.propDecidable (s0.memaddrs a))
        (.cmp .equal (.op .and [.var .local (ofString "dst"), .const 7]) (.const 0)) =
        some (.val (.word 1)) := by
      have hand7' : AndOp.and dst (AndOp.and 7#64 18446744073709551615#64) = 0#64 := by
        change dst &&& (7#64 &&& ~~~0#64) = 0#64
        have h7all : (7#64 &&& ~~~0#64) = 7#64 := by decide
        rw [h7all]
        exact hand7
      simp [evalHOLExact, evalListHOLExact, hs0_dst, valueIsWord, valueWord, wordOpHOL, wordOp,
        hand7', Compiler.Encoders.Asm.wordCmpHOL]
    rw [hcond]
    simp [show (1 : BitVec 64) ≠ 0 by decide]
  rw [hite_eq, evaluateHOLFiniteState_seq_line780] at hret ⊢
  -- Helper to extract `mzLoop1` non-timeout from outer `hret`
  have hnt_l1 : (evaluateHOLFiniteState s0 mzLoop1).1 ≠ some .timeOut := by
    intro hto
    rcases hp1 : evaluateHOLFiniteState s0 mzLoop1 with ⟨r1, m1⟩
    rw [hp1] at hto hret
    dsimp only at hto
    subst hto
    simp at hret
  -- Helper for BitVec address normalization `dst + iv + off = dst + BitVec.ofNat 64 ...`
  have hdom_at : ∀ {G : PanSemStateFiniteExact 64 F} (hm : G.memaddrs = state.memaddrs)
      (iv off : BitVec 64) (k : Nat), k < 22 → iv + off = BitVec.ofNat 64 (8 * k) →
      G.memaddrs (dst + iv + off) := by
    intro G hm iv off k hk heq
    rw [hm, BitVec.add_assoc, heq]
    exact hdom k hk
  have hdom_at0 : ∀ {G : PanSemStateFiniteExact 64 F} (hm : G.memaddrs = state.memaddrs)
      (iv : BitVec 64) (k : Nat), k < 22 → iv = BitVec.ofNat 64 (8 * k) →
      G.memaddrs (dst + iv) := by
    intro G hm iv k hk heq
    rw [hm, heq]
    exact hdom k hk
  -- Unroll 5 iterations of `mzLoop1` (i = 0 -> 32 -> 64 -> 96 -> 128 -> 160)
  obtain ⟨s1, hg1, _, hm1, _, _, hd1, hn1, hi1, hmem1, heq1⟩ :=
    mzLoop1_step s0 dst 0 hs0_dst hs0_n hs0_i (by decide)
      (hdom_at0 rfl 0 0 (by decide) (by decide))
      (hdom_at rfl 0 8 1 (by decide) (by decide))
      (hdom_at rfl 0 16 2 (by decide) (by decide))
      (hdom_at rfl 0 24 3 (by decide) (by decide))
      hnt_l1
  rw [heq1] at hret hnt_l1 ⊢
  have hi1' : s1.locals.lookup (ofString "i") = some (.val (.word 32)) := hi1
  obtain ⟨s2, hg2, _, hm2, _, _, hd2, hn2, hi2, hmem2, heq2⟩ :=
    mzLoop1_step s1 dst 32 hd1 hn1 hi1' (by decide)
      (hdom_at0 hm1 32 4 (by decide) (by decide))
      (hdom_at hm1 32 8 5 (by decide) (by decide))
      (hdom_at hm1 32 16 6 (by decide) (by decide))
      (hdom_at hm1 32 24 7 (by decide) (by decide))
      hnt_l1
  rw [heq2] at hret hnt_l1 ⊢
  have hi2' : s2.locals.lookup (ofString "i") = some (.val (.word 64)) := hi2
  obtain ⟨s3, hg3, _, hm3, _, _, hd3, hn3, hi3, hmem3, heq3⟩ :=
    mzLoop1_step s2 dst 64 hd2 hn2 hi2' (by decide)
      (hdom_at0 (hm2.trans hm1) 64 8 (by decide) (by decide))
      (hdom_at (hm2.trans hm1) 64 8 9 (by decide) (by decide))
      (hdom_at (hm2.trans hm1) 64 16 10 (by decide) (by decide))
      (hdom_at (hm2.trans hm1) 64 24 11 (by decide) (by decide))
      hnt_l1
  rw [heq3] at hret hnt_l1 ⊢
  have hi3' : s3.locals.lookup (ofString "i") = some (.val (.word 96)) := hi3
  obtain ⟨s4, hg4, _, hm4, _, _, hd4, hn4, hi4, hmem4, heq4⟩ :=
    mzLoop1_step s3 dst 96 hd3 hn3 hi3' (by decide)
      (hdom_at0 (hm3.trans (hm2.trans hm1)) 96 12 (by decide) (by decide))
      (hdom_at (hm3.trans (hm2.trans hm1)) 96 8 13 (by decide) (by decide))
      (hdom_at (hm3.trans (hm2.trans hm1)) 96 16 14 (by decide) (by decide))
      (hdom_at (hm3.trans (hm2.trans hm1)) 96 24 15 (by decide) (by decide))
      hnt_l1
  rw [heq4] at hret hnt_l1 ⊢
  have hi4' : s4.locals.lookup (ofString "i") = some (.val (.word 128)) := hi4
  obtain ⟨s5, hg5, _, hm5, _, _, hd5, hn5, hi5, hmem5, heq5⟩ :=
    mzLoop1_step s4 dst 128 hd4 hn4 hi4' (by decide)
      (hdom_at0 (hm4.trans (hm3.trans (hm2.trans hm1))) 128 16 (by decide) (by decide))
      (hdom_at (hm4.trans (hm3.trans (hm2.trans hm1))) 128 8 17 (by decide) (by decide))
      (hdom_at (hm4.trans (hm3.trans (hm2.trans hm1))) 128 16 18 (by decide) (by decide))
      (hdom_at (hm4.trans (hm3.trans (hm2.trans hm1))) 128 24 19 (by decide) (by decide))
      hnt_l1
  rw [heq5] at hret ⊢
  have hi5' : s5.locals.lookup (ofString "i") = some (.val (.word 160)) := hi5
  have hm5_eq : s5.memaddrs = state.memaddrs :=
    hm5.trans (hm4.trans (hm3.trans (hm2.trans hm1)))
  have hg5_eq : s5.globals = state.globals :=
    hg5.trans (hg4.trans (hg3.trans (hg2.trans hg1)))
  -- Exit `mzLoop1` at `i = 160` (`160 + 32 = 192 > 176`)
  have hl1_exit : evaluateHOLFiniteState s5 mzLoop1 = (none, s5) := by
    apply eval_while_false
    simp [ev, evalHOLExact, evalListHOLExact, hn5, hi5', valueIsWord, valueWord, wordOpHOL, wordOp,
      Compiler.Encoders.Asm.wordCmpHOL]
  rw [hl1_exit] at hret ⊢
  dsimp only at hret ⊢
  -- Unroll 2 iterations of `mzLoop2` (`i = 160 -> 168 -> 176`)
  have hnt_l2 : (evaluateHOLFiniteState s5 mzLoop2).1 ≠ some .timeOut := by
    intro hto
    rcases hp2 : evaluateHOLFiniteState s5 mzLoop2 with ⟨r2, m2⟩
    rw [hp2] at hto hret
    dsimp only at hto
    subst hto
    simp at hret
  obtain ⟨s6, hg6, _, hm6, _, _, hd6, hn6, hi6, hmem6, heq6⟩ :=
    mzLoop2_step s5 dst 160 hd5 hn5 hi5' (by decide)
      (hdom_at0 hm5_eq 160 20 (by decide) (by decide)) hnt_l2
  rw [heq6] at hret hnt_l2 ⊢
  have hi6' : s6.locals.lookup (ofString "i") = some (.val (.word 168)) := hi6
  obtain ⟨s7, hg7, _, hm7, _, _, hd7, hn7, hi7, hmem7, heq7⟩ :=
    mzLoop2_step s6 dst 168 hd6 hn6 hi6' (by decide)
      (hdom_at0 (hm6.trans hm5_eq) 168 21 (by decide) (by decide)) hnt_l2
  rw [heq7] at hret ⊢
  have hi7' : s7.locals.lookup (ofString "i") = some (.val (.word 176)) := hi7
  -- Exit `mzLoop2` at `i = 176` (`176 + 8 = 184 > 176`)
  have hl2_exit : evaluateHOLFiniteState s7 mzLoop2 = (none, s7) := by
    apply eval_while_false
    simp [ev, evalHOLExact, evalListHOLExact, hn7, hi7', valueIsWord, valueWord, wordOpHOL, wordOp,
      Compiler.Encoders.Asm.wordCmpHOL]
  rw [hl2_exit] at hret ⊢
  dsimp only at hret ⊢
  -- Exit `mzLoop3` at `i = 176`
  rw [evaluateHOLFiniteState_seq_line780] at hret ⊢
  have hl3_exit : evaluateHOLFiniteState s7 mzLoop3 = (none, s7) := by
    apply eval_while_false
    simp [ev, evalHOLExact, evalListHOLExact, hn7, hi7', valueIsWord, valueWord, wordOpHOL, wordOp,
      Compiler.Encoders.Asm.wordCmpHOL]
  rw [hl3_exit] at hret ⊢
  dsimp only at hret ⊢
  -- Exit `mzLoop4` at `i = 176` (`176 < 176` is false)
  rw [evaluateHOLFiniteState_seq_line780] at hret ⊢
  have hl4_exit : evaluateHOLFiniteState s7 mzLoop4 = (none, s7) := by
    apply eval_while_false
    simp [ev, evalHOLExact, hn7, hi7', Compiler.Encoders.Asm.wordCmpHOL]
  rw [hl4_exit] at hret ⊢
  dsimp only at hret ⊢
  -- Final `return 0`
  have hret0 : evaluateHOLFiniteState s7 (.return (.const 0)) =
      (some (.returned (.val (.word 0))), emptyLocalsHOLFinite s7) := by
    rw [evaluateHOLFiniteState_return]
    simp [evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL]
  rw [hret0]
  dsimp only [emptyLocalsHOLFinite]
  refine ⟨hg7.trans (hg6.trans hg5_eq), ?_⟩
  -- Every `updW _ _ 0` writes `.word 0`, and each of the 22 addresses `dst + 8*k` was written!
  have hupd0_hit : ∀ (m : BitVec 64 → HolWordLab 64) (a : BitVec 64), updW m a 0 a = .word 0 := by
    intro m a; simp [updW]
  have hupd0_pres : ∀ (m : BitVec 64 → HolWordLab 64) (a b : BitVec 64),
      m b = .word 0 → updW m a 0 b = .word 0 := by
    intro m a b h; unfold updW; split <;> [rfl; exact h]
  have h7_mem : ∀ k : Nat, k < 22 → s7.memory (dst + BitVec.ofNat 64 (8 * k)) = .word 0 := by
    rw [hmem7, hmem6, hmem5, hmem4, hmem3, hmem2, hmem1]
    have norm_addr : ∀ (iv off : BitVec 64), dst + iv + off = dst + (iv + off) :=
      fun iv off => BitVec.add_assoc dst iv off
    simp only [norm_addr]
    intro k hk
    interval_cases k
    all_goals
      simp only [show (0 : BitVec 64) + 8 = 8 by decide,
        show (0 : BitVec 64) + 16 = 16 by decide,
        show (0 : BitVec 64) + 24 = 24 by decide,
        show (32 : BitVec 64) + 8 = 40 by decide,
        show (32 : BitVec 64) + 16 = 48 by decide,
        show (32 : BitVec 64) + 24 = 56 by decide,
        show (64 : BitVec 64) + 8 = 72 by decide,
        show (64 : BitVec 64) + 16 = 80 by decide,
        show (64 : BitVec 64) + 24 = 88 by decide,
        show (96 : BitVec 64) + 8 = 104 by decide,
        show (96 : BitVec 64) + 16 = 112 by decide,
        show (96 : BitVec 64) + 24 = 120 by decide,
        show (128 : BitVec 64) + 8 = 136 by decide,
        show (128 : BitVec 64) + 16 = 144 by decide,
        show (128 : BitVec 64) + 24 = 152 by decide,
        BitVec.ofNat]
      repeat' (first | apply hupd0_hit | apply hupd0_pres)
  exact h7_mem

/-- `msg_new` (AST line 15344): returns a fresh zeroed 176-byte message record (`alloc(176)`,
`memzero`). -/
theorem rt_msg_new :
    Returns ArenaReady (fun s post m => FreshBlock s post m 176 ∧
      ∀ k, k < 22 → memW post (m + 8 * k) = 0)
    (ofString "msg_new") := by
  refine ⟨_, _, _, lookup_msg_new, ?_⟩
  intro F s hcode hAR _ _hnt v hret
  obtain ⟨hG, hA⟩ := hAR
  obtain ⟨hp, fp, sp, hhp, hhp_eq, hfp, hfp_eq, hsp, hsp_eq⟩ := arenaOK_globals s hA
  have hbody : sourceFnBody Guest.Software.guestFn_msg_new =
      .decCall (ofString "m") .one (ofString "alloc") [.const 176]
        (.seq
          (.call (some (none, none)) (ofString "memzero")
            [.var .local (ofString "m"), .const 176])
          (.return (.var .local (ofString "m")))) := rfl
  have hrun : Ret s (sourceFnBody Guest.Software.guestFn_msg_new)
      (fun rv post => ∃ w : BitVec 64, rv = .val (.word w) ∧
        ArenaReady post ∧ AllocatorGrows s post ∧
        FreshBlock s post w.toNat 176 ∧
        ∀ k, k < 22 → memW post (w.toNat + 8 * k) = 0) := by
    rw [hbody]
    apply Ret.of_NS
    refine Ret.ns_alloc hcode 176 rfl hp hhp ?_
    intro hcmp1 hcmp2
    set q : BitVec 64 := (hp + (176 + 7)) &&& ((0 : BitVec 64) - 8)
    set L1 := s.locals.update (ofString "m", .val (.word hp))
    set G1 := s.globals.update (ofString "heap_ptr", .val (.word q))
    set s1 := NS s L1 G1 s.memory (s.clock - 1)
    show Ret s1 _ _
    intro v1 hv1
    rw [evaluateHOLFiniteState_seq_line780] at hv1 ⊢
    -- Step through `.call (some (none, none)) "memzero" [m, 176]`
    have hhp_hi : hp.toNat ≤ heapLimit := by rw [hhp_eq]; exact hA.2.1
    have hhp_al : hp.toNat % 8 = 0 := by rw [hhp_eq]; exact hA.2.2.2.2.2.1
    have hsb_le : sourceBase ≤ hp.toNat := by rw [hhp_eq]; exact hA.1
    obtain ⟨hq_eq, hq_hi, hq_al, hp_le_q⟩ := alloc_arith hp 176 hhp_hi hhp_al hcmp1 hcmp2
    change q.toNat = _ at hq_eq
    change q.toNat ≤ heapLimit at hq_hi
    change q.toNat % 8 = 0 at hq_al
    change hp.toNat ≤ q.toNat at hp_le_q
    have h176 : ((176 : BitVec 64).toNat + 7) / 8 * 8 = 176 := by decide
    rw [h176] at hq_eq
    have hlim_le_he : heapLimit ≤ heapEnd := by decide
    have hdom_22 : ∀ k : Nat, k < 22 → s1.memaddrs (hp + BitVec.ofNat 64 (8 * k)) := by
      intro k hk
      change s.memaddrs _
      rw [hG.memaddrs, ← ofNat_add_toNat_eq hp (8 * k)]
      exact ordinaryDomain_of_nat (hp.toNat + 8 * k) (by omega) (by omega) (by omega)
    rcases hcall : evaluateHOLFiniteState s1
        (.call (some (none, none)) (ofString "memzero")
          [.var .local (ofString "m"), .const 176]) with ⟨rc, sc⟩
    simp only [hcall] at hv1 ⊢
    cases rc with
    | some r' =>
      -- A non-`none` result of `call (some (none, none))` is never `returned`!
      rw [evaluateHOLFiniteState_call] at hcall
      have hargs : evalListHOLFinite s1
          (h := fun a => Classical.propDecidable (s1.memaddrs a))
          [.var .local (ofString "m"), .const 176] =
          some [.val (.word hp), .val (.word 176)] := by
        simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, s1, L1,
          HolFiniteMapExact.lookup_update, FUPDATE]
      rw [hargs] at hcall
      dsimp only at hcall
      have hl := pan_two_word_lookup s1.code.lookup (ofString "memzero")
        (ofString "dst") (ofString "n") (sourceFnBody Guest.Software.guestFn_memzero)
        hp 176 (by decide) (by change s.code.lookup _ = _; rw [hcode]; exact lookup_memzero)
      rw [hl] at hcall
      dsimp only at hcall
      split at hcall
      · injection hcall with h1 _
        cases h1
        simp at hv1
      · rcases hmz : evaluateHOLFiniteState _ (sourceFnBody Guest.Software.guestFn_memzero) with
          ⟨rmz, smz⟩
        rw [hmz] at hcall
        cases rmz with
        | none =>
          dsimp only at hcall
          injection hcall with h1 _
          cases h1
          simp at hv1
        | some rmz' =>
          cases rmz' with
          | returned _ =>
            dsimp only at hcall
            split at hcall
            · injection hcall with h1 _; cases h1
            · injection hcall with h1 _; cases h1; simp at hv1
          | «break» | «continue» | error | timeOut | finalFfi _ | exception _ _ =>
            dsimp only at hcall
            injection hcall with h1 _
            cases h1
            simp at hv1
    | none =>
      dsimp only at hv1 ⊢
      -- Extract `sc` properties from `hcall : evaluate ... = (none, sc)`
      have hcall' := hcall
      rw [evaluateHOLFiniteState_call] at hcall'
      have hargs : evalListHOLFinite s1
          (h := fun a => Classical.propDecidable (s1.memaddrs a))
          [.var .local (ofString "m"), .const 176] =
          some [.val (.word hp), .val (.word 176)] := by
        simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, s1, L1,
          HolFiniteMapExact.lookup_update, FUPDATE]
      rw [hargs] at hcall'
      dsimp only at hcall'
      have hl := pan_two_word_lookup s1.code.lookup (ofString "memzero")
        (ofString "dst") (ofString "n") (sourceFnBody Guest.Software.guestFn_memzero)
        hp 176 (by decide) (by change s.code.lookup _ = _; rw [hcode]; exact lookup_memzero)
      rw [hl] at hcall'
      dsimp only at hcall'
      split at hcall'
      · cases hcall'
      · set centry := callEntryStateHOLFinite s1
          ((HolFiniteMapExact.empty.update (ofString "dst", .val (.word hp))).update
            (ofString "n", .val (.word 176)))
        have hmeta_mz := evaluateHOLFiniteState_metadata centry
          (sourceFnBody Guest.Software.guestFn_memzero)
        have hG_mz := guestInv_evaluate centry (sourceFnBody Guest.Software.guestFn_memzero)
          ⟨hG.code, hG.memaddrs, hG.shMemaddrs, hG.baseAddr⟩
        rcases hmz : evaluateHOLFiniteState centry (sourceFnBody Guest.Software.guestFn_memzero) with
          ⟨rmz, smz⟩
        rw [hmz] at hcall' hmeta_mz hG_mz
        cases rmz with
        | none => cases hcall'
        | some rmz' =>
          cases rmz' with
          | returned v_mz =>
            dsimp only at hcall'
            split at hcall'
            · injection hcall' with _ hsc
              have hcentry_dst : centry.locals.lookup (ofString "dst") = some (.val (.word hp)) := by
                simp [centry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                  show ofString "n" ≠ ofString "dst" by decide]
              have hcentry_n : centry.locals.lookup (ofString "n") = some (.val (.word 176)) := by
                simp [centry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
              have hmz_props := memzero_176_run centry hp hhp_al hdom_22 hcentry_dst hcentry_n
                v_mz (by rw [hmz])
              dsimp only at hmz_props
              rw [hmz] at hmz_props
              obtain ⟨hsmz_glob, hsmz_zero⟩ := hmz_props
              subst hsc
              -- Now evaluate `.return (.var .local "m")` from `{ smz with locals := s1.locals }`
              have hret_m : evaluateHOLFiniteState { smz with locals := s1.locals }
                  (.return (.var .local (ofString "m"))) =
                  (some (.returned (.val (.word hp))),
                    emptyLocalsHOLFinite { smz with locals := s1.locals }) := by
                rw [evaluateHOLFiniteState_return]
                simp [evalHOLExact, s1, L1, HolFiniteMapExact.lookup_update, FUPDATE,
                  shapeOfHOLExact, sizeOfShapeWithContextHOL]
              rw [hret_m] at hv1 ⊢
              injection hv1 with hv1'
              injection hv1' with hv1''
              subst hv1''
              dsimp only [emptyLocalsHOLFinite]
              refine ⟨hp, rfl, ?_⟩
              set post : PanSemStateFiniteExact 64 F :=
                { smz with
                  locals := HolFiniteMapExact.resVarEq HolFiniteMapExact.empty
                    (ofString "m", s.locals.lookup (ofString "m")) }
              change ArenaReady post ∧ AllocatorGrows s post ∧
                FreshBlock s post hp.toNat 176 ∧
                ∀ k, k < 22 → memW post (hp.toNat + 8 * k) = 0
              have hpost_glob : post.globals = G1 := hsmz_glob
              have hpost_hp : globN post "heap_ptr" = q.toNat := by
                unfold globN; rw [hpost_glob]
                simp [G1, HolFiniteMapExact.lookup_update, FUPDATE]
              have hpost_fp : globN post "frame_mem_ptr" = globN s "frame_mem_ptr" := by
                unfold globN; rw [hpost_glob]
                simp [G1, HolFiniteMapExact.lookup_update, FUPDATE,
                  show ofString "heap_ptr" ≠ ofString "frame_mem_ptr" by decide]
              have hpost_sp : globN post "scratch_ptr" = globN s "scratch_ptr" := by
                unfold globN; rw [hpost_glob]
                simp [G1, HolFiniteMapExact.lookup_update, FUPDATE,
                  show ofString "heap_ptr" ≠ ofString "scratch_ptr" by decide]
              have hG_post : GuestInv post :=
                ⟨hG_mz.code, hG_mz.memaddrs, hG_mz.shMemaddrs, hG_mz.baseAddr⟩
              have hA_post : ArenaOK post := by
                unfold ArenaOK
                rw [hpost_hp, hpost_fp, hpost_sp]
                exact ⟨by omega, hq_hi, hA.2.2.1, hA.2.2.2.1, hA.2.2.2.2.1,
                  hq_al, hA.2.2.2.2.2.2.1, hA.2.2.2.2.2.2.2.1,
                  globalsWord_update (s := s) (t := post) (ofString "heap_ptr") q hpost_glob hA.2.2.2.2.2.2.2.2⟩
              have hAG : AllocatorGrows s post := by
                refine ⟨?_, by rw [hpost_sp]⟩
                rw [hpost_hp, ← hhp_eq]; exact hp_le_q
              have hFB : FreshBlock s post hp.toNat 176 := by
                refine ⟨hhp_al, ?_, ?_⟩
                · change Inside (hp.toNat, 176) (globN s "heap_ptr") (globN post "heap_ptr")
                  rw [← hhp_eq, hpost_hp]
                  exact ⟨le_rfl, le_of_eq hq_eq.symm⟩
                · change WordsOK post (hp.toNat, 176)
                  exact wordsOK_of_guestInv post hG_post hp.toNat 176 hhp_al (by decide)
                    hsb_le (by omega)
              refine ⟨⟨hG_post, hA_post⟩, hAG, hFB, ?_⟩
              intro k hk
              unfold memW
              rw [ofNat_add_toNat_eq hp (8 * k)]
              change (match smz.memory (hp + BitVec.ofNat 64 (8 * k)) with | .word w => w.toNat) = 0
              rw [hsmz_zero k hk]
              rfl
            · cases hcall'
          | _ => cases hcall'
  exact hrun v hret

end InitECandidate.Solver.Wave8Contracts.M26
