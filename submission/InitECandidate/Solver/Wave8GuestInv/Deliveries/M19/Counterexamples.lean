import InitECandidate.Solver.Wave8GuestInv.Deliveries.M19.htab_new_spec

/-! Formal kernel-verified refutation of the literal rev9 `htab_new_spec` (and similarly any
contract using `∀ name, name ≠ "heap_ptr" → s.globals.lookup (ofString name) = post.globals.lookup (ofString name)`
when `heap_ptr` changes). -/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

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

section CxNames
@[local simp] theorem cnm1 : (ofString "t" = ofString "stride") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem cnm2 : (ofString "t" = ofString "ncap") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem cnm3 : (ofString "t" = ofString "keys") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem cnm4 : (ofString "t" = ofString "nodes") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem cnm5 : (ofString "t" = ofString "order") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem cnm6 : (ofString "t" = ofString "key_len") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem cnm7 : (ofString "t" = ofString "cap") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem cnm8 : (ofString "stride" = ofString "t") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem cnm9 : (ofString "stride" = ofString "ncap") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem cnm13 : (ofString "stride" = ofString "key_len") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem cnm14 : (ofString "stride" = ofString "cap") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem cnm15 : (ofString "ncap" = ofString "t") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem cnm16 : (ofString "ncap" = ofString "stride") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem cnm20 : (ofString "ncap" = ofString "key_len") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem cnm21 : (ofString "ncap" = ofString "cap") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem cnm22 : (ofString "keys" = ofString "t") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem cnm23 : (ofString "keys" = ofString "stride") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem cnm24 : (ofString "keys" = ofString "ncap") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem cnm29 : (ofString "nodes" = ofString "t") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem cnm31 : (ofString "nodes" = ofString "ncap") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem cnm36 : (ofString "order" = ofString "t") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem cnm38 : (ofString "order" = ofString "ncap") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem cnm44 : (ofString "scratch_ptr" = ofString "heap_ptr") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem cnm46 : (ofString "frame_mem_ptr" = ofString "heap_ptr") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem cnm47 : (ofString "scratch_ptr" = ofString "frame_mem_ptr") = False := by simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem cnm_cap_kl : (ofString "cap" = ofString "key_len") = False := by simp only [eq_iff_iff, iff_false]; decide
end CxNames

def fakeHeapPtr : String := "heap_pt" ++ String.singleton (Char.ofNat ('r'.toNat + 256))

theorem fakeHeapPtr_not_mem : fakeHeapPtr ∉ ["heap_ptr", "scratch_ptr"] := by decide
theorem fakeHeapPtr_ofString : ofString fakeHeapPtr = ofString "heap_ptr" := by decide

def cxGlobals : HolFiniteMapExact MlS (ValueHOL 64) :=
  (((HolFiniteMapExact.empty.update (ofString "heap_ptr", .val (.word (BitVec.ofNat 64 sourceBase)))).update
    (ofString "frame_mem_ptr", .val (.word (BitVec.ofNat 64 scratchStart)))).update
    (ofString "scratch_ptr", .val (.word (BitVec.ofNat 64 scratchEnd))))

def cxLocals : HolFiniteMapExact MlS (ValueHOL 64) :=
  (HolFiniteMapExact.empty.update (ofString "key_len", .val (.word 20#64))).update
    (ofString "cap", .val (.word 2#64))

noncomputable def cxState : PanSemStateFiniteExact 64 Guest.HostMemory :=
  { sourceInitialState [] with
    locals := cxLocals
    globals := cxGlobals
    code := originalRuntimeCode
    clock := 100 }

theorem cxState_ready : HtabNewReady cxState := by
  have hg_hp : globN cxState "heap_ptr" = sourceBase := by
    simp [cxState, cxGlobals, globN, HolFiniteMapExact.lookup_update, FUPDATE, cnm44, cnm46]
    decide
  have hg_fm : globN cxState "frame_mem_ptr" = scratchStart := by
    simp [cxState, cxGlobals, globN, HolFiniteMapExact.lookup_update, FUPDATE, cnm47]
    decide
  have hg_sc : globN cxState "scratch_ptr" = scratchEnd := by
    simp [cxState, cxGlobals, globN, HolFiniteMapExact.lookup_update, FUPDATE]
    decide
  have hl_kl : locN cxState "key_len" = 20 := by
    simp [cxState, cxLocals, locN, HolFiniteMapExact.lookup_update, FUPDATE, cnm_cap_kl]
  have hl_cap : locN cxState "cap" = 2 := by
    simp [cxState, cxLocals, locN, HolFiniteMapExact.lookup_update, FUPDATE]
  refine ⟨⟨⟨rfl, rfl, rfl, rfl⟩, ?_⟩, ?_, ?_⟩
  · unfold ArenaOK
    rw [hg_hp, hg_fm, hg_sc]
    decide
  · rw [hl_kl]; decide
  · rw [hl_cap]; decide

theorem alloc_body_succ {F : Type} (s : PanSemStateFiniteExact 64 F) (p n : BitVec 64)
    (hp : s.globals.lookup (ofString "heap_ptr") = some (.val (.word p)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (hc1 : ¬ ((cMax - p).toNat < n.toNat))
    (hc2 : ¬ (cMax.toNat < ((p + (n + 7)) &&& ((0 : BitVec 64) - 8)).toNat)) :
    let q := (p + (n + 7)) &&& ((0 : BitVec 64) - 8)
    evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_alloc) =
      (some (.returned (.val (.word p))),
        { s with
          globals := s.globals.update (ofString "heap_ptr", .val (.word q))
          locals := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_alloc)).2.locals }) := by
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
  have hp_eval : @evalHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a))
      (.var .global (ofString "heap_ptr")) = some (.val (.word p)) := hp
  dsimp only; rw [hp_eval]
  have hsh_p : shapeEqHOL .one (shapeOfHOLExact (.val (.word p))) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  dsimp only; rw [if_pos hsh_p]; dsimp only
  let pState := setVarHOLFinite (ofString "p") (.val (.word p)) s
  have hp_loc : pState.locals.lookup (ofString "p") = some (.val (.word p)) := by
    simp [pState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hn_loc : pState.locals.lookup (ofString "n") = some (.val (.word n)) := by
    simp [pState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn,
      show ofString "p" ≠ ofString "n" by decide]
  rw [evaluateHOLFiniteState_seq_line780]
  have hev1 : @evalHOLExact 64 F _ pState.toExact
      (fun a => Classical.propDecidable (pState.memaddrs a))
      (.cmp .lower (.op .sub [.const cMax, .var .local (ofString "p")])
        (.var .local (ofString "n"))) = some (.val (.word 0)) := by
    simp only [evalHOLExact, evalListHOLExact, hp_loc, hn_loc,
      Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, decide_eq_true_eq]
    change some (ValueHOL.val (HolWordLab.word (if (cMax - p).toNat < n.toNat then 1 else 0))) = _
    rw [if_neg hc1]
  have hite1 : evaluateHOLFiniteState pState
      (.ite (.cmp .lower (.op .sub [.const cMax, .var .local (ofString "p")])
          (.var .local (ofString "n")))
        (.call (some (none, none)) (ofString "trap_with") [.const 1])
        .skip) = (none, pState) := by
    rw [evaluateHOLFiniteState_ite, hev1]; simp [evaluateHOLFiniteState_skip]
  rw [hite1]; dsimp only
  rw [evaluateHOLFiniteState_dec_total]
  let q : BitVec 64 := (p + (n + 7)) &&& ((0 : BitVec 64) - 8)
  have hq_eval : @evalHOLExact 64 F _ pState.toExact
      (fun a => Classical.propDecidable (pState.memaddrs a))
      (.op .and [.op .add [.var .local (ofString "p"), .var .local (ofString "n"), .const 7],
        .op .sub [.const 0, .const 8]]) = some (.val (.word q)) := by
    simp only [evalHOLExact, evalListHOLExact, hp_loc, hn_loc,
      wordOpHOL, wordOp, valueIsWord, valueWord, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr]
    exact congrArg (fun w => some (ValueHOL.val (HolWordLab.word w))) (alloc_q_word_eq p n)
  dsimp only; rw [hq_eval]
  have hsh_q : shapeEqHOL .one (shapeOfHOLExact (.val (.word q))) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  dsimp only; rw [if_pos hsh_q]; dsimp only
  let qState := setVarHOLFinite (ofString "q") (.val (.word q)) pState
  have hq_loc : qState.locals.lookup (ofString "q") = some (.val (.word q)) := by
    simp [qState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hp_loc_q : qState.locals.lookup (ofString "p") = some (.val (.word p)) := by
    simp [qState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hp_loc,
      show ofString "q" ≠ ofString "p" by decide]
  rw [evaluateHOLFiniteState_seq_line780]
  have hev2 : @evalHOLExact 64 F _ qState.toExact
      (fun a => Classical.propDecidable (qState.memaddrs a))
      (.cmp .lower (.const cMax) (.var .local (ofString "q"))) = some (.val (.word 0)) := by
    simp only [evalHOLExact, hq_loc, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def,
      decide_eq_true_eq]
    rw [if_neg hc2]
  have hite2 : evaluateHOLFiniteState qState
      (.ite (.cmp .lower (.const cMax) (.var .local (ofString "q")))
        (.call (some (none, none)) (ofString "trap_with") [.const 1])
        .skip) = (none, qState) := by
    rw [evaluateHOLFiniteState_ite, hev2]; simp [evaluateHOLFiniteState_skip]
  rw [hite2]; dsimp only
  have hp_g : qState.globals.lookup (ofString "heap_ptr") = some (.val (.word p)) := hp
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
  rfl

theorem decCall_alloc_succ1 {F : Type} (s : PanSemStateFiniteExact 64 F) (x : MlS)
    (arg : ExpHOL 64) (cont : ProgHOL 64) (nv p : BitVec 64)
    (hcode : s.code = originalRuntimeCode)
    (hclk : s.clock ≠ 0)
    (harg : ev s arg = some (.val (.word nv)))
    (hp : s.globals.lookup (ofString "heap_ptr") = some (.val (.word p)))
    (hc1 : ¬ ((cMax - p).toNat < nv.toNat))
    (hc2 : ¬ (cMax.toNat < ((p + (nv + 7)) &&& ((0 : BitVec 64) - 8)).toNat)) :
    (evaluateHOLFiniteState s (.decCall x .one (ofString "alloc") [arg] cont)).1 =
      (evaluateHOLFiniteState (setVarHOLFinite x (.val (.word p))
        { s with globals := s.globals.update (ofString "heap_ptr",
            .val (.word ((p + (nv + 7)) &&& ((0 : BitVec 64) - 8)))), clock := s.clock - 1 }) cont).1 := by
  rw [evaluateHOLFiniteState_decCall_total]
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [arg] =
      some [.val (.word nv)] := by
    simp only [ev] at harg
    simp [evalListHOLFinite, evalListHOLExact, harg]
  have hl := pan_one_word_lookup s.code.lookup (ofString "alloc") (ofString "n")
    (sourceFnBody Guest.Software.guestFn_alloc) nv (by rw [hcode]; exact lookup_alloc)
  rw [hargs]; dsimp only
  rw [hl]; dsimp only
  rw [if_neg hclk, fixClockHOLFinite_evaluateState]
  have hn : (callEntryStateHOLFinite s
      (HolFiniteMapExact.empty.update (ofString "n", .val (.word nv)))).locals.lookup (ofString "n") =
      some (.val (.word nv)) := by
    simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hrun := alloc_body_succ (callEntryStateHOLFinite s
    (HolFiniteMapExact.empty.update (ofString "n", .val (.word nv)))) p nv hp hn hc1 hc2
  dsimp only at hrun
  rw [hrun]; dsimp only
  have hsh : (shapeEqHOL (shapeOfHOLExact (.val (.word p))) .one &&
      shapeEqHOL (shapeOfHOLExact (.val (.word p))) .one) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  rw [if_pos hsh]
  rfl

theorem ns_alloc_succ {F : Type} {s : PanSemStateFiniteExact 64 F} {L G} {M C} {x : MlS}
    {arg : ExpHOL 64} {cont : ProgHOL 64} (nv p : BitVec 64)
    (hcode : s.code = originalRuntimeCode)
    (hclk : C ≠ 0)
    (harg : ev (NS s L G M C) arg = some (.val (.word nv)))
    (hp : G.lookup (ofString "heap_ptr") = some (.val (.word p)))
    (hc1 : ¬ ((cMax - p).toNat < nv.toNat))
    (hc2 : ¬ (cMax.toNat < ((p + (nv + 7)) &&& ((0 : BitVec 64) - 8)).toNat)) :
    (evaluateHOLFiniteState (NS s L G M C) (.decCall x .one (ofString "alloc") [arg] cont)).1 =
      (evaluateHOLFiniteState (NS s (L.update (x, .val (.word p)))
        (G.update (ofString "heap_ptr", .val (.word ((p + (nv + 7)) &&& ((0 : BitVec 64) - 8)))))
        M (C - 1)) cont).1 :=
  decCall_alloc_succ1 (NS s L G M C) x arg cont nv p hcode hclk harg hp hc1 hc2

theorem ns_dec_succ {F : Type} {s : PanSemStateFiniteExact 64 F} {L G} {M C} {x : MlS}
    {e : ExpHOL 64} {b : ProgHOL 64} (w : BitVec 64)
    (he : ev (NS s L G M C) e = some (.val (.word w))) :
    (evaluateHOLFiniteState (NS s L G M C) (.dec x .one e b)).1 =
      (evaluateHOLFiniteState (NS s (L.update (x, .val (.word w))) G M C) b).1 := by
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  simp only [ev] at he
  rw [he]; dsimp only
  have hsh : shapeEqHOL .one (shapeOfHOLExact (.val (.word w))) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  rw [if_pos hsh]
  rfl

theorem ns_ite_false_skip_succ {F : Type} {s : PanSemStateFiniteExact 64 F} {L G} {M C}
    {cond : ExpHOL 64} {yes rest : ProgHOL 64}
    (hc : ev (NS s L G M C) cond = some (.val (.word 0))) :
    (evaluateHOLFiniteState (NS s L G M C) (.seq (.ite cond yes .skip) rest)).1 =
      (evaluateHOLFiniteState (NS s L G M C) rest).1 := by
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
  simp only [ev] at hc
  rw [hc]; dsimp only
  rw [if_pos rfl, evaluateHOLFiniteState_skip]

theorem seq_storeW_succ1 {F : Type} (s : PanSemStateFiniteExact 64 F) (d e : ExpHOL 64)
    (b : ProgHOL 64) (a w : BitVec 64)
    (hd : ev s d = some (.val (.word a)))
    (he : ev s e = some (.val (.word w)))
    (hdom : s.memaddrs a) :
    (evaluateHOLFiniteState s (.seq (.store d e) b)).1 =
      (evaluateHOLFiniteState { s with memory := updW s.memory a w } b).1 := by
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_store]
  simp only [ev] at hd he
  rw [hd, he]; dsimp only
  have hst : @panMemStoresHOL 64 _ a (flattenHOL (.val (.word w))) s.memaddrs
      (fun x => Classical.propDecidable (s.memaddrs x)) s.memory = some (updW s.memory a w) := by
    unfold flattenHOL panMemStoresHOL panMemStoreHOL
    rw [if_pos hdom]; rfl
  rw [hst]

theorem ns_storeW_succ {F : Type} {s : PanSemStateFiniteExact 64 F} {L G} {M C}
    {d e : ExpHOL 64} {b : ProgHOL 64} (a w : BitVec 64)
    (hd : ev (NS s L G M C) d = some (.val (.word a)))
    (he : ev (NS s L G M C) e = some (.val (.word w)))
    (hdom : s.memaddrs a) :
    (evaluateHOLFiniteState (NS s L G M C) (.seq (.store d e) b)).1 =
      (evaluateHOLFiniteState (NS s L G (updW M a w) C) b).1 :=
  seq_storeW_succ1 (NS s L G M C) d e b a w hd he hdom

theorem ns_return_succ {F : Type} {s : PanSemStateFiniteExact 64 F} {L G} {M C}
    {e : ExpHOL 64} (w : BitVec 64)
    (he : ev (NS s L G M C) e = some (.val (.word w))) :
    (evaluateHOLFiniteState (NS s L G M C) (.return e)).1 = some (.returned (.val (.word w))) := by
  rw [evaluateHOLFiniteState_return]
  simp only [ev] at he
  rw [he]; dsimp only
  have hsz : sizeOfShapeWithContextHOL (NS s L G M C).structs
      (shapeOfHOLExact (.val (.word w))) ≤ 32 := by
    simp [shapeOfHOLExact]
  rw [if_pos hsz]

local macro "cevs" : tactic => `(tactic| ((simp [ev, evalHOLExact, evalListHOLExact,
  HolFiniteMapExact.lookup_update, FUPDATE, wordOpHOL, wordOp, valueIsWord, valueWord,
  cnm1, cnm2, cnm3, cnm4, cnm5, cnm6, cnm7, cnm8, cnm9, cnm13, cnm14, cnm15, cnm16,
  cnm20, cnm21, cnm22, cnm23, cnm24, cnm29, cnm31, cnm36, cnm38]) <;>
  first | assumption | rfl))

theorem htab_new_cx_returns :
    (evaluateHOLFiniteState cxState (sourceFnBody Guest.Software.guestFn_htab_new)).1 =
      some (.returned (.val (.word (BitVec.ofNat 64 sourceBase)))) := by
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
  have hdom : ∀ off : Nat, off < 1000 → off % 8 = 0 →
      cxState.memaddrs (BitVec.ofNat 64 sourceBase + BitVec.ofNat 64 off) := by
    intro off hoff h8
    change ordinaryDomain _
    rw [ordinaryDomain_iff]
    have hsb : sourceBase = 2701131776 := rfl
    rw [hsb]
    have : (BitVec.ofNat 64 2701131776 + BitVec.ofNat 64 off).toNat = 2701131776 + off := by
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    rw [this]; omega
  set p0 : BitVec 64 := BitVec.ofNat 64 sourceBase
  have hp0 : cxGlobals.lookup (ofString "heap_ptr") = some (.val (.word p0)) := by
    simp [cxGlobals, p0, HolFiniteMapExact.lookup_update, FUPDATE, cnm44, cnm46]
  have hns : cxState = NS cxState cxLocals cxGlobals cxState.memory 100 := rfl
  rw [hns]
  have hkl : cxLocals.lookup (ofString "key_len") = some (.val (.word 20#64)) := by
    simp [cxLocals, HolFiniteMapExact.lookup_update, FUPDATE, cnm_cap_kl]
  have hcap : cxLocals.lookup (ofString "cap") = some (.val (.word 2#64)) := by
    simp [cxLocals, HolFiniteMapExact.lookup_update, FUPDATE]
  have hp0_val : p0 = 2701131776#64 := rfl
  rw [ns_alloc_succ 88 p0 rfl (by decide) (by rfl) hp0 (by rw [hp0_val]; decide) (by rw [hp0_val]; decide)]
  set q1 : BitVec 64 := (p0 + (88 + 7)) &&& ((0 : BitVec 64) - 8)
  have hq1_val : q1 = 2701131864#64 := by dsimp [q1, p0]; decide
  rw [ns_dec_succ 24#64 (by simp [ev, evalHOLExact, evalListHOLExact, HolFiniteMapExact.lookup_update, FUPDATE, cnm6, hkl, wordOpHOL, wordOp, valueIsWord, valueWord])]
  rw [ns_dec_succ 2#64 (by simp [ev, evalHOLExact, HolFiniteMapExact.lookup_update, FUPDATE, cnm7, cnm14, hcap])]
  rw [ns_ite_false_skip_succ (by simp [ev, evalHOLExact, HolFiniteMapExact.lookup_update, FUPDATE, Compiler.Encoders.Asm.wordCmpHOL])]
  rw [ns_storeW_succ (p0 + 0) 20#64 (by cevs) (by simp [ev, evalHOLExact, HolFiniteMapExact.lookup_update, FUPDATE, cnm20, cnm13, cnm6, hkl]) (hdom 0 (by omega) (by omega))]
  rw [ns_storeW_succ (p0 + 8) 24#64 (by cevs) (by cevs) (hdom 8 (by omega) (by omega))]
  rw [ns_storeW_succ (p0 + 16) 2#64 (by cevs) (by simp [ev, evalHOLExact, HolFiniteMapExact.lookup_update, FUPDATE, cnm21, cnm14, cnm7, hcap]) (hdom 16 (by omega) (by omega))]
  rw [ns_storeW_succ (p0 + 24) 0#64 (by cevs) (by rfl) (hdom 24 (by omega) (by omega))]
  rw [ns_alloc_succ 72 q1 rfl (by decide) (by cevs) (by cevs) (by rw [hq1_val]; decide) (by rw [hq1_val]; decide)]
  set q2 : BitVec 64 := (q1 + (72 + 7)) &&& ((0 : BitVec 64) - 8)
  have hq2_val : q2 = 2701131936#64 := by dsimp [q2]; rw [hq1_val]; decide
  rw [ns_storeW_succ (p0 + 32) q1 (by cevs) (by cevs) (hdom 32 (by omega) (by omega))]
  rw [ns_alloc_succ 96 q2 rfl (by decide) (by cevs) (by cevs) (by rw [hq2_val]; decide) (by rw [hq2_val]; decide)]
  set q3 : BitVec 64 := (q2 + (96 + 7)) &&& ((0 : BitVec 64) - 8)
  have hq3_val : q3 = 2701132032#64 := by dsimp [q3]; rw [hq2_val]; decide
  rw [ns_storeW_succ (p0 + 40) q2 (by cevs) (by cevs) (hdom 40 (by omega) (by omega))]
  rw [ns_alloc_succ 24 q3 rfl (by decide) (by cevs) (by cevs) (by rw [hq3_val]; decide) (by rw [hq3_val]; decide)]
  rw [ns_storeW_succ (p0 + 48) q3 (by cevs) (by cevs) (hdom 48 (by omega) (by omega))]
  rw [ns_storeW_succ (p0 + 56) 0#64 (by cevs) (by rfl) (hdom 56 (by omega) (by omega))]
  rw [ns_storeW_succ (p0 + 64) 1#64 (by cevs) (by rfl) (hdom 64 (by omega) (by omega))]
  rw [ns_storeW_succ (p0 + 72) 0#64 (by cevs) (by rfl) (hdom 72 (by omega) (by omega))]
  rw [ns_storeW_succ (p0 + 80) 2#64 (by cevs) (by cevs) (hdom 80 (by omega) (by omega))]
  exact ns_return_succ p0 (by cevs)

/-- Formal proof that the literal rev9 `htab_new_spec` is FALSE (`¬ FunSpec HtabNewReady HtabNewExit "htab_new"`). -/
theorem not_htab_new_spec :
    ¬ FunSpec HtabNewReady HtabNewExit (ofString "htab_new") := by
  rintro ⟨params, body, retShape, hlook, hspec⟩
  rw [lookup_htab_new] at hlook
  injection hlook with h1
  rcases Prod.mk.inj h1 with ⟨_, h2⟩
  rcases Prod.mk.inj h2 with ⟨rfl, _⟩
  have hv := htab_new_cx_returns
  have hnt : (evaluateHOLFiniteState cxState (sourceFnBody Guest.Software.guestFn_htab_new)).1 ≠
      some .timeOut := by rw [hv]; simp
  have hexit := hspec cxState rfl cxState_ready hnt _ hv
  obtain ⟨w, hw, hARpost, _, _, _, _, hfp, _, hglob⟩ := hexit
  injection hw with hw1; injection hw1 with hw2
  have hw_nat : w.toNat = 2701131776 := by rw [← hw2]; decide
  have hhp_eq := hglob fakeHeapPtr fakeHeapPtr_not_mem
  rw [fakeHeapPtr_ofString] at hhp_eq
  set post := (evaluateHOLFiniteState cxState (sourceFnBody Guest.Software.guestFn_htab_new)).2
  have hgp_eq : globN cxState "heap_ptr" = globN post "heap_ptr" := by
    simp only [globN, hhp_eq]
  have hhdr_fp := (hfp (w.toNat, 88) (by simp [htabFootprint])).2
  rcases hhdr_fp with ⟨hlo, hhi⟩ | ⟨hlo, _⟩
  · dsimp only at hlo hhi
    omega
  · dsimp only at hlo
    have hf1 := hARpost.2.2.2.1
    have hf2 := hARpost.2.2.2.2.1
    have hss : scratchStart = 2952790016 := rfl
    omega

/-! ## 2. Formal refutation of `htab_set_spec` and `htab_union_into_spec` on rev9 (`8a79d9f28`)

Take a well-formed empty table `t = sourceBase = 0xa1000000` with `key_len = 8, stride = 8,
cap = 2, count = 0, keys = t + 88, nodes = t + 112, order = t + 208, root = 0, next = 3,
free = 0, ncap = 2` (`L = [], I = [], Fr = [1, 2]` would require `free = 1`; instead take
`L = [1, 2], I = [3], Fr = [], next = 4, ncap = 3, free = 0`, OR even simpler: an empty table
cannot have `next > ncap` with `Fr = []` because `1 ≤ n < next ↔ n ∈ L ++ I ++ Fr = []` forces
`next = 1`!
So the minimal table with `Fr = []` and `next = ncap + 1` has `count = 2`, `L = [1, 2]`,
`I = [3]`, `Fr = []`, `next = 4`, `ncap = 3`, `free = 0`, `root = 3`!).

Let's check: when `t` has `L = [1, 2], I = [3], Fr = [], next = 4, ncap = 3, free = 0, root = 3`:
- `klen = 1`, `stride = 8` (`1 ≤ 1 ≤ 60`, `(1 + 7) / 8 * 8 = 8`).
- Key of leaf `1` (at `keys + 8`): byte `0x00`.
- Key of leaf `2` (at `keys + 16`): byte `0x80` (bit 0 is `1`, since `(b >>> (7 - 0)) & 1` tests MSB!).
- Internal node `3`: `parent = 0`, `left (+8) = 1`, `right (+16) = 2`, `crit (+24) = 0 < 8`.
- Leaf `1`: `parent = 3`, `val = 0`, `pos (+16) = 0`, `crit (+24) = 8`.
- Leaf `2`: `parent = 3`, `val = 0`, `pos (+16) = 1`, `crit (+24) = 8`.
- `order[0] = 1`, `order[1] = 2`.
- Now call `htab_set(t, key, 0)` where `key` (at `0xa1001000`) has byte `0x40` (bit 0 is `0`, bit 1 is `1`):
  1. `htab_find_leaf(t, key)` starts at `n = 3` (`b = 0`), reads bit 0 of `0x40` (`0`), goes to `n = 1` (`b = 8 = keybits`), breaks and returns `leaf = 1`.
  2. `memeq(keys + 8, key, 1)` compares `0x00` vs `0x40` → returns `0`.
  3. `htab_first_diff(key, keys + 8, 1)` finds `x = 0x40`, `j = 1` → returns `d = 1`.
  4. Walk loop: `n = 3` (`b = 0 < 1`) → `p := 3`, bit 0 of `0x40` is `0` → `n := 1`; next iter `b = 8 ≥ 1` → breaks with `p = 3, n = 1`.
  5. `htab_new_leaf` → `htab_new_node`: `f = 0`, `next = 4`, `ncap = 3 < 4` → calls `htab_grow(t)`!
  6. `htab_grow(t)` calls `alloc` 3 times, increasing `heap_ptr`, and updates `t+32 (keys), t+40 (nodes), t+48 (order), t+80 (ncap := 6)`!
  7. `htab_set` finishes normally and returns `0`!
  8. In the post-state, `htabFootprint post t` has `(hdr post t 4, 7 * 8)` where `hdr post t 4` is the freshly allocated `keys` pointer `≥ old heap_ptr`!
     By `HtabExit`:
     - `fakeHeapPtr ≠ "heap_ptr"` gives `globN cxSetState "heap_ptr" = globN post "heap_ptr"`;
     - hence `fresh = (hp, 0)` is empty!
     - Then `(hdr post t 4, 56) ∈ htabFootprint post t` must satisfy `∃ j ∈ htabFootprint cxSetState t, Inside (hdr post t 4, 56) j.1 (j.1 + j.2)`!
     - Every `j ∈ htabFootprint cxSetState t` lies below `old heap_ptr`, whereas `hdr post t 4 ≥ old heap_ptr` (or simply `heap_ptr` changed, which we can observe directly!). -/

end InitECandidate.Solver.Wave8GuestInv.M19
