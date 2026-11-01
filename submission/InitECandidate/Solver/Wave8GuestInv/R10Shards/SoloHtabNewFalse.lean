import InitECandidate.Solver.Wave8GuestInv.ContractParts.C00
import InitECandidate.Solver.HeapPotential

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.Wave8GuestInv.R10Shards

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.Wave8GuestInv

def fakeHeapPtr : String := "heap_pt" ++ String.singleton (Char.ofNat ('r'.toNat + 256))

theorem fakeHeapPtr_not_mem : fakeHeapPtr ∉ ["heap_ptr", "scratch_ptr"] := by decide

theorem fakeHeapPtr_ofString : ofString fakeHeapPtr = ofString "heap_ptr" := by decide

section CxNames
@[local simp] theorem cnm_sc_hp : (ofString "scratch_ptr" = ofString "heap_ptr") = False := by
  simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem cnm_fm_hp : (ofString "frame_mem_ptr" = ofString "heap_ptr") = False := by
  simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem cnm_sc_fm : (ofString "scratch_ptr" = ofString "frame_mem_ptr") = False := by
  simp only [eq_iff_iff, iff_false]; decide
@[local simp] theorem cnm_cap_kl : (ofString "cap" = ofString "key_len") = False := by
  simp only [eq_iff_iff, iff_false]; decide
end CxNames

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
    clock := 100000 }

theorem cx_glob (n : String) (w : BitVec 64)
    (h : cxGlobals.lookup (ofString n) = some (.val (.word w))) :
    globN cxState n = w.toNat := by
  simp [globN, cxState, h]

theorem cxState_ready : HtabNewReady cxState := by
  have hg_hp : globN cxState "heap_ptr" = sourceBase := by
    simp [cxState, cxGlobals, globN, HolFiniteMapExact.lookup_update, FUPDATE, cnm_sc_hp, cnm_fm_hp]
    decide
  have hg_fm : globN cxState "frame_mem_ptr" = scratchStart := by
    simp [cxState, cxGlobals, globN, HolFiniteMapExact.lookup_update, FUPDATE, cnm_sc_fm]
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

def htabNewBody : ProgHOL 64 :=
  InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
    (extractFn Guest.Software.guestFn_htab_new).body



section Step
variable {F : Type}

theorem alloc_result {s : PanSemStateFiniteExact 64 F} (p n : BitVec 64)
    (hp : s.globals.lookup (ofString "heap_ptr") = some (.val (.word p)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (hc1 : ¬ ((cMax - p).toNat < n.toNat))
    (hc2 : ¬ (cMax.toNat < ((p + (n + 7)) &&& ((0 : BitVec 64) - 8)).toNat)) :
    let q := (p + (n + 7)) &&& ((0 : BitVec 64) - 8)
    evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_alloc) =
      (some (.returned (.val (.word p))),
        { s with
          locals := HolFiniteMapExact.resVarEq
            (HolFiniteMapExact.resVarEq HolFiniteMapExact.empty
              (ofString "q", s.locals.lookup (ofString "q")))
            (ofString "p", s.locals.lookup (ofString "p")),
          globals := s.globals.update (ofString "heap_ptr", .val (.word q)) }) := by
  classical
  simp only
  have hbody : sourceFnBody Guest.Software.guestFn_alloc =
      .dec (ofString "p") .one (ExpHOL.var .global (ofString "heap_ptr"))
        (.seq
          (.ite (.cmp .lower (.op .sub [.const cMax, ExpHOL.var .local (ofString "p")])
              (ExpHOL.var .local (ofString "n")))
            (.call (some (none, none)) (ofString "trap_with") [.const 1]) .skip)
          (.dec (ofString "q") .one
            (.op .and [.op .add [ExpHOL.var .local (ofString "p"), ExpHOL.var .local (ofString "n"), .const 7],
              .op .sub [.const 0, .const 8]])
            (.seq
              (.ite (.cmp .lower (.const cMax) (ExpHOL.var .local (ofString "q")))
                (.call (some (none, none)) (ofString "trap_with") [.const 1]) .skip)
              (.seq (ProgHOL.assign .global (ofString "heap_ptr") (ExpHOL.var .local (ofString "q")))
                (ProgHOL.return (ExpHOL.var .local (ofString "p"))))))) := rfl
  have hpn : ofString "p" ≠ ofString "n" := by decide
  have hpq : ofString "p" ≠ ofString "q" := by decide
  have hqn : ofString "q" ≠ ofString "n" := by decide
  rw [hbody, evaluateHOLFiniteState_dec_total]
  have hinit : @evalHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a))
      (ExpHOL.var .global (ofString "heap_ptr")) = some (.val (.word p)) := hp
  simp only [hinit]
  have hsh : shapeEqHOL .one (shapeOfHOLExact (.val (.word p))) = true := by
    simp [shapeOfHOLExact, shapeEqHOL]
  simp only [hsh, ite_true]
  set st1 := setVarHOLFinite (ofString "p") (.val (.word p)) s
  have hpL : st1.locals.lookup (ofString "p") = some (.val (.word p)) := by
    simp [st1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hnL : st1.locals.lookup (ofString "n") = some (.val (.word n)) := by
    simpa [st1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hpn] using hn
  have hite1 : evaluateHOLFiniteState st1
      (.ite (.cmp .lower (.op .sub [.const cMax, ExpHOL.var .local (ofString "p")])
          (ExpHOL.var .local (ofString "n")))
        (.call (some (none, none)) (ofString "trap_with") [.const 1]) .skip) = (none, st1) := by
    rw [evaluateHOLFiniteState_ite]
    have hsub : @evalHOLExact 64 F _ st1.toExact
        (fun a => Classical.propDecidable (st1.memaddrs a))
        (.op .sub [.const cMax, ExpHOL.var .local (ofString "p")]) = some (.val (.word (cMax - p))) := by
      simp [evalHOLExact, evalListHOLExact, hpL, wordOpHOL, wordOp, valueIsWord, valueWord]
    have hnE : @evalHOLExact 64 F _ st1.toExact
        (fun a => Classical.propDecidable (st1.memaddrs a))
        (ExpHOL.var .local (ofString "n")) = some (.val (.word n)) := hnL
    have hcmp : @evalHOLExact 64 F _ st1.toExact
        (fun a => Classical.propDecidable (st1.memaddrs a))
        (.cmp .lower (.op .sub [.const cMax, ExpHOL.var .local (ofString "p")])
          (ExpHOL.var .local (ofString "n"))) = some (.val (.word 0)) := by
      unfold evalHOLExact
      rw [hsub, hnE]
      simp only [Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, decide_eq_true_eq]
      rw [if_neg hc1]
    simp [hcmp, evaluateHOLFiniteState_skip]
  simp only [evaluateHOLFiniteState_seq_line780, hite1]
  have hqE : @evalHOLExact 64 F _ st1.toExact
      (fun a => Classical.propDecidable (st1.memaddrs a))
      (.op .and [.op .add [ExpHOL.var .local (ofString "p"), ExpHOL.var .local (ofString "n"), .const 7],
        .op .sub [.const 0, .const 8]]) =
      some (.val (.word ((p + (n + 7)) &&& ((0 : BitVec 64) - 8)))) := by
    simp only [evalHOLExact, evalListHOLExact, hpL, hnL, wordOpHOL, wordOp, valueIsWord, valueWord]
    change some (ValueHOL.val (HolWordLab.word ((p + (n + 7)) &&& (((0:BitVec 64) - 8) &&& (~~~(0:BitVec 64)))))) = _
    rw [show (~~~(0:BitVec 64)) = BitVec.allOnes 64 by decide]
    rw [← BitVec.and_assoc, BitVec.and_allOnes]
  rw [evaluateHOLFiniteState_dec_total]
  simp only [hqE]
  have hshq : shapeEqHOL .one (shapeOfHOLExact (.val (.word ((p + (n + 7)) &&& ((0 : BitVec 64) - 8))))) = true := by
    simp [shapeOfHOLExact, shapeEqHOL]
  simp only [hshq, ite_true]
  set q : BitVec 64 := (p + (n + 7)) &&& ((0 : BitVec 64) - 8)
  set st2 := setVarHOLFinite (ofString "q") (.val (.word q)) st1
  have hqL : st2.locals.lookup (ofString "q") = some (.val (.word q)) := by
    simp [st2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hpL2 : st2.locals.lookup (ofString "p") = some (.val (.word p)) := by
    have hpq' : (ofString "q" == ofString "p") = false := by
      simpa [beq_iff_eq] using Ne.symm hpq
    simp [st2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hpq', hpL]
  have hite2 : evaluateHOLFiniteState st2
      (.ite (.cmp .lower (.const cMax) (ExpHOL.var .local (ofString "q")))
        (.call (some (none, none)) (ofString "trap_with") [.const 1]) .skip) = (none, st2) := by
    rw [evaluateHOLFiniteState_ite]
    have hcmp : @evalHOLExact 64 F _ st2.toExact
        (fun a => Classical.propDecidable (st2.memaddrs a))
        (.cmp .lower (.const cMax) (ExpHOL.var .local (ofString "q"))) = some (.val (.word 0)) := by
      have hc : @evalHOLExact 64 F _ st2.toExact
          (fun a => Classical.propDecidable (st2.memaddrs a))
          (.const cMax) = some (.val (.word cMax)) := rfl
      have hqv0 : @evalHOLExact 64 F _ st2.toExact
          (fun a => Classical.propDecidable (st2.memaddrs a))
          (ExpHOL.var .local (ofString "q")) = some (.val (.word q)) := hqL
      unfold evalHOLExact
      rw [hc, hqv0]
      simp only [Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, decide_eq_true_eq]
      rw [if_neg hc2]
    simp [hcmp, evaluateHOLFiniteState_skip]
  simp only [evaluateHOLFiniteState_seq_line780, hite2]
  have hqv : @evalHOLExact 64 F _ st2.toExact
      (fun a => Classical.propDecidable (st2.memaddrs a))
      (ExpHOL.var .local (ofString "q")) = some (.val (.word q)) := hqL
  have hst1g : st1.globals = s.globals := rfl
  have hvalid : isValidValueHOLFinite st2 .global (ofString "heap_ptr") (.val (.word q)) = true := by
    simp only [isValidValueHOLFinite, lookupKvarHOLFinite, st2, setVarHOLFinite, hst1g, hp,
      shapeEqHOL, shapeOfHOLExact]
  have hassign : evaluateHOLFiniteState st2
      (ProgHOL.assign .global (ofString "heap_ptr") (ExpHOL.var .local (ofString "q"))) =
      (none, setGlobalHOLFinite (ofString "heap_ptr") (.val (.word q)) st2) := by
    rw [evaluateHOLFiniteState_assign]
    simp only [hqv, hvalid, ite_true, setKvarHOLFinite, setGlobalHOLFinite]
  simp only [hassign]
  rw [evaluateHOLFiniteState_return]
  have hret : @evalHOLExact 64 F _ (setGlobalHOLFinite (ofString "heap_ptr") (.val (.word q)) st2).toExact
      (fun a => Classical.propDecidable
        ((setGlobalHOLFinite (ofString "heap_ptr") (.val (.word q)) st2).memaddrs a))
      (ExpHOL.var .local (ofString "p")) = some (.val (.word p)) := by
    rw [evalHOLExact]
    simpa [setGlobalHOLFinite] using hpL2
  simp only [hret]
  have hsz : Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL st2.structs
      (shapeOfHOLExact (.val (.word p))) ≤ 32 := by
    simp [shapeOfHOLExact, st2]
  simp only [setGlobalHOLFinite, hsz, ite_true, emptyLocalsHOLFinite]
  rfl


theorem decCall_alloc {s : PanSemStateFiniteExact 64 F} (x : MlS) (arg : ExpHOL 64)
    (cont : ProgHOL 64) (nv p : BitVec 64)
    (hcode : s.code = originalRuntimeCode) (hclk : s.clock ≠ 0)
    (harg : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) arg =
      some (.val (.word nv)))
    (hp : s.globals.lookup (ofString "heap_ptr") = some (.val (.word p)))
    (hc1 : ¬ ((cMax - p).toNat < nv.toNat))
    (hc2 : ¬ (cMax.toNat < ((p + (nv + 7)) &&& ((0 : BitVec 64) - 8)).toNat)) :
    evaluateHOLFiniteState s (.decCall x .one (ofString "alloc") [arg] cont) =
      let contState := setVarHOLFinite x (.val (.word p))
        { s with
          globals := s.globals.update (ofString "heap_ptr",
            .val (.word ((p + (nv + 7)) &&& ((0 : BitVec 64) - 8)))),
          clock := s.clock - 1 }
      let contOutput := evaluateHOLFiniteState contState cont
      (contOutput.1, { contOutput.2 with
        locals := HolFiniteMapExact.resVarEq contOutput.2.locals (x, s.locals.lookup x) }) := by
  classical
  rw [evaluateHOLFiniteState_decCall_total]
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [arg] =
      some [.val (.word nv)] := by
    simp [evalListHOLFinite, evalListHOLExact, harg]
  rw [hargs]
  have hl : lookupCodeHOLFinite s.code.lookup (ofString "alloc") [.val (.word nv)] =
      some (sourceFnBody Guest.Software.guestFn_alloc,
        HolFiniteMapExact.empty.update (ofString "n", .val (.word nv)), .one) :=
    pan_one_word_lookup s.code.lookup (ofString "alloc") (ofString "n")
      (sourceFnBody Guest.Software.guestFn_alloc) nv (by rw [hcode]; exact lookup_alloc)
  set entry := callEntryStateHOLFinite s
    (HolFiniteMapExact.empty.update (ofString "n", .val (.word nv)))
  have hrun := alloc_result (s := entry) p nv
    (by simpa [entry, callEntryStateHOLFinite] using hp)
    (by simp [entry, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]) hc1 hc2
  simp only at hrun
  generalize hvals : [ValueHOL.val (HolWordLab.word nv)] = vals at hl ⊢
  beta_reduce
  simp only [hl, if_neg hclk]
  have hent : callEntryStateHOLFinite s
      (HolFiniteMapExact.empty.update (ofString "n", .val (.word nv))) = entry := rfl
  simp only [hent, hrun, fixClockHOLFinite, shapeEqHOL, shapeOfHOLExact, ite_true]
  simp only [entry, callEntryStateHOLFinite]
  have hlt : (s.clock - 1 < s.clock - 1) = False := by simp
  simp only [hlt, ite_false]
  simp only [Bool.and_self, beq_self_eq_true, ite_true]

end Step

#print axioms alloc_result
#print axioms decCall_alloc

end InitECandidate.Solver.Wave8GuestInv.R10Shards
