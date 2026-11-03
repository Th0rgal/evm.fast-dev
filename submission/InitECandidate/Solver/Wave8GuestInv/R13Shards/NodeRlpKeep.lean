import InitECandidate.Solver.Wave8GuestInv.ContractParts.C03
import InitECandidate.Solver.GuestGlobalKeep
import InitECandidate.Solver.HeapPotential

/-! Node RLP encoding arena preservation (`ak__node_rlp_begin` and `ak__node_rlp_finish`). -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.style.nameCheck false

namespace InitECandidate.Solver.Wave8GuestInv.R13NodeRlpKeep

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

namespace R13NodeRlp

def encodingGood (f : MlS) : Bool :=
  (["_node_rlp_begin", "_node_rlp_finish", "alloc", "keccak256", "keccak_absorb_block",
    "keccak_f1600", "memcpy", "memzero", "mpt_fail", "nibble_list_to_compact",
    "node_hash_cached", "node_ref_len", "node_write_ref", "rlp_be_len",
    "rlp_bytes_encoded_len", "rlp_encode_bytes", "rlp_encode_list_header",
    "rlp_header_len", "rlp_list_header_len", "rlp_put_be", "rlp_value_encoded_len",
    "rlp_write_header", "trap_with"] : List String).map ofString |>.contains f

private def heapSafeProg : ProgHOL 64 → Bool
  | .dec _ _ _ body => heapSafeProg body
  | .seq first second => heapSafeProg first && heapSafeProg second
  | .ite _ yes no => heapSafeProg yes && heapSafeProg no
  | .while _ body => heapSafeProg body
  | .assign .local _ _ => true
  | .store _ _ | .storeByte _ _ | .shMemStore _ _ _ => true
  | .skip | .break | .continue | .annot _ _ | .raise _ _ | .return _ => true
  | .extCall _ _ _ _ _ | .primitive _ _ _ => true
  | .decCall _ _ function _ continuation => encodingGood function && heapSafeProg continuation
  | .call none function _ => encodingGood function
  | .call (some (none, none)) function _ => encodingGood function
  | .call (some (some (.local, _), none)) function _ => encodingGood function
  | _ => false

private theorem lookup_alloc :
    originalRuntimeCode.lookup (ofString "alloc") =
      some ([(ofString "n", .one)], sourceFnBody Guest.Software.guestFn_alloc, .one) :=
  lookup_of_guestAst_getElem 7 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_alloc) rfl

private theorem lookup_memzero :
    originalRuntimeCode.lookup (ofString "memzero") =
      some ([(ofString "dst", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_memzero, .one) :=
  lookup_of_guestAst_getElem 17 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_memzero) rfl

private theorem alloc_body_heap_mono {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hA : ArenaOK s) :
    let post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_alloc)).2
    ArenaOK post ∧ globN s "heap_ptr" ≤ globN post "heap_ptr" := by
  dsimp only
  have hbody : sourceFnBody Guest.Software.guestFn_alloc =
      .dec (ofString "p") .one (.var .global (ofString "heap_ptr"))
        (.seq
          (.ite (.cmp .lower (.op .sub [.const HeapPotential.cMax, .var .local (ofString "p")])
              (.var .local (ofString "n")))
            (.call (some (none, none)) (ofString "trap_with") [.const 1])
            .skip)
          (.dec (ofString "q") .one
            (.op .and [.op .add [.var .local (ofString "p"), .var .local (ofString "n"), .const 7],
              .op .sub [.const 0, .const 8]])
            (.seq
              (.ite (.cmp .lower (.const HeapPotential.cMax) (.var .local (ofString "q")))
                (.call (some (none, none)) (ofString "trap_with") [.const 1])
                .skip)
              (.seq
                (.assign .global (ofString "heap_ptr") (.var .local (ofString "q")))
                (.return (.var .local (ofString "p"))))))) := rfl
  have hgw0 : GlobalsWord s := hA.2.2.2.2.2.2.2.2
  rcases hA with ⟨hp_lo, hp_hi, hfm_lo, hfm_hi, hsp_hi, hp_al, hfm_al, hsp_al, _⟩
  have hp_word : ∃ p : BitVec 64, s.globals.lookup (ofString "heap_ptr") = some (.val (.word p)) := by
    rcases hg : s.globals.lookup (ofString "heap_ptr") with _ | gv
    · simp [globN, hg, sourceBase] at hp_lo
    · rcases gv with ⟨⟨p⟩⟩ | _ | _
      · exact ⟨p, rfl⟩
      · simp [globN, hg, sourceBase] at hp_lo
      · simp [globN, hg, sourceBase] at hp_lo
  obtain ⟨p, hp_lk⟩ := hp_word
  have hp_glob : globN s "heap_ptr" = p.toNat := by simp [globN, hp_lk]
  have hsame : ∀ t : PanSemStateFiniteExact 64 F, t.globals = s.globals →
      ArenaOK t ∧ globN s "heap_ptr" ≤ globN t "heap_ptr" := by
    intro t hg
    exact ⟨⟨by simpa only [globN, hg] using hp_lo,
      by simpa only [globN, hg] using hp_hi,
      by simpa only [globN, hg] using hfm_lo,
      by simpa only [globN, hg] using hfm_hi,
      by simpa only [globN, hg] using hsp_hi,
      by simpa only [globN, hg] using hp_al,
      by simpa only [globN, hg] using hfm_al,
      by simpa only [globN, hg] using hsp_al,
      globalsWord_congr hg hgw0⟩,
      by simp [globN, hg]⟩
  have htrap_globals : ∀ t : PanSemStateFiniteExact 64 F, t.code = originalRuntimeCode →
      (evaluateHOLFiniteState t (.call (some (none, none)) (ofString "trap_with") [.const 1])).2.globals = t.globals := by
    intro t htc
    apply HolFiniteMapExact.ext_lookup
    intro key
    refine InitECandidate.Solver.GuestGlobalKeep.evaluate_keepsG key (fun f => f == ofString "trap_with") ?_ _ rfl t htc
    intro f hf vs b callee rs hl
    have hfn : f = ofString "trap_with" := by simpa only [beq_iff_eq] using hf
    subst hfn
    have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ b _ rs vs callee lookup_trap_with hl
    subst hb; rfl
  rw [hbody, evaluateHOLFiniteState_dec_total]
  have hp_ev : @evalHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a))
      (.var .global (ofString "heap_ptr")) = some (.val (.word p)) := hp_lk
  dsimp only; rw [hp_ev]; dsimp only
  have hsh_p : shapeEqHOL .one (shapeOfHOLExact (.val (.word p))) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  rw [if_pos hsh_p]; dsimp only
  let pState := setVarHOLFinite (ofString "p") (.val (.word p)) s
  have hp_loc : pState.locals.lookup (ofString "p") = some (.val (.word p)) := by
    simp [pState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  rw [evaluateHOLFiniteState_seq_line780]
  rcases hn_lk : s.locals.lookup (ofString "n") with _ | nv
  · have hnl : pState.locals.lookup (ofString "n") = none := by
      simp [pState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn_lk,
        show ofString "p" ≠ ofString "n" by decide]
    have herr : evaluateHOLFiniteState pState
        (.ite (.cmp .lower (.op .sub [.const HeapPotential.cMax, .var .local (ofString "p")])
            (.var .local (ofString "n")))
          (.call (some (none, none)) (ofString "trap_with") [.const 1])
          .skip) = (some .error, pState) := by
      rw [evaluateHOLFiniteState_ite]; simp [evalHOLExact, evalListHOLExact, hnl]
    rw [herr]; exact hsame _ rfl
  · rcases nv with ⟨⟨n⟩⟩ | fs | ⟨nm, fs⟩
    · have hn_loc : pState.locals.lookup (ofString "n") = some (.val (.word n)) := by
        simp [pState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn_lk,
          show ofString "p" ≠ ofString "n" by decide]
      have hev1 : @evalHOLExact 64 F _ pState.toExact
          (fun a => Classical.propDecidable (pState.memaddrs a))
          (.cmp .lower (.op .sub [.const HeapPotential.cMax, .var .local (ofString "p")])
            (.var .local (ofString "n"))) =
          some (.val (.word (if (HeapPotential.cMax - p).toNat < n.toNat then 1 else 0))) := by
        simp only [evalHOLExact, evalListHOLExact, hp_loc, hn_loc,
          Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, decide_eq_true_eq]; rfl
      by_cases hcmp1 : (HeapPotential.cMax - p).toNat < n.toNat
      · have hite1 : evaluateHOLFiniteState pState
            (.ite (.cmp .lower (.op .sub [.const HeapPotential.cMax, .var .local (ofString "p")])
                (.var .local (ofString "n")))
              (.call (some (none, none)) (ofString "trap_with") [.const 1])
              .skip) =
            evaluateHOLFiniteState pState (.call (some (none, none)) (ofString "trap_with") [.const 1]) := by
          rw [evaluateHOLFiniteState_ite, hev1, if_pos hcmp1]; simp
        rw [hite1]
        have hno_none := evaluate_call_trap_with_no_none pState 1 hc
        have htg := htrap_globals pState hc
        rcases htr : evaluateHOLFiniteState pState (.call (some (none, none)) (ofString "trap_with") [.const 1]) with ⟨r1, s1⟩
        rw [htr] at hno_none htg
        cases r1 with
        | none => exact absurd rfl hno_none
        | some _ => exact hsame _ htg
      · have hite1 : evaluateHOLFiniteState pState
            (.ite (.cmp .lower (.op .sub [.const HeapPotential.cMax, .var .local (ofString "p")])
                (.var .local (ofString "n")))
              (.call (some (none, none)) (ofString "trap_with") [.const 1])
              .skip) = (none, pState) := by
          rw [evaluateHOLFiniteState_ite, hev1, if_neg hcmp1]; simp [evaluateHOLFiniteState_skip]
        rw [hite1]; dsimp only; rw [evaluateHOLFiniteState_dec_total]
        let q : BitVec 64 := (p + (n + 7)) &&& ((0 : BitVec 64) - 8)
        have hq_eval : @evalHOLExact 64 F _ pState.toExact
            (fun a => Classical.propDecidable (pState.memaddrs a))
            (.op .and [.op .add [.var .local (ofString "p"), .var .local (ofString "n"), .const 7],
              .op .sub [.const 0, .const 8]]) = some (.val (.word q)) := by
          simp only [evalHOLExact, evalListHOLExact, hp_loc, hn_loc,
            wordOpHOL, wordOp, valueIsWord, valueWord, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr]
          exact congrArg (fun w => some (ValueHOL.val (HolWordLab.word w))) (HeapPotential.alloc_q_word_eq p n)
        dsimp only; rw [hq_eval]; dsimp only
        have hsh_q : shapeEqHOL .one (shapeOfHOLExact (.val (.word q))) = true := by
          simp [shapeEqHOL, shapeOfHOLExact]
        rw [if_pos hsh_q]; dsimp only
        let qState := setVarHOLFinite (ofString "q") (.val (.word q)) pState
        have hq_loc : qState.locals.lookup (ofString "q") = some (.val (.word q)) := by
          simp [qState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have hp_loc_q : qState.locals.lookup (ofString "p") = some (.val (.word p)) := by
          simp [qState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hp_loc,
            show ofString "q" ≠ ofString "p" by decide]
        rw [evaluateHOLFiniteState_seq_line780]
        have hev2 : @evalHOLExact 64 F _ qState.toExact
            (fun a => Classical.propDecidable (qState.memaddrs a))
            (.cmp .lower (.const HeapPotential.cMax) (.var .local (ofString "q"))) =
            some (.val (.word (if HeapPotential.cMax.toNat < q.toNat then 1 else 0))) := by
          simp only [evalHOLExact, hq_loc, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, decide_eq_true_eq]
        by_cases hcmp2 : HeapPotential.cMax.toNat < q.toNat
        · have hite2 : evaluateHOLFiniteState qState
              (.ite (.cmp .lower (.const HeapPotential.cMax) (.var .local (ofString "q")))
                (.call (some (none, none)) (ofString "trap_with") [.const 1])
                .skip) =
              evaluateHOLFiniteState qState (.call (some (none, none)) (ofString "trap_with") [.const 1]) := by
            rw [evaluateHOLFiniteState_ite, hev2, if_pos hcmp2]; simp
          rw [hite2]
          have hno_none := evaluate_call_trap_with_no_none qState 1 hc
          have htg := htrap_globals qState hc
          rcases htr : evaluateHOLFiniteState qState (.call (some (none, none)) (ofString "trap_with") [.const 1]) with ⟨r2, s2⟩
          rw [htr] at hno_none htg
          cases r2 with
          | none => exact absurd rfl hno_none
          | some _ => exact hsame _ htg
        · have hite2 : evaluateHOLFiniteState qState
              (.ite (.cmp .lower (.const HeapPotential.cMax) (.var .local (ofString "q")))
                (.call (some (none, none)) (ofString "trap_with") [.const 1])
                .skip) = (none, qState) := by
            rw [evaluateHOLFiniteState_ite, hev2, if_neg hcmp2]; simp [evaluateHOLFiniteState_skip]
          rw [hite2]; dsimp only
          have hp_g : qState.globals.lookup (ofString "heap_ptr") = some (.val (.word p)) := hp_lk
          have heval_end : evaluateHOLFiniteState qState
              (.seq (.assign .global (ofString "heap_ptr") (.var .local (ofString "q")))
                (.return (.var .local (ofString "p")))) =
              (some (.returned (.val (.word p))),
                emptyLocalsHOLFinite (setGlobalHOLFinite (ofString "heap_ptr") (.val (.word q)) qState)) := by
            rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
            simp [evalHOLExact, hq_loc, hp_loc_q, isValidValueHOLExact, lookupKvarHOLExact, hp_g,
              shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite, setGlobalHOLFinite,
              evaluateHOLFiniteState_return, sizeOfShapeWithContextHOL]
          rw [heval_end]; dsimp only
          have hcMax_val : HeapPotential.cMax.toNat = 2952790016 := rfl
          have hhl_val : heapLimit = 2952790016 := rfl
          have hp_le_cMax : p.toNat ≤ HeapPotential.cMax.toNat := by omega
          have hsub_toNat : (HeapPotential.cMax - p).toNat = HeapPotential.cMax.toNat - p.toNat := by
            rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr hp_le_cMax)]
          have h7 : (7 : BitVec 64).toNat = 7 := rfl
          have hn7 : (n + 7).toNat = n.toNat + 7 := by rw [BitVec.toNat_add, h7]; omega
          have hsum : (p + (n + 7)).toNat = p.toNat + n.toNat + 7 := by rw [BitVec.toNat_add, hn7]; omega
          have hq_toNat : q.toNat = (p.toNat + n.toNat + 7) / 8 * 8 := by
            have hq1 := and_neg8_toNat (p + (n + 7))
            change q.toNat = _ at hq1
            rw [hq1, hsum]
          set fin := emptyLocalsHOLFinite (setGlobalHOLFinite (ofString "heap_ptr") (.val (.word q)) qState)
          have hfin_hp : globN fin "heap_ptr" = q.toNat := by
            simp [fin, globN, emptyLocalsHOLFinite, setGlobalHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          have hfin_fm : globN fin "frame_mem_ptr" = globN s "frame_mem_ptr" := by
            simp [fin, qState, pState, globN, emptyLocalsHOLFinite, setGlobalHOLFinite, setVarHOLFinite,
              HolFiniteMapExact.lookup_update, FUPDATE, show ofString "heap_ptr" ≠ ofString "frame_mem_ptr" by decide]
          have hfin_sp : globN fin "scratch_ptr" = globN s "scratch_ptr" := by
            simp [fin, qState, pState, globN, emptyLocalsHOLFinite, setGlobalHOLFinite, setVarHOLFinite,
              HolFiniteMapExact.lookup_update, FUPDATE, show ofString "heap_ptr" ≠ ofString "scratch_ptr" by decide]
          change ArenaOK { fin with locals := _ } ∧ globN s "heap_ptr" ≤ globN { fin with locals := _ } "heap_ptr"
          have hfin_gw : GlobalsWord fin := by
            intro gn hgn
            by_cases hgn_hp : ofString gn = ofString "heap_ptr"
            · exact ⟨q, by simp [fin, GlobalWord, emptyLocalsHOLFinite, setGlobalHOLFinite,
                HolFiniteMapExact.lookup_update, FUPDATE, hgn_hp]⟩
            · obtain ⟨wg, hwg⟩ := hgw0 gn hgn
              have hne : ofString "heap_ptr" ≠ ofString gn := Ne.symm hgn_hp
              exact ⟨wg, by simpa [fin, qState, pState, GlobalWord, emptyLocalsHOLFinite,
                setGlobalHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                hne] using hwg⟩
          have hfin_ok : ArenaOK fin := by
            unfold ArenaOK
            rw [hfin_hp, hfin_fm, hfin_sp]
            exact ⟨by omega, by omega, hfm_lo, hfm_hi, hsp_hi, by omega, hfm_al, hsp_al, hfin_gw⟩
          have hfin_le : globN s "heap_ptr" ≤ globN fin "heap_ptr" := by
            rw [hp_glob, hfin_hp]; omega
          exact ⟨hfin_ok, hfin_le⟩
    · have hnl : pState.locals.lookup (ofString "n") = some (.rStruct fs) := by
        simp [pState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn_lk,
          show ofString "p" ≠ ofString "n" by decide]
      have herr : evaluateHOLFiniteState pState
          (.ite (.cmp .lower (.op .sub [.const HeapPotential.cMax, .var .local (ofString "p")])
              (.var .local (ofString "n")))
            (.call (some (none, none)) (ofString "trap_with") [.const 1])
            .skip) = (some .error, pState) := by
        rw [evaluateHOLFiniteState_ite]; simp [evalHOLExact, evalListHOLExact, hnl, valueIsWord]
      rw [herr]; exact hsame _ rfl
    · have hnl : pState.locals.lookup (ofString "n") = some (.nStruct nm fs) := by
        simp [pState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn_lk,
          show ofString "p" ≠ ofString "n" by decide]
      have herr : evaluateHOLFiniteState pState
          (.ite (.cmp .lower (.op .sub [.const HeapPotential.cMax, .var .local (ofString "p")])
              (.var .local (ofString "n")))
            (.call (some (none, none)) (ofString "trap_with") [.const 1])
            .skip) = (some .error, pState) := by
        rw [evaluateHOLFiniteState_ite]; simp [evalHOLExact, evalListHOLExact, hnl, valueIsWord]
      rw [herr]; exact hsame _ rfl

private theorem encoding_body_heapSafe (f : MlS) (hf : encodingGood f = true)
    (values : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (rs : ShapeHOL)
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup f values = some (body, callee, rs)) :
    (f = ofString "alloc" ∧ body = sourceFnBody Guest.Software.guestFn_alloc) ∨
      heapSafeProg body = true := by
  simp only [encodingGood, List.map_cons, List.map_nil, List.contains_cons, List.contains_nil,
    Bool.or_eq_true, beq_iff_eq, Bool.false_eq_true, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · right; have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 281 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn__node_rlp_begin) rfl) hl; subst hb; rfl
  · right; have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 282 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn__node_rlp_finish) rfl) hl; subst hb; rfl
  · left; exact ⟨rfl, lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee lookup_alloc hl⟩
  · right; have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 103 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_keccak256) rfl) hl; subst hb; rfl
  · right; have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 102 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_keccak_absorb_block) rfl) hl; subst hb; rfl
  · right; have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 101 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_keccak_f1600) rfl) hl; subst hb; rfl
  · right; have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 16 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_memcpy) rfl) hl; subst hb; rfl
  · right; have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee lookup_memzero hl; subst hb; rfl
  · right; have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 246 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_mpt_fail) rfl) hl; subst hb; rfl
  · right; have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 250 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_nibble_list_to_compact) rfl) hl; subst hb; rfl
  · right; have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 288 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_node_hash_cached) rfl) hl; subst hb; rfl
  · right; have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 287 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_node_ref_len) rfl) hl; subst hb; rfl
  · right; have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 289 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_node_write_ref) rfl) hl; subst hb; rfl
  · right; have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 118 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_rlp_be_len) rfl) hl; subst hb; rfl
  · right; have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 125 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_rlp_bytes_encoded_len) rfl) hl; subst hb; rfl
  · right; have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 122 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_rlp_encode_bytes) rfl) hl; subst hb; rfl
  · right; have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 124 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_rlp_encode_list_header) rfl) hl; subst hb; rfl
  · right; have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 121 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_rlp_header_len) rfl) hl; subst hb; rfl
  · right; have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 126 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_rlp_list_header_len) rfl) hl; subst hb; rfl
  · right; have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 119 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_rlp_put_be) rfl) hl; subst hb; rfl
  · right; have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 286 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_rlp_value_encoded_len) rfl) hl; subst hb; rfl
  · right; have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee (lookup_of_guestAst_getElem 120 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_rlp_write_header) rfl) hl; subst hb; rfl
  · right; have hb := lookupCodeHOLFinite_installed_body originalRuntimeCode.lookup _ _ _ body _ rs values callee lookup_trap_with hl; subst hb; rfl

private theorem arenaOK_congr_globals {F : Type} {s t : PanSemStateFiniteExact 64 F}
    (hg : t.globals = s.globals) (h : ArenaOK s) : ArenaOK t := by
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, hgw⟩
  exact ⟨by simpa only [globN, hg] using h1,
    by simpa only [globN, hg] using h2,
    by simpa only [globN, hg] using h3,
    by simpa only [globN, hg] using h4,
    by simpa only [globN, hg] using h5,
    by simpa only [globN, hg] using h6,
    by simpa only [globN, hg] using h7,
    by simpa only [globN, hg] using h8,
    globalsWord_congr hg hgw⟩

theorem evaluate_heapSafeProg {F : Type} (program : ProgHOL 64)
    (supported : heapSafeProg program = true)
    (state : PanSemStateFiniteExact 64 F) (code : state.code = originalRuntimeCode)
    (hA : ArenaOK state) :
    ArenaOK (evaluateHOLFiniteState state program).2 ∧
      globN state "heap_ptr" ≤ globN (evaluateHOLFiniteState state program).2 "heap_ptr" := by
  cases shape : program with
  | skip => rw [evaluateHOLFiniteState_skip]; exact ⟨hA, Nat.le_refl _⟩
  | dec name kind initializer body =>
    have child : heapSafeProg body = true := by simpa only [shape, heapSafeProg] using supported
    rw [evaluateHOLFiniteState_dec_total]; dsimp only
    split
    · exact ⟨hA, Nat.le_refl _⟩
    · rename_i val _
      split
      · obtain ⟨hAb, hle⟩ := evaluate_heapSafeProg body child (setVarHOLFinite name val state) code hA
        exact ⟨arenaOK_congr_globals rfl hAb, hle⟩
      · exact ⟨hA, Nat.le_refl _⟩
  | decCall name kind function arguments continuation =>
    have children : encodingGood function = true ∧ heapSafeProg continuation = true := by
      simpa only [shape, heapSafeProg, Bool.and_eq_true] using supported
    rw [evaluateHOLFiniteState_decCall_total]
    split
    · exact ⟨hA, Nat.le_refl _⟩
    · rename_i values _
      split
      · exact ⟨hA, Nat.le_refl _⟩
      · rename_i body callee rs found
        rw [code] at found
        split
        · exact ⟨hA, Nat.le_refl _⟩
        · rename_i nonzero
          dsimp only
          have hbodyA : ArenaOK (evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body).2 ∧
              globN state "heap_ptr" ≤ globN (evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body).2 "heap_ptr" := by
            rcases encoding_body_heapSafe function children.1 values body callee rs found with ⟨_, rfl⟩ | hsafe
            · exact alloc_body_heap_mono (callEntryStateHOLFinite state callee) code hA
            · exact evaluate_heapSafeProg body hsafe (callEntryStateHOLFinite state callee) code hA
          have meta' := InitECandidate.Solver.GuestGlobalKeep.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state callee) body
          have cl := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite state callee) body
          generalize evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = out at hbodyA meta' cl
          obtain ⟨r, st⟩ := out
          dsimp only at hbodyA meta' cl ⊢
          change st.clock ≤ state.clock - 1 at cl
          have stCode : st.code = originalRuntimeCode := meta'.1.trans code
          rcases r with _ | (_ | _ | _ | _ | v | _ | _)
          all_goals (dsimp only [fixClockHOLFinite])
          all_goals (try exact hbodyA)
          split
          · have small : (if state.clock - 1 < st.clock then state.clock - 1 else st.clock) < state.clock := by
              split <;> omega
            let resumed : PanSemStateFiniteExact 64 F :=
              setVarHOLFinite name v
                { st with locals := state.locals,
                          clock := if (callEntryStateHOLFinite state callee).clock < st.clock
                                   then (callEntryStateHOLFinite state callee).clock else st.clock }
            obtain ⟨hAc, hlec⟩ := evaluate_heapSafeProg continuation children.2 resumed
              stCode (arenaOK_congr_globals rfl hbodyA.1)
            exact ⟨arenaOK_congr_globals rfl hAc, Nat.le_trans hbodyA.2 hlec⟩
          · exact hbodyA
  | assign kind name value =>
    cases kind with
    | global => simp [shape, heapSafeProg] at supported
    | «local» =>
      rw [evaluateHOLFiniteState_assign]
      split
      · exact ⟨hA, Nat.le_refl _⟩
      · split <;> exact ⟨arenaOK_congr_globals rfl hA, Nat.le_refl _⟩
  | seq first second =>
    have children : heapSafeProg first = true ∧ heapSafeProg second = true := by
      simpa only [shape, heapSafeProg, Bool.and_eq_true] using supported
    have hA1 := evaluate_heapSafeProg first children.1 state code hA
    have remaining := evaluateHOLFiniteState_clock_le state first
    have meta' := InitECandidate.Solver.GuestGlobalKeep.evaluateHOLFiniteState_metadata state first
    rw [evaluateHOLFiniteState_seq_line780]
    cases firstRun : evaluateHOLFiniteState state first with
    | mk result middle =>
      rw [firstRun] at hA1 remaining meta'
      dsimp only at hA1 remaining meta'
      cases result with
      | none =>
        have mclock : middle.clock ≤ state.clock := remaining
        obtain ⟨hA2, hle2⟩ := evaluate_heapSafeProg second children.2 middle (meta'.1.trans code) hA1.1
        exact ⟨hA2, Nat.le_trans hA1.2 hle2⟩
      | some _ => exact hA1
  | ite condition yes no =>
    have children : heapSafeProg yes = true ∧ heapSafeProg no = true := by
      simpa only [shape, heapSafeProg, Bool.and_eq_true] using supported
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_heapSafeProg no children.2 state code hA
      · exact evaluate_heapSafeProg yes children.1 state code hA
    · exact ⟨hA, Nat.le_refl _⟩
  | «while» condition body =>
    have child : heapSafeProg body = true := by simpa only [shape, heapSafeProg] using supported
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · exact ⟨hA, Nat.le_refl _⟩
        · rename_i nonzero
          dsimp only
          rw [fixClockHOLFinite_evaluateState]
          have hAb := evaluate_heapSafeProg body child (decClockHOLFinite state) code hA
          have remaining := evaluateHOLFiniteState_clock_le (decClockHOLFinite state) body
          have meta' := InitECandidate.Solver.GuestGlobalKeep.evaluateHOLFiniteState_metadata (decClockHOLFinite state) body
          cases bodyRun : evaluateHOLFiniteState (decClockHOLFinite state) body with
          | mk result middle =>
            rw [bodyRun] at hAb remaining meta'
            dsimp only at hAb remaining meta'
            have smaller : middle.clock < state.clock := by
              change middle.clock ≤ state.clock - 1 at remaining; omega
            have mCode : middle.code = originalRuntimeCode := meta'.1.trans code
            cases result with
            | none =>
              obtain ⟨hAw, hlew⟩ := evaluate_heapSafeProg (.while condition body) (by simpa [heapSafeProg] using child) middle mCode hAb.1
              exact ⟨hAw, Nat.le_trans hAb.2 hlew⟩
            | some r =>
              cases r with
              | «continue» =>
                obtain ⟨hAw, hlew⟩ := evaluate_heapSafeProg (.while condition body) (by simpa [heapSafeProg] using child) middle mCode hAb.1
                exact ⟨hAw, Nat.le_trans hAb.2 hlew⟩
              | _ => exact hAb
      · exact ⟨hA, Nat.le_refl _⟩
    · exact ⟨hA, Nat.le_refl _⟩
  | «break» => rw [evaluateHOLFiniteState_break]; exact ⟨hA, Nat.le_refl _⟩
  | «continue» => rw [evaluateHOLFiniteState_continue]; exact ⟨hA, Nat.le_refl _⟩
  | annot tag text => rw [evaluateHOLFiniteState_annot]; exact ⟨hA, Nat.le_refl _⟩
  | raise name value =>
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only; split <;> exact ⟨hA, Nat.le_refl _⟩
    · exact ⟨hA, Nat.le_refl _⟩
  | «return» value =>
    rw [evaluateHOLFiniteState_return]
    split
    · exact ⟨hA, Nat.le_refl _⟩
    · split <;> exact ⟨hA, Nat.le_refl _⟩
  | store destination value =>
    rw [evaluateHOLFiniteState_store]
    split <;> try exact ⟨hA, Nat.le_refl _⟩
    split <;> try exact ⟨hA, Nat.le_refl _⟩
    split <;> exact ⟨hA, Nat.le_refl _⟩
  | storeByte destination value =>
    rw [evaluateHOLFiniteState_storeByte]
    split <;> try exact ⟨hA, Nat.le_refl _⟩
    split <;> try exact ⟨hA, Nat.le_refl _⟩
    split <;> exact ⟨hA, Nat.le_refl _⟩
  | shMemStore op a v =>
    have hg : (evaluateHOLFiniteState state (.shMemStore op a v)).2.globals = state.globals := by
      apply HolFiniteMapExact.ext_lookup
      intro k; exact InitECandidate.Solver.GuestGlobalKeep.shMemStore_globals state op a v k
    exact ⟨arenaOK_congr_globals hg hA, by unfold globN; rw [hg]⟩
  | extCall name a b c d =>
    rw [evaluateHOLFiniteState_extCall_source]
    split <;> try exact ⟨hA, Nat.le_refl _⟩
    split <;> try exact ⟨hA, Nat.le_refl _⟩
    split <;> exact ⟨arenaOK_congr_globals (by simp [emptyLocalsHOLFinite, ofExact, toExact]) hA,
      by simp [globN, emptyLocalsHOLFinite, ofExact, toExact]⟩
  | primitive name op args =>
    rw [evaluateHOLFiniteState_primitive]
    split <;> try exact ⟨hA, Nat.le_refl _⟩
    split <;> try exact ⟨hA, Nat.le_refl _⟩
    split <;> exact ⟨hA, Nat.le_refl _⟩
  | call info function arguments =>
    have hk : encodingGood function = true ∧
        (info = none ∨ info = some (none, none) ∨ ∃ nm, info = some (some (.local, nm), none)) := by
      rcases info with _ | ⟨_ | ⟨kind, nm⟩, _ | _⟩
      · exact ⟨by simpa [shape, heapSafeProg] using supported, Or.inl rfl⟩
      · exact ⟨by simpa [shape, heapSafeProg] using supported, Or.inr (Or.inl rfl)⟩
      · simp [shape, heapSafeProg] at supported
      · cases kind
        · exact ⟨by simpa [shape, heapSafeProg] using supported, Or.inr (Or.inr ⟨nm, rfl⟩)⟩
        · simp [shape, heapSafeProg] at supported
      · simp [shape, heapSafeProg] at supported
    rw [evaluateHOLFiniteState_call]
    split
    · exact ⟨hA, Nat.le_refl _⟩
    · rename_i values _
      split
      · exact ⟨hA, Nat.le_refl _⟩
      · rename_i body callee rs found
        rw [code] at found
        split
        · exact ⟨hA, Nat.le_refl _⟩
        · rename_i nonzero
          have hbodyA : let out := (evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body).2
              ArenaOK out ∧ globN state "heap_ptr" ≤ globN out "heap_ptr" := by
            rcases encoding_body_heapSafe function hk.1 values body callee rs found with ⟨_, rfl⟩ | hsafe
            · exact alloc_body_heap_mono (callEntryStateHOLFinite state callee) code hA
            · exact evaluate_heapSafeProg body hsafe (callEntryStateHOLFinite state callee) code hA
          generalize evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = out at hbodyA
          obtain ⟨r, st⟩ := out
          dsimp only at hbodyA ⊢
          rcases hk.2 with rfl | rfl | ⟨nm, rfl⟩
          · rcases r with _ | (_ | _ | _ | _ | v | _ | _) <;> dsimp only <;> (repeat' split) <;>
              exact ⟨arenaOK_congr_globals (by simp [emptyLocalsHOLFinite]) hbodyA.1,
                by simpa [globN, emptyLocalsHOLFinite] using hbodyA.2⟩
          · rcases r with _ | (_ | _ | _ | _ | v | _ | _) <;> dsimp only <;> (repeat' split) <;>
              exact ⟨arenaOK_congr_globals (by simp [emptyLocalsHOLFinite]) hbodyA.1,
                by simpa [globN, emptyLocalsHOLFinite] using hbodyA.2⟩
          · rcases r with _ | (_ | _ | _ | _ | v | _ | _) <;> dsimp only <;> (repeat' split) <;>
              exact ⟨arenaOK_congr_globals (by simp [setKvarHOLFinite, setVarHOLFinite, emptyLocalsHOLFinite]) hbodyA.1,
                by simpa [globN, setKvarHOLFinite, setVarHOLFinite, emptyLocalsHOLFinite] using hbodyA.2⟩
  | _ => simp [shape, heapSafeProg] at supported
termination_by (state.clock, sizeOf program)
decreasing_by
  all_goals
    simp_wf
    apply InitECandidate.Solver.GuestGlobalKeep.lex_of
    try subst shape
    try simp only [setVarHOLFinite, decClockHOLFinite, callEntryStateHOLFinite, ProgHOL.seq.sizeOf_spec,
      ProgHOL.ite.sizeOf_spec, ProgHOL.dec.sizeOf_spec, ProgHOL.while.sizeOf_spec, ProgHOL.decCall.sizeOf_spec, true_and]
    first
      | exact Or.inl small
      | omega

end R13NodeRlp

theorem ak__node_rlp_begin : KeepsOn ArenaReady ArenaReady (ofString "_node_rlp_begin") := by
  refine ⟨_, _, _, lookup_of_guestAst_getElem 281 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn__node_rlp_begin) rfl, ?_⟩
  intro F s hc hAR _ _ _
  exact ⟨guestInv_evaluate s _ hAR.1, (R13NodeRlp.evaluate_heapSafeProg _ rfl s hc hAR.2).1⟩

theorem ak__node_rlp_finish : KeepsOn ArenaReady ArenaReady (ofString "_node_rlp_finish") := by
  refine ⟨_, _, _, lookup_of_guestAst_getElem 282 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn__node_rlp_finish) rfl, ?_⟩
  intro F s hc hAR _ _ _
  exact ⟨guestInv_evaluate s _ hAR.1, (R13NodeRlp.evaluate_heapSafeProg _ rfl s hc hAR.2).1⟩

end InitECandidate.Solver.Wave8GuestInv.R13NodeRlpKeep
