import InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc.Batch1
import InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_GbodyC17ToC21
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M13.wk_u256_to_be_min
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M27.rv_u256_to_be_min

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.style.nameCheck false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.HeaderHashRecover

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R16Shards.WkBlockTxEnc
open InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_GbodyC17ToC21 (IvlUnhit)

def headerSlices {F : Type} (s : PanSemStateFiniteExact 64 F) (h : Nat) : List Ivl :=
  [(memW s (h + 8), 32), (memW s (h + 16), 32), (memW s (h + 24), 20),
   (memW s (h + 32), 32), (memW s (h + 40), 32), (memW s (h + 48), 32),
   (memW s (h + 56), 256), (memW s (h + 128), memW s (h + 136)),
   (memW s (h + 144), 32), (memW s (h + 152), 8), (memW s (h + 192), 32),
   (memW s (h + 216), 32), (memW s (h + 224), 32)] ++
  (if memW s h ≠ 0 then [(memW s (h + 232), 32)] else [])

def HeaderAtStrong {F : Type} (s : PanSemStateFiniteExact 64 F) (h : Nat) : Prop :=
  HeaderAt s h ∧ Inside (h, 248) sourceBase (globN s "heap_ptr")

def HeaderOKStrong : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => HeaderAtStrong s (locN s "h")

theorem headerAtStrong_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) (h : Nat) :
    HeaderAtStrong { s with locals := locals, clock := k } h ↔ HeaderAtStrong s h := by
  have hmemW : ∀ a, memW { s with locals := locals, clock := k } a = memW s a := fun _ => rfl
  have hglob : ∀ g, globN { s with locals := locals, clock := k } g = globN s g := fun _ => rfl
  have hwords : ∀ i, WordsOK { s with locals := locals, clock := k } i ↔ WordsOK s i := fun _ => Iff.rfl
  simp only [HeaderAtStrong, HeaderAt, hwords, hmemW, hglob]

theorem localsOnly_headerOKStrong : LocalsOnly ["h"] HeaderOKStrong := by
  intro F s locals k hl hP
  have hh := locN_congr s locals k "h" (hl "h" (by simp))
  simp only [HeaderOKStrong, headerAtStrong_with_locals] at hP ⊢
  rw [hh]
  exact hP

theorem headerAt_of_ivlUnhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hgS : GuestInv s) (hgP : GuestInv post) {h : Nat}
    (hh_bound : h + 248 ≤ 2 ^ 64)
    (hu : IvlUnhit s post (h, 248))
    (hH : HeaderAt s h) :
    HeaderAt post h := by
  obtain ⟨hw, h136⟩ := hH
  refine ⟨R10Shards.Fast_GbodyC17ToC21.wordsOK_transfer hgS hgP hw, ?_⟩
  have hm := R10Shards.Fast_GbodyC17ToC21.memW_eq_of_ivlUnhit (a := h + 136) hu
    (by have := hw.1; omega) hh_bound ⟨by omega, by omega⟩
  omega

theorem headerAtStrong_of_ivlUnhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hgS : GuestInv s) (hgP : GuestInv post)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    {h : Nat} (hh_bound : h + 248 ≤ 2 ^ 64)
    (hu : IvlUnhit s post (h, 248))
    (hH : HeaderAtStrong s h) :
    HeaderAtStrong post h :=
  ⟨headerAt_of_ivlUnhit hgS hgP hh_bound hu hH.1, ⟨hH.2.1, Nat.le_trans hH.2.2 hhp⟩⟩

theorem headerSlices_eq_of_ivlUnhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {h : Nat} (hh8 : h % 8 = 0) (hh_bound : h + 248 ≤ 2 ^ 64)
    (hu : IvlUnhit s post (h, 248)) :
    headerSlices post h = headerSlices s h := by
  have hm : ∀ off, off % 8 = 0 → off + 8 ≤ 248 → memW post (h + off) = memW s (h + off) := by
    intro off hoff8 hoff_hi
    exact R10Shards.Fast_GbodyC17ToC21.memW_eq_of_ivlUnhit hu
      (by omega) hh_bound ⟨by omega, by omega⟩
  have h0 : memW post h = memW s h := by simpa using hm 0 (by omega) (by omega)
  unfold headerSlices
  rw [h0,
    hm 8 (by omega) (by omega), hm 16 (by omega) (by omega), hm 24 (by omega) (by omega),
    hm 32 (by omega) (by omega), hm 40 (by omega) (by omega), hm 48 (by omega) (by omega),
    hm 56 (by omega) (by omega), hm 128 (by omega) (by omega), hm 136 (by omega) (by omega),
    hm 144 (by omega) (by omega), hm 152 (by omega) (by omega), hm 192 (by omega) (by omega),
    hm 216 (by omega) (by omega), hm 224 (by omega) (by omega), hm 232 (by omega) (by omega)]

theorem headerAtStrong_of_allocatorGrows {F : Type} {s post : PanSemStateFiniteExact 64 F}
    (hAs : ArenaReady s) (hAp : ArenaReady post) (hag : AllocatorGrows s post)
    {keep : List Ivl} {fresh : Ivl}
    (hfr : FrameOutside s post keep fresh)
    (hk_sub : ∀ k ∈ keep, k = (globN post "scratch_ptr", globN s "scratch_ptr" - globN post "scratch_ptr"))
    (hf_eq : fresh = (globN s "heap_ptr", globN post "heap_ptr" - globN s "heap_ptr"))
    {h : Nat} (hH : HeaderAtStrong s h) :
    HeaderAtStrong post h ∧ IvlUnhit s post (h, 248) := by
  have hal : Allocated s (h, 248) := Or.inl hH.2
  have hbound := (R10Shards.Fast_GbodyC17ToC21.ivl_allocated_bound hAs.2 hal).2
  have hu := R10Shards.Fast_GbodyC17ToC21.ivl_unhit_free_of_zero_or_allocated
    hAs.2 hAp.2 hag hfr hk_sub hf_eq (Or.inr ⟨by omega, hal⟩)
  exact ⟨headerAtStrong_of_ivlUnhit hAs.1 hAp.1 hag.1 hbound hu hH, hu⟩

theorem headerAtStrong_of_worldStep {F : Type}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {s post : PanSemStateFiniteExact 64 F} {r : Option (PanSemResultExact 64)}
    {S Nd : List Nat} {h : Nat}
    (hAs : ArenaReady s)
    (hWS : WorldStep R gw keep Q s r post)
    (hWT : WorldTypedWith s S Nd)
    (hD : IvlsDisj (R s) (worldTypedIvls s S Nd))
    (hR_z : ∀ j ∈ R s, j.2 = 0 → j.1 % 8 = 0)
    (hH : HeaderAtStrong s h)
    (hdisj_wo : IvlsDisj [(h, 248)] (worldOwned s S Nd))
    (hdisj_R : IvlsDisj [(h, 248)] (R s)) :
    ∃ S' Nd', (∀ t ∈ S, t ∈ S') ∧ WorldTypedWith post S' Nd' ∧
      HeaderAtStrong post h ∧
      IvlsDisj [(h, 248)] (worldOwned post S' Nd') ∧
      IvlUnhit s post (h, 248) ∧
      Q s r post S' Nd' := by
  obtain ⟨hAp, hhp, _, _, hStep⟩ := hWS
  obtain ⟨S', Nd', hsub, hWT', hog, hfr, hQ⟩ := hStep S Nd hWT hD
  have hbound := (R10Shards.Fast_GbodyC17ToC21.ivl_allocated_bound hAs.2 (Or.inl hH.2)).2
  obtain ⟨hin_post, hdisj_post, hu⟩ :=
    R10Shards.Fast_GbodyC17ToC21.heap_ivl_survives_step hAs.2 hhp hog hfr
      (R10Shards.Fast_GbodyC17ToC21.worldOwned_zero_aligned hWT) hR_z
      hH.1.1.1 (by omega) hH.2
      (fun j hj => hdisj_wo (h, 248) List.mem_cons_self j hj)
      (fun j hj => hdisj_R (h, 248) List.mem_cons_self j hj)
  refine ⟨S', Nd', hsub, hWT',
    ⟨headerAt_of_ivlUnhit hAs.1 hAp.1 hbound hu hH.1, hin_post⟩,
    fun x hx o ho => ?_, hu, hQ⟩
  simp only [List.mem_singleton] at hx
  subst hx
  exact hdisj_post o ho

theorem lookup_rlp_put_u256 :
    originalRuntimeCode.lookup (ofString "rlp_put_u256") =
      some ([(ofString "dst", .one), (ofString "v", .comb [.one, .one, .one, .one])],
        sourceFnBody Guest.Software.guestFn_rlp_put_u256, .one) :=
  lookup_of_guestAst_getElem 228 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_rlp_put_u256) rfl

theorem lookup_encode_header :
    originalRuntimeCode.lookup (ofString "encode_header") =
      some ([(ofString "h", .one)],
        sourceFnBody Guest.Software.guestFn_encode_header, .comb [.one, .one]) :=
  lookup_of_guestAst_getElem 229 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_encode_header) rfl

theorem lookup_header_hash :
    originalRuntimeCode.lookup (ofString "header_hash") =
      some ([(ofString "h", .one), (ofString "out", .one)],
        sourceFnBody Guest.Software.guestFn_header_hash, .one) :=
  lookup_of_guestAst_getElem 230 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_header_hash) rfl

private theorem heapByteEff_of_dec_word {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {x : MlS} {e : ExpHOL 64} {w : BitVec 64}
    {body : ProgHOL 64} {Rl : List Ivl} {gw : List String}
    (hev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e =
      some (.val (.word w)))
    (hb : HeapByteEff s0 (evaluateHOLFiniteState (setVarHOLFinite x (.val (.word w)) s) body).2 Rl gw) :
    HeapByteEff s0 (evaluateHOLFiniteState s (.dec x .one e body)).2 Rl gw := by
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only; rw [hev]; dsimp only
  have hsh : shapeEqHOL .one (shapeOfHOLExact (.val (.word w) : ValueHOL 64)) = true := by
    simp [shapeOfHOLExact, shapeEqHOL]
  rw [if_pos hsh]
  exact hb.locals_clock _ (evaluateHOLFiniteState (setVarHOLFinite x (.val (.word w)) s) body).2.clock

private theorem heapByteEff_of_seq_none {F : Type}
    {s0 s m : PanSemStateFiniteExact 64 F} {a b : ProgHOL 64} {Rl : List Ivl} {gw : List String}
    (ha : evaluateHOLFiniteState s a = (none, m))
    (hb : HeapByteEff s0 (evaluateHOLFiniteState m b).2 Rl gw) :
    HeapByteEff s0 (evaluateHOLFiniteState s (.seq a b)).2 Rl gw := by
  rw [evaluateHOLFiniteState_seq_line780, ha]
  exact hb

private theorem heapByteEff_of_seq_some {F : Type}
    {s0 s m : PanSemStateFiniteExact 64 F} {a b : ProgHOL 64} {r : PanSemResultExact 64}
    {Rl : List Ivl} {gw : List String}
    (ha : evaluateHOLFiniteState s a = (some r, m))
    (hm : HeapByteEff s0 m Rl gw) :
    HeapByteEff s0 (evaluateHOLFiniteState s (.seq a b)).2 Rl gw := by
  rw [evaluateHOLFiniteState_seq_line780, ha]
  exact hm

private theorem heapByteEff_of_eq_resVar {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {p : ProgHOL 64}
    {r' : Option (PanSemResultExact 64)} {q : PanSemStateFiniteExact 64 F}
    {L : HolFiniteMapExact MlS (ValueHOL 64)} {Rl : List Ivl} {gw : List String}
    (heq : evaluateHOLFiniteState s p = (r', { q with locals := L }))
    (hq : HeapByteEff s0 q Rl gw) :
    HeapByteEff s0 (evaluateHOLFiniteState s p).2 Rl gw := by
  rw [heq]
  exact hq.locals_clock L q.clock

private theorem pan_word_u256_lookup
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (name first second : MlS) (body : ProgHOL 64)
    (left : BitVec 64) (w0 w1 w2 w3 : BitVec 64)
    (different : first ≠ second)
    (lookup : code name =
      some ([(first, .one), (second, .comb [.one, .one, .one, .one])], body, .one)) :
    let vval : ValueHOL 64 := .rStruct [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3)]
    PanSemStateFiniteExact.lookupCodeHOLFinite code name [.val (.word left), vval] =
      some (body, (HolFiniteMapExact.empty.update (first, .val (.word left))).update (second, vval), .one) := by
  intro vval
  have raw : lookupCodeHOLExact code name [.val (.word left), vval] =
      some (body, (fun key => if key = second then some vval else if key = first then some (.val (.word left)) else none), .one) := by
    simp [lookupCodeHOLExact, lookup, shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL, different, vval]
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite
  split
  · rename_i missing; rw [raw] at missing; cases missing
  · rename_i foundBody foundLocals foundShape found
    have equal := Option.some.inj (found.symm.trans raw)
    obtain ⟨rfl, rest⟩ := Prod.mk.inj equal
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj rest
    apply congrArg (fun locals => some (foundBody, locals, ShapeHOL.one))
    apply HolFiniteMapExact.ext
    funext key
    by_cases two : key = second
    · subst key; simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY]
    · have backTwo : second ≠ key := Ne.symm two
      by_cases one : key = first
      · subst key; simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY, different, Ne.symm different]
      · have backOne : first ≠ key := Ne.symm one
        simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY, one, two, backOne, backTwo]

private theorem pan_u256_word_lookup
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (name first second : MlS) (body : ProgHOL 64)
    (w0 w1 w2 w3 : BitVec 64) (right : BitVec 64)
    (different : first ≠ second)
    (lookup : code name =
      some ([(first, .comb [.one, .one, .one, .one]), (second, .one)], body, .one)) :
    let vval : ValueHOL 64 := .rStruct [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3)]
    PanSemStateFiniteExact.lookupCodeHOLFinite code name [vval, .val (.word right)] =
      some (body, (HolFiniteMapExact.empty.update (first, vval)).update (second, .val (.word right)), .one) := by
  intro vval
  have raw : lookupCodeHOLExact code name [vval, .val (.word right)] =
      some (body, (fun key => if key = second then some (.val (.word right)) else if key = first then some vval else none), .one) := by
    simp [lookupCodeHOLExact, lookup, shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL, different, vval]
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite
  split
  · rename_i missing; rw [raw] at missing; cases missing
  · rename_i foundBody foundLocals foundShape found
    have equal := Option.some.inj (found.symm.trans raw)
    obtain ⟨rfl, rest⟩ := Prod.mk.inj equal
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj rest
    apply congrArg (fun locals => some (foundBody, locals, ShapeHOL.one))
    apply HolFiniteMapExact.ext
    funext key
    by_cases two : key = second
    · subst key; simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY]
    · have backTwo : second ≠ key := Ne.symm two
      by_cases one : key = first
      · subst key; simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY, different, Ne.symm different]
      · have backOne : first ≠ key := Ne.symm one
        simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY, one, two, backOne, backTwo]

private theorem pan_one_word_lookup_any
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (name parameter : MlS) (body : ProgHOL 64) (rs : ShapeHOL) (amount : BitVec 64)
    (lookup : code name = some ([(parameter, .one)], body, rs)) :
    PanSemStateFiniteExact.lookupCodeHOLFinite code name [.val (.word amount)] =
      some (body, HolFiniteMapExact.empty.update (parameter, .val (.word amount)), rs) := by
  have raw : lookupCodeHOLExact code name [.val (.word amount)] =
      some (body, (fun key => if key = parameter then some (.val (.word amount)) else none), rs) := by
    simp [lookupCodeHOLExact, lookup, shapeOfHOLExact, shapeEqHOL]
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite
  split
  · rename_i missing; rw [raw] at missing; cases missing
  · rename_i foundBody foundLocals foundShape found
    have equal := Option.some.inj (found.symm.trans raw)
    obtain ⟨rfl, rest⟩ := Prod.mk.inj equal
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj rest
    apply congrArg (fun locals => some (foundBody, locals, foundShape))
    apply HolFiniteMapExact.ext
    funext key
    by_cases same : key = parameter
    · subst same; simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY]
    · have different : parameter ≠ key := Ne.symm same
      simp [same, different, HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY]

private def toBeMinLoopBody_hh : ProgHOL 64 :=
  .dec (ofString "pos") .one
    (.op .sub [.op .sub [.var .local (ofString "len"), .const 1#64], .var .local (ofString "i")])
    (.decCall (ofString "l") .one (ofString "u256_limb")
      [.var .local (ofString "a"), .shift .lsr (.var .local (ofString "pos")) (.const 3#64)]
      (.seq
        (.storeByte (.op .add [.var .local (ofString "out"), .var .local (ofString "i")])
          (.op .and
            [.shift .lsr (.var .local (ofString "l"))
              (.panop .mul [.op .and [.var .local (ofString "pos"), .const 7#64], .const 8#64]),
             .const 255#64]))
        (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1#64]))))

private def toBeMinWhile_hh : ProgHOL 64 :=
  .while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "len"))) toBeMinLoopBody_hh

private theorem lookup_resVarEq_ne_hh (m : HolFiniteMapExact MlS (ValueHOL 64))
    (k q : MlS) (old : Option (ValueHOL 64)) (hne : k ≠ q) :
    (m.resVarEq (k, old)).lookup q = m.lookup q := by
  unfold HolFiniteMapExact.resVarEq
  cases old with
  | none => simp [HolFiniteMapExact.eraseEq, FDOMSUB_HOL, hne.symm]
  | some v => simp [HolFiniteMapExact.updateEq, FUPDATE_HOL, hne.symm]

private theorem toBeMinLoopBody_step_hh {F : Type}
    (s : PanSemStateFiniteExact 64 F) (R : List Ivl) (len iv : BitVec 64)
    (outOpt : Option (ValueHOL 64))
    (hcode : s.code = originalRuntimeCode)
    (hdom_eq : s.memaddrs = ordinaryDomain)
    (hiv_lt : iv.toNat < len.toNat)
    (hlen_le : len.toNat ≤ 32)
    (hlen : s.locals.lookup (ofString "len") = some (.val (.word len)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iv)))
    (hout : s.locals.lookup (ofString "out") = outOpt)
    (hR : ∀ outW : BitVec 64, outOpt = some (.val (.word outW)) → (outW.toNat, 32) ∈ R) :
    let res := evaluateHOLFiniteState s toBeMinLoopBody_hh
    M13.ByteFrame R s res.2 ∧
    res.1 ≠ some .continue ∧
    res.1 ≠ some .break ∧
    (∀ eid ev, res.1 ≠ some (.exception eid ev)) ∧
    (∀ r0, res.1 = some r0 → ¬ Resumes (some r0)) ∧
    (res.1 = none →
      res.2.code = originalRuntimeCode ∧
      res.2.memaddrs = ordinaryDomain ∧
      res.2.locals.lookup (ofString "len") = some (.val (.word len)) ∧
      res.2.locals.lookup (ofString "out") = outOpt ∧
      ∃ iv' : BitVec 64, res.2.locals.lookup (ofString "i") = some (.val (.word iv'))) := by
  dsimp only [toBeMinLoopBody_hh]
  rw [evaluateHOLFiniteState_dec_total]; dsimp only
  let posv := (len - 1#64) - iv
  have hev_pos : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .sub [.op .sub [.var .local (ofString "len"), .const 1#64], .var .local (ofString "i")]) =
      some (.val (.word posv)) := by
    simp [evalHOLExact, evalListHOLExact, hlen, hi, wordOpHOL, wordOp, valueIsWord, valueWord, posv]
  rw [hev_pos]; dsimp only
  have hsh1 : shapeEqHOL .one (shapeOfHOLExact (.val (.word posv))) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  rw [if_pos hsh1]; dsimp only
  set s1 := setVarHOLFinite (ofString "pos") (.val (.word posv)) s
  have hs1_len : s1.locals.lookup (ofString "len") = some (.val (.word len)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hlen,
      show ofString "pos" ≠ ofString "len" from M13.mls_ne rfl]
  have hs1_i : s1.locals.lookup (ofString "i") = some (.val (.word iv)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hi,
      show ofString "pos" ≠ ofString "i" from M13.mls_ne rfl]
  have hs1_out : s1.locals.lookup (ofString "out") = outOpt := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hout,
      show ofString "pos" ≠ ofString "out" from M13.mls_ne rfl]
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
  split
  · exact ⟨(M13.ByteFrame.refl R s).setVar _ _ |>.locals _, by simp, by simp, fun _ _ => by simp,
      fun _ h => by injection h with h'; subst h'; exact not_resumes_error,
      fun h => by simp at h⟩
  · rename_i values _
    split
    · exact ⟨(M13.ByteFrame.refl R s).setVar _ _ |>.locals _, by simp, by simp, fun _ _ => by simp,
        fun _ h => by injection h with h'; subst h'; exact not_resumes_error,
        fun h => by simp at h⟩
    · rename_i body' callee ret' hl
      have hsame := lookupCodeHOLFinite_installed_body s1.code.lookup (ofString "u256_limb")
        [(ofString "a", .comb [.one, .one, .one, .one]), (ofString "i", .one)]
        (sourceFnBody Guest.Software.guestFn_u256_limb) body' .one ret' values callee
        (by rw [show s1.code = originalRuntimeCode from hcode]; exact M13.lookup_u256_limb) hl
      subst hsame
      split
      · exact ⟨(M13.ByteFrame.refl R s).setVar _ _ |>.emptyLocals.locals _, by simp, by simp, fun _ _ => by simp,
          fun _ h => by injection h with h'; subst h'; rintro (⟨_, hc⟩ | ⟨_, _, hc, _⟩) <;> simp at hc,
          fun h => by simp at h⟩
      · dsimp only
        have hlf_b : M13.LocFrame (callEntryStateHOLFinite s1 callee)
            (evaluateHOLFiniteState (callEntryStateHOLFinite s1 callee)
              (sourceFnBody Guest.Software.guestFn_u256_limb)).2 :=
          M13.locFrameW_eval _ rfl _
        have hno_exc : ∀ eid ev,
            (evaluateHOLFiniteState (callEntryStateHOLFinite s1 callee)
              (sourceFnBody Guest.Software.guestFn_u256_limb)).1 ≠ some (.exception eid ev) := by
          have hb_limb : sourceFnBody Guest.Software.guestFn_u256_limb =
              .seq (.ite (.cmp .equal (.var .local (ofString "i")) (.const 0#64))
                  (.return (.rfield 0 (.var .local (ofString "a")))) .skip)
                (.seq (.ite (.cmp .equal (.var .local (ofString "i")) (.const 1#64))
                    (.return (.rfield 1 (.var .local (ofString "a")))) .skip)
                  (.seq (.ite (.cmp .equal (.var .local (ofString "i")) (.const 2#64))
                      (.return (.rfield 2 (.var .local (ofString "a")))) .skip)
                    (.seq (.ite (.cmp .equal (.var .local (ofString "i")) (.const 3#64))
                        (.return (.rfield 3 (.var .local (ofString "a")))) .skip)
                      (.return (.const 0#64))))) := rfl
          have hret_ne : ∀ (u : PanSemStateFiniteExact 64 F) (e : ExpHOL 64) eid ev,
              (evaluateHOLFiniteState u (.return e)).1 ≠ some (.exception eid ev) := by
            intro u e eid ev
            rw [evaluateHOLFiniteState_return]
            split <;> (try split) <;> simp
          have hite_ret_ne : ∀ (u : PanSemStateFiniteExact 64 F) (c e : ExpHOL 64) (p2 : ProgHOL 64) eid ev,
              (∀ (u' : PanSemStateFiniteExact 64 F), (evaluateHOLFiniteState u' p2).1 ≠ some (.exception eid ev)) →
              (evaluateHOLFiniteState u (.seq (.ite c (.return e) .skip) p2)).1 ≠ some (.exception eid ev) := by
            intro u c e p2 eid ev hp2
            rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
            split
            · split
              · rw [evaluateHOLFiniteState_skip]; exact hp2 u
              · rcases hr : evaluateHOLFiniteState u (.return e) with ⟨r1, m1⟩
                cases r1 with
                | none => exact hp2 m1
                | some r0 =>
                  have hne := hret_ne u e eid ev; rw [hr] at hne; exact hne
            · simp
          intro eid ev
          rw [hb_limb]
          refine hite_ret_ne _ _ _ _ eid ev (fun _ => hite_ret_ne _ _ _ _ eid ev (fun _ =>
            hite_ret_ne _ _ _ _ eid ev (fun _ => hite_ret_ne _ _ _ _ eid ev (fun u' => hret_ne u' _ eid ev))))
        rcases hrun_l : evaluateHOLFiniteState (callEntryStateHOLFinite s1 callee)
            (sourceFnBody Guest.Software.guestFn_u256_limb) with ⟨rl, post_l⟩
        rw [hrun_l] at hlf_b hno_exc
        have hbf_l : M13.ByteFrame R s post_l :=
          M13.ByteFrame.of_locFrame R (by unfold M13.LocFrame at hlf_b ⊢; dsimp only at hlf_b; rw [hlf_b]; rfl)
        rcases rl with _ | rl
        · exact ⟨hbf_l.locals _, by simp, by simp, fun _ _ => by simp,
            fun _ h => by injection h with h'; subst h'; exact not_resumes_error,
            fun h => by simp at h⟩
        · cases rl with
          | returned vl =>
            dsimp only
            split
            · dsimp only
              set s2 := setVarHOLFinite (ofString "l") vl { post_l with locals := s1.locals }
              have hs2_bf : M13.ByteFrame R s s2 := (hbf_l.locals _).setVar _ _
              have hs2_code : s2.code = originalRuntimeCode := by rw [hs2_bf.1]; exact hcode
              have hs2_dom : s2.memaddrs = ordinaryDomain := by rw [hs2_bf.1]; exact hdom_eq
              have hs2_len : s2.locals.lookup (ofString "len") = some (.val (.word len)) := by
                simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs1_len,
                  show ofString "l" ≠ ofString "len" from M13.mls_ne rfl]
              have hs2_i : s2.locals.lookup (ofString "i") = some (.val (.word iv)) := by
                simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs1_i,
                  show ofString "l" ≠ ofString "i" from M13.mls_ne rfl]
              have hs2_out : s2.locals.lookup (ofString "out") = outOpt := by
                simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs1_out,
                  show ofString "l" ≠ ofString "out" from M13.mls_ne rfl]
              let sbProg : ProgHOL 64 := .storeByte (.op .add [.var .local (ofString "out"), .var .local (ofString "i")])
                (.op .and
                  [.shift .lsr (.var .local (ofString "l"))
                    (.panop .mul [.op .and [.var .local (ofString "pos"), .const 7#64], .const 8#64]),
                   .const 255#64])
              have hbf_sb : M13.ByteFrame R s2 (evaluateHOLFiniteState s2 sbProg).2 := by
                refine M13.byteFrame_storeByte s2 _ _ (fun addr hdst hdom => ?_)
                rcases hout_case : outOpt with _ | outVal
                · simp [evalHOLExact, evalListHOLExact, hs2_out, hout_case] at hdst
                · cases outVal with
                  | rStruct _ =>
                    simp [evalHOLExact, evalListHOLExact, hs2_out, hs2_i, hout_case, List.all, wordOpHOL, wordOp, valueIsWord] at hdst
                  | nStruct _ _ =>
                    simp [evalHOLExact, evalListHOLExact, hs2_out, hs2_i, hout_case, List.all, wordOpHOL, wordOp, valueIsWord] at hdst
                  | val wl =>
                    cases wl with
                    | word outW =>
                      have haddr_eq : addr = outW + iv := by
                        simp [evalHOLExact, evalListHOLExact, hs2_out, hs2_i, hout_case,
                          wordOpHOL, wordOp, valueIsWord, valueWord] at hdst
                        exact hdst.symm
                      subst haddr_eq
                      rw [hs2_dom] at hdom
                      have hsb_val : sourceBase = 2701131776 := rfl
                      have hnw := M13.add_no_wrap_of_memaddrs outW iv (by omega) hdom
                      exact ⟨(outW.toNat, 32), hR outW hout_case, by rw [hnw.2.1]; omega, by rw [hnw.2.1]; omega⟩
              rw [evaluateHOLFiniteState_seq_line780]
              rcases hsb_run : evaluateHOLFiniteState s2 sbProg with ⟨rsb, s3⟩
              rw [hsb_run] at hbf_sb
              have hsb_ctrl := evaluate_storeByte_control_frame s2
                (.op .add [.var .local (ofString "out"), .var .local (ofString "i")])
                (.op .and
                  [.shift .lsr (.var .local (ofString "l"))
                    (.panop .mul [.op .and [.var .local (ofString "pos"), .const 7#64], .const 8#64]),
                   .const 255#64])
              have hsb_r : rsb = none ∨ rsb = some .error := by
                have h1 := hsb_ctrl.1; change (evaluateHOLFiniteState s2 sbProg).1 = _ ∨ (evaluateHOLFiniteState s2 sbProg).1 = _ at h1
                rw [hsb_run] at h1; exact h1
              have hs3_loc : s3.locals = s2.locals := by
                have h2 := hsb_ctrl.2.2.1; change (evaluateHOLFiniteState s2 sbProg).2.locals = s2.locals at h2
                rw [hsb_run] at h2; exact h2
              rcases hsb_r with rfl | rfl
              · dsimp only
                rw [evaluateHOLFiniteState_assign]
                have hs3_i : s3.locals.lookup (ofString "i") = some (.val (.word iv)) := by
                  rw [hs3_loc]; exact hs2_i
                have hs3_len : s3.locals.lookup (ofString "len") = some (.val (.word len)) := by
                  rw [hs3_loc]; exact hs2_len
                have hs3_out : s3.locals.lookup (ofString "out") = outOpt := by
                  rw [hs3_loc]; exact hs2_out
                have hev_inc : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
                    (.op .add [.var .local (ofString "i"), .const 1#64]) = some (.val (.word (iv + 1#64))) := by
                  simp [evalHOLExact, evalListHOLExact, hs3_i, wordOpHOL, wordOp, valueIsWord, valueWord]
                rw [hev_inc]; dsimp only
                have hval_i : isValidValueHOLFinite s3 .local (ofString "i") (.val (.word (iv + 1#64))) = true := by
                  simp [isValidValueHOLFinite, lookupKvarHOLFinite, hs3_i, shapeOfHOLExact, shapeEqHOL]
                rw [if_pos hval_i]; dsimp only
                have hbf_all : M13.ByteFrame R s (setKvarHOLFinite .local (ofString "i") (.val (.word (iv + 1#64))) s3) :=
                  (hs2_bf.trans hbf_sb).setVar _ _
                let finalSt :=
                  let __src2 := setKvarHOLFinite .local (ofString "i") (.val (.word (iv + 1#64))) s3
                  let __src1 : PanSemStateFiniteExact 64 F := { __src2 with locals := __src2.locals.resVarEq (ofString "l", s1.locals.lookup (ofString "l")) }
                  ({ __src1 with locals := __src1.locals.resVarEq (ofString "pos", s.locals.lookup (ofString "pos")) } : PanSemStateFiniteExact 64 F)
                have hbf_final : M13.ByteFrame R s finalSt := hbf_all.locals _ |>.locals _
                have hf_code : finalSt.code = originalRuntimeCode := by
                  have h1 := hbf_all.1; dsimp only [finalSt]; rw [h1]; exact hcode
                have hf_dom : finalSt.memaddrs = ordinaryDomain := by
                  have h1 := hbf_all.1; dsimp only [finalSt]; rw [h1]; exact hdom_eq
                refine ⟨hbf_final, by simp, by simp, fun _ _ => by simp, fun _ h => by simp at h, fun _ => ⟨hf_code, hf_dom, ?_, ?_, iv + 1#64, ?_⟩⟩
                · change ((setKvarHOLFinite .local (ofString "i") (.val (.word (iv + 1#64))) s3).locals.resVarEq
                      (ofString "l", s1.locals.lookup (ofString "l")) |>.resVarEq
                      (ofString "pos", s.locals.lookup (ofString "pos"))).lookup (ofString "len") = _
                  rw [lookup_resVarEq_ne_hh _ _ _ _ (M13.mls_ne rfl), lookup_resVarEq_ne_hh _ _ _ _ (M13.mls_ne rfl)]
                  simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_len,
                    show ofString "i" ≠ ofString "len" from M13.mls_ne rfl]
                · change ((setKvarHOLFinite .local (ofString "i") (.val (.word (iv + 1#64))) s3).locals.resVarEq
                      (ofString "l", s1.locals.lookup (ofString "l")) |>.resVarEq
                      (ofString "pos", s.locals.lookup (ofString "pos"))).lookup (ofString "out") = _
                  rw [lookup_resVarEq_ne_hh _ _ _ _ (M13.mls_ne rfl), lookup_resVarEq_ne_hh _ _ _ _ (M13.mls_ne rfl)]
                  simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_out,
                    show ofString "i" ≠ ofString "out" from M13.mls_ne rfl]
                · change ((setKvarHOLFinite .local (ofString "i") (.val (.word (iv + 1#64))) s3).locals.resVarEq
                      (ofString "l", s1.locals.lookup (ofString "l")) |>.resVarEq
                      (ofString "pos", s.locals.lookup (ofString "pos"))).lookup (ofString "i") = _
                  rw [lookup_resVarEq_ne_hh _ _ _ _ (M13.mls_ne rfl), lookup_resVarEq_ne_hh _ _ _ _ (M13.mls_ne rfl)]
                  simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
              · exact ⟨(hs2_bf.trans hbf_sb).locals _ |>.locals _, by simp, by simp, fun _ _ => by simp,
                  fun _ h => by injection h with h'; subst h'; exact not_resumes_error,
                  fun h => by simp at h⟩
            · exact ⟨hbf_l.locals _, by simp, by simp, fun _ _ => by simp,
                fun _ h => by injection h with h'; subst h'; exact not_resumes_error,
                fun h => by simp at h⟩
          | exception eid ev => exact absurd rfl (hno_exc eid ev)
          | «break» | «continue» =>
            exact ⟨hbf_l.locals _, by simp, by simp, fun _ _ => by simp,
              fun _ h => by injection h with h'; subst h'; exact not_resumes_error,
              fun h => by simp at h⟩
          | timeOut | error | finalFfi _ =>
            exact ⟨hbf_l.emptyLocals.locals _, by simp, by simp, fun _ _ => by simp,
              fun _ h => by injection h with h'; subst h'; rintro (⟨_, hc⟩ | ⟨_, _, hc, _⟩) <;> simp at hc,
              fun h => by simp at h⟩

private theorem toBeMinWhile_run_hh {F : Type}
    (s : PanSemStateFiniteExact 64 F) (R : List Ivl) (len iv : BitVec 64)
    (outOpt : Option (ValueHOL 64))
    (hcode : s.code = originalRuntimeCode)
    (hdom_eq : s.memaddrs = ordinaryDomain)
    (hlen_le : len.toNat ≤ 32)
    (hlen : s.locals.lookup (ofString "len") = some (.val (.word len)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iv)))
    (hout : s.locals.lookup (ofString "out") = outOpt)
    (hR : ∀ outW : BitVec 64, outOpt = some (.val (.word outW)) → (outW.toNat, 32) ∈ R) :
    let res := evaluateHOLFiniteState s toBeMinWhile_hh
    M13.ByteFrame R s res.2 ∧
    (res.1 = none → res.2.locals.lookup (ofString "len") = some (.val (.word len))) ∧
    (∀ eid ev, res.1 ≠ some (.exception eid ev)) ∧
    (∀ r0, res.1 = some r0 → ¬ Resumes (some r0)) := by
  suffices hrec : ∀ (clk : Nat) (st : PanSemStateFiniteExact 64 F) (w : BitVec 64),
      st.clock = clk →
      st.code = originalRuntimeCode →
      st.memaddrs = ordinaryDomain →
      st.locals.lookup (ofString "len") = some (.val (.word len)) →
      st.locals.lookup (ofString "i") = some (.val (.word w)) →
      st.locals.lookup (ofString "out") = outOpt →
      let res := evaluateHOLFiniteState st toBeMinWhile_hh
      M13.ByteFrame R st res.2 ∧
      (res.1 = none → res.2.locals.lookup (ofString "len") = some (.val (.word len))) ∧
      (∀ eid ev, res.1 ≠ some (.exception eid ev)) ∧
      (∀ r0, res.1 = some r0 → ¬ Resumes (some r0)) by
    exact hrec s.clock s iv rfl hcode hdom_eq hlen hi hout
  intro clk
  induction clk using Nat.strongRecOn with
  | ind clk ih =>
    intro st w hclk hst_code hst_dom hst_len hst_i hst_out
    dsimp only [toBeMinWhile_hh]
    rw [evaluateHOLFiniteState_while_total, evalHOLFinite_eq_toExact]
    have hevc : @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a))
        (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "len"))) =
        some (.val (.word (if w.toNat < len.toNat then 1 else 0))) := by
      simp only [evalHOLExact, hst_i, hst_len, Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
        BitVec.lt_def, decide_eq_true_eq]
    rw [hevc]; dsimp only
    by_cases hlt_w : w.toNat < len.toNat
    · rw [if_pos hlt_w]
      have h1 : (1 : BitVec 64) ≠ 0 := by intro h; cases h
      rw [if_pos h1]
      by_cases hcz : st.clock = 0
      · rw [if_pos hcz]
        exact ⟨(M13.ByteFrame.refl R st).emptyLocals, fun h => by simp at h, fun _ _ => by simp,
          fun _ h => by injection h with h'; subst h'; rintro (⟨_, hc⟩ | ⟨_, _, hc, _⟩) <;> simp at hc⟩
      · rw [if_neg hcz]
        rw [fixClockHOLFinite_evaluateState]
        have hstep := toBeMinLoopBody_step_hh (decClockHOLFinite st) R len w outOpt
          hst_code hst_dom hlt_w hlen_le hst_len hst_i hst_out hR
        have hcle := evaluateHOLFiniteState_clock_le (decClockHOLFinite st) toBeMinLoopBody_hh
        rcases hbr : evaluateHOLFiniteState (decClockHOLFinite st) toBeMinLoopBody_hh with ⟨rb, mid⟩
        rw [hbr] at hstep hcle; dsimp only at hstep hcle
        have hclk_lt : mid.clock < clk := by change mid.clock ≤ st.clock - 1 at hcle; omega
        have hbf1 : M13.ByteFrame R st mid :=
          (M13.ByteFrame.of_locFrame R (s := st) (t := decClockHOLFinite st) rfl).trans hstep.1
        cases rb with
        | none =>
          obtain ⟨hm_code, hm_dom, hm_len, hm_out, w', hm_i⟩ := hstep.2.2.2.2.2 rfl
          have hih := ih mid.clock hclk_lt mid w' rfl hm_code hm_dom hm_len hm_i hm_out
          exact ⟨hbf1.trans hih.1, hih.2.1, hih.2.2.1, hih.2.2.2⟩
        | some r' =>
          cases r' with
          | «continue» => exact absurd rfl hstep.2.1
          | «break» => exact absurd rfl hstep.2.2.1
          | returned v =>
            exact ⟨hbf1, fun h => by simp at h, fun _ _ => by simp,
              fun _ h => by injection h with h'; subst h'; exact hstep.2.2.2.2.1 (.returned v) rfl⟩
          | exception eid ev =>
            exact absurd rfl (hstep.2.2.2.1 eid ev)
          | timeOut =>
            exact ⟨hbf1, fun h => by simp at h, fun _ _ => by simp,
              fun _ h => by injection h with h'; subst h'; exact hstep.2.2.2.2.1 .timeOut rfl⟩
          | finalFfi f =>
            exact ⟨hbf1, fun h => by simp at h, fun _ _ => by simp,
              fun _ h => by injection h with h'; subst h'; exact hstep.2.2.2.2.1 (.finalFfi f) rfl⟩
          | error =>
            exact ⟨hbf1, fun h => by simp at h, fun _ _ => by simp,
              fun _ h => by injection h with h'; subst h'; exact not_resumes_error⟩
    · rw [if_neg hlt_w]
      have h0 : ¬ ((0 : BitVec 64) ≠ 0) := not_not.mpr rfl
      rw [if_neg h0]
      exact ⟨M13.ByteFrame.refl R st, fun _ => hst_len, fun _ _ => by simp, fun _ h => by simp at h⟩

private theorem byteFrame_to_heapByteEff {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {gw : List String}
    (hAR : ArenaReady s) (hBF : M13.ByteFrame Rl s post) :
    HeapByteEff s post Rl gw := by
  have heff : M13.ByteRegionEffect s post Rl := by
    refine ⟨by rw [hBF.1], by rw [hBF.1], by rw [hBF.1], by rw [hBF.1], by rw [hBF.1], by rw [hBF.1],
      ?_, ?_, ?_⟩
    · intro a hna; by_contra hne; exact hna (hBF.2.1 a hne).1
    · intro a hno; by_contra hne; obtain ⟨_, ri, hri, hch⟩ := hBF.2.1 a hne; exact hno ri hri hch
    · intro b hb hno; by_contra hne; obtain ⟨ri, hri, hin⟩ := hBF.2.2 b hb hne; exact hno ri hri hin
  exact HeapByteEff.of_m13_bre hAR heff

private theorem u256_byte_length_no_exc {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hcode : s.code = originalRuntimeCode) :
    ∀ eid ev,
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_u256_byte_length)).1 ≠
        some (.exception eid ev) := by
  have hbl64_no_exc : ∀ (t : PanSemStateFiniteExact 64 F) eid ev,
      (evaluateHOLFiniteState t (sourceFnBody Guest.Software.guestFn_bit_length64)).1 ≠
        some (.exception eid ev) := by
    intro t eid ev
    have hb64 : sourceFnBody Guest.Software.guestFn_bit_length64 =
        .dec (ofString "n") .one (.const 0#64)
          (.seq (.ite (.cmp .notEqual (.shift .lsr (.var .local (ofString "x")) (.const 32#64)) (.const 0#64))
              (.seq (.assign .local (ofString "n") (.op .add [.var .local (ofString "n"), .const 32#64]))
                (.assign .local (ofString "x") (.shift .lsr (.var .local (ofString "x")) (.const 32#64)))) .skip)
            (.seq (.ite (.cmp .notEqual (.shift .lsr (.var .local (ofString "x")) (.const 16#64)) (.const 0#64))
                (.seq (.assign .local (ofString "n") (.op .add [.var .local (ofString "n"), .const 16#64]))
                  (.assign .local (ofString "x") (.shift .lsr (.var .local (ofString "x")) (.const 16#64)))) .skip)
              (.seq (.ite (.cmp .notEqual (.shift .lsr (.var .local (ofString "x")) (.const 8#64)) (.const 0#64))
                  (.seq (.assign .local (ofString "n") (.op .add [.var .local (ofString "n"), .const 8#64]))
                    (.assign .local (ofString "x") (.shift .lsr (.var .local (ofString "x")) (.const 8#64)))) .skip)
                (.seq (.ite (.cmp .notEqual (.shift .lsr (.var .local (ofString "x")) (.const 4#64)) (.const 0#64))
                    (.seq (.assign .local (ofString "n") (.op .add [.var .local (ofString "n"), .const 4#64]))
                      (.assign .local (ofString "x") (.shift .lsr (.var .local (ofString "x")) (.const 4#64)))) .skip)
                  (.seq (.ite (.cmp .notEqual (.shift .lsr (.var .local (ofString "x")) (.const 2#64)) (.const 0#64))
                      (.seq (.assign .local (ofString "n") (.op .add [.var .local (ofString "n"), .const 2#64]))
                        (.assign .local (ofString "x") (.shift .lsr (.var .local (ofString "x")) (.const 2#64)))) .skip)
                    (.seq (.ite (.cmp .notEqual (.shift .lsr (.var .local (ofString "x")) (.const 1#64)) (.const 0#64))
                        (.seq (.assign .local (ofString "n") (.op .add [.var .local (ofString "n"), .const 1#64]))
                          (.assign .local (ofString "x") (.shift .lsr (.var .local (ofString "x")) (.const 1#64)))) .skip)
                      (.return (.op .add [.var .local (ofString "n"), .var .local (ofString "x")])))))))) := rfl
    have hstep_ne : ∀ (u : PanSemStateFiniteExact 64 F) (c : ExpHOL 64) (p1 p2 : ProgHOL 64),
        (∀ (u' : PanSemStateFiniteExact 64 F), (evaluateHOLFiniteState u' p1).1 ≠ some (.exception eid ev) ∧
          (evaluateHOLFiniteState u' p1).1 ≠ some .continue) →
        (∀ (u' : PanSemStateFiniteExact 64 F), (evaluateHOLFiniteState u' p2).1 ≠ some (.exception eid ev)) →
        (evaluateHOLFiniteState u (.seq (.ite c p1 .skip) p2)).1 ≠ some (.exception eid ev) := by
      intro u c p1 p2 hp1 hp2
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
      split
      · split
        · rw [evaluateHOLFiniteState_skip]; exact hp2 u
        · rcases hr : evaluateHOLFiniteState u p1 with ⟨r1, m1⟩
          cases r1 with
          | none => exact hp2 m1
          | some r0 =>
            have hne := (hp1 u).1; rw [hr] at hne; exact hne
      · simp
    have hass_ne : ∀ (u : PanSemStateFiniteExact 64 F) nm ex,
        (evaluateHOLFiniteState u (.assign .local nm ex)).1 = none ∨
        (evaluateHOLFiniteState u (.assign .local nm ex)).1 = some .error := by
      intro u nm ex; rw [evaluateHOLFiniteState_assign]
      split
      · exact Or.inr rfl
      · split
        · exact Or.inl rfl
        · exact Or.inr rfl
    have hseq_ass : ∀ (u : PanSemStateFiniteExact 64 F) n1 e1 n2 e2,
        (evaluateHOLFiniteState u (.seq (.assign .local n1 e1) (.assign .local n2 e2))).1 ≠ some (.exception eid ev) ∧
        (evaluateHOLFiniteState u (.seq (.assign .local n1 e1) (.assign .local n2 e2))).1 ≠ some .continue := by
      intro u n1 e1 n2 e2
      rw [evaluateHOLFiniteState_seq_line780]
      rcases h1 : evaluateHOLFiniteState u (.assign .local n1 e1) with ⟨r1, m1⟩
      have ha1 := hass_ne u n1 e1; rw [h1] at ha1
      rcases ha1 with rfl | rfl
      · dsimp only
        rcases hass_ne m1 n2 e2 with h2 | h2 <;> rw [h2] <;> simp
      · simp
    rw [hb64, evaluateHOLFiniteState_dec_total]; dsimp only
    split
    · simp
    · split
      · dsimp only
        intro hexc
        revert hexc
        apply hstep_ne; · intro u'; exact hseq_ass u' _ _ _ _
        intro u2; apply hstep_ne; · intro u'; exact hseq_ass u' _ _ _ _
        intro u3; apply hstep_ne; · intro u'; exact hseq_ass u' _ _ _ _
        intro u4; apply hstep_ne; · intro u'; exact hseq_ass u' _ _ _ _
        intro u5; apply hstep_ne; · intro u'; exact hseq_ass u' _ _ _ _
        intro u6; apply hstep_ne; · intro u'; exact hseq_ass u' _ _ _ _
        intro u'; rw [evaluateHOLFiniteState_return]; split <;> (try split) <;> simp
      · simp
  have hubl_no_exc : ∀ (t : PanSemStateFiniteExact 64 F), t.code = originalRuntimeCode → ∀ eid ev,
      (evaluateHOLFiniteState t (sourceFnBody Guest.Software.guestFn_u256_bit_length)).1 ≠
        some (.exception eid ev) := by
    intro t ht eid ev
    have hdec_bl : ∀ (u : PanSemStateFiniteExact 64 F), u.code = originalRuntimeCode →
        ∀ nm ex cont,
          (∀ u' : PanSemStateFiniteExact 64 F, (evaluateHOLFiniteState u' cont).1 ≠ some (.exception eid ev)) →
          (evaluateHOLFiniteState u (.decCall nm .one (ofString "bit_length64") [ex] cont)).1 ≠
            some (.exception eid ev) := by
      intro u hu nm ex cont hcont
      rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
      split
      · simp
      · rename_i vs _
        split
        · simp
        · rename_i b' cal' r' hl'
          have hs' := lookupCodeHOLFinite_installed_body u.code.lookup (ofString "bit_length64")
            [(ofString "x", .one)] (sourceFnBody Guest.Software.guestFn_bit_length64) b' .one r' vs cal'
            (by rw [hu]; exact M13.lookup_bit_length64) hl'
          subst hs'
          split
          · simp
          · dsimp only
            have hne64 := hbl64_no_exc (callEntryStateHOLFinite u cal') eid ev
            rcases hrun64 : evaluateHOLFiniteState (callEntryStateHOLFinite u cal')
                (sourceFnBody Guest.Software.guestFn_bit_length64) with ⟨r64, p64⟩
            rw [hrun64] at hne64
            rcases r64 with _ | r64
            · simp
            · cases r64 with
              | returned _ => dsimp only; split <;> [exact hcont _; simp]
              | exception _ _ => exact hne64
              | _ => simp
    have hite_bl : ∀ (u : PanSemStateFiniteExact 64 F), u.code = originalRuntimeCode →
        ∀ c nm ex retE nextP,
          (∀ m : PanSemStateFiniteExact 64 F, m.code = originalRuntimeCode →
            (evaluateHOLFiniteState m nextP).1 ≠ some (.exception eid ev)) →
          (evaluateHOLFiniteState u (.seq (.ite c
              (.decCall nm .one (ofString "bit_length64") [ex] (.return retE)) .skip) nextP)).1 ≠
            some (.exception eid ev) := by
      intro u hu c nm ex retE nextP hnext
      have hlf1 : M13.LocFrame u (evaluateHOLFiniteState u
          (.ite c (.decCall nm .one (ofString "bit_length64") [ex] (.return retE)) .skip)).2 :=
        M13.locFrame_ite c
          (M13.locFrame_decCall hu M13.funLocFrame_bit_length64 _ _ _ (fun x _ => M13.locFrameW_eval _ rfl x))
          (M13.locFrameW_eval _ rfl u)
      rw [evaluateHOLFiniteState_seq_line780]
      rcases h1 : evaluateHOLFiniteState u
          (.ite c (.decCall nm .one (ofString "bit_length64") [ex] (.return retE)) .skip) with ⟨r1, m1⟩
      rw [h1] at hlf1
      cases r1 with
      | none => exact hnext m1 (hlf1.code.trans hu)
      | some r0 =>
        have hne1 : (evaluateHOLFiniteState u
            (.ite c (.decCall nm .one (ofString "bit_length64") [ex] (.return retE)) .skip)).1 ≠
              some (.exception eid ev) := by
          rw [evaluateHOLFiniteState_ite]
          split
          · split
            · simp [evaluateHOLFiniteState_skip]
            · exact hdec_bl u hu nm ex (.return retE) (fun u' => by
                rw [evaluateHOLFiniteState_return]; split <;> (try split) <;> simp)
          · simp
        rw [h1] at hne1; exact hne1
    dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_u256_bit_length,
      InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural, List.map, Option.map]
    apply hite_bl t ht; intro m1 hm1
    apply hite_bl m1 hm1; intro m2 hm2
    apply hite_bl m2 hm2; intro m3 hm3
    rw [evaluateHOLFiniteState_call]
    split
    · simp
    · rename_i vs _
      split
      · simp
      · rename_i b' cal' r' hl'
        have hs' := lookupCodeHOLFinite_installed_body m3.code.lookup (ofString "bit_length64")
          [(ofString "x", .one)] (sourceFnBody Guest.Software.guestFn_bit_length64) b' .one r' vs cal'
          (by rw [hm3]; exact M13.lookup_bit_length64) hl'
        subst hs'
        split
        · simp
        · dsimp only
          have hne64 := hbl64_no_exc (callEntryStateHOLFinite m3 cal') eid ev
          rcases hrun64 : evaluateHOLFiniteState (callEntryStateHOLFinite m3 cal')
              (sourceFnBody Guest.Software.guestFn_bit_length64) with ⟨r64, p64⟩
          rw [hrun64] at hne64
          rcases r64 with _ | r64
          · simp
          · cases r64 with
            | returned _ => dsimp only; split <;> simp
            | exception _ _ => exact hne64
            | _ => simp
  intro eid ev
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_u256_byte_length,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
  split
  · simp
  · rename_i vs _
    split
    · simp
    · rename_i b' cal' r' hl'
      have hs' := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "u256_bit_length")
        [(ofString "a", .comb [.one, .one, .one, .one])]
        (sourceFnBody Guest.Software.guestFn_u256_bit_length) b' .one r' vs cal'
        (by rw [hcode]; exact M13.lookup_u256_bit_length) hl'
      subst hs'
      split
      · simp
      · dsimp only
        have hne_ubl := hubl_no_exc (callEntryStateHOLFinite s cal') hcode eid ev
        rcases hrun_ubl : evaluateHOLFiniteState (callEntryStateHOLFinite s cal')
            (sourceFnBody Guest.Software.guestFn_u256_bit_length) with ⟨rubl, publ⟩
        rw [hrun_ubl] at hne_ubl
        rcases rubl with _ | rubl
        · simp
        · cases rubl with
          | returned _ =>
            dsimp only
            split
            · dsimp only; rw [evaluateHOLFiniteState_return]; split <;> (try split) <;> simp
            · simp
          | exception _ _ => exact hne_ubl
          | _ => simp

private theorem eval_decCall_u256_to_be_min {F : Type}
    (s : PanSemStateFiniteExact 64 F) (lname : String) (vExp outExp : ExpHOL 64)
    (w0 w1 w2 w3 out0 : BitVec 64) (cont : ProgHOL 64) (Rl : List Ivl) (gw : List String)
    (hcode : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hv : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) vExp =
      some (.rStruct [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3)]))
    (hout : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) outExp =
      some (.val (.word out0)))
    (hin_ivl : (out0.toNat, 32) ∈ Rl)
    (hnt : (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "u256_to_be_min") [vExp, outExp] cont)).1 ≠
      some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.decCall (ofString lname) .one (ofString "u256_to_be_min") [vExp, outExp] cont)).1) :
    ∃ (nw : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      nw.toNat ≤ 32 ∧
      mid.globals = s.globals ∧
      mid.locals = s.locals.update (ofString lname, .val (.word nw)) ∧
      HeapByteEff s mid Rl gw ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState mid cont).1 ∧
      (evaluateHOLFiniteState s
        (.decCall (ofString lname) .one (ofString "u256_to_be_min") [vExp, outExp] cont)) =
        ((evaluateHOLFiniteState mid cont).1,
         { (evaluateHOLFiniteState mid cont).2 with
           locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState mid cont).2.locals
             (ofString lname, s.locals.lookup (ofString lname)) }) := by
  let vval : ValueHOL 64 := .rStruct [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3)]
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hres ⊢
  have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [vExp, outExp] = some [vval, .val (.word out0)] := by
    simp [evalListHOLFinite, evalListHOLExact, hv, hout, vval]
  have hlk : PanSemStateFiniteExact.lookupCodeHOLFinite s.code.lookup (ofString "u256_to_be_min")
      [vval, .val (.word out0)] =
      some (sourceFnBody Guest.Software.guestFn_u256_to_be_min,
        (HolFiniteMapExact.empty.update (ofString "a", vval)).update (ofString "out", .val (.word out0)), .one) :=
    pan_u256_word_lookup s.code.lookup (ofString "u256_to_be_min")
      (ofString "a") (ofString "out")
      (sourceFnBody Guest.Software.guestFn_u256_to_be_min) w0 w1 w2 w3 out0 (by decide)
      (by rw [hcode]; exact M13.lookup_u256_to_be_min)
  rw [ha] at hnt hres ⊢
  dsimp only at hnt hres ⊢
  rw [hlk] at hnt hres ⊢
  dsimp only at hnt hres ⊢
  by_cases hcz : s.clock = 0
  · simp [hcz] at hnt
  · simp only [hcz, ↓reduceIte] at hnt hres ⊢
    set cmap := (HolFiniteMapExact.empty.update (ofString "a", vval)).update (ofString "out", .val (.word out0))
    set ent := callEntryStateHOLFinite s cmap
    have hent_code : ent.code = originalRuntimeCode := hcode
    have hent_dom : ent.memaddrs = ordinaryDomain := hAR.1.memaddrs
    have hent_out : ent.locals.lookup (ofString "out") = some (.val (.word out0)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hbody_run :
        let res := evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_u256_to_be_min)
        M13.ByteFrame Rl ent res.2 ∧
        (∀ rv, res.1 = some (.returned rv) → ∃ nw : BitVec 64, rv = .val (.word nw) ∧ nw.toNat ≤ 32) ∧
        (∀ eid ev, res.1 ≠ some (.exception eid ev)) := by
      dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_u256_to_be_min,
        InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural, List.map, Option.map]
      rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
      split
      · exact ⟨M13.ByteFrame.refl Rl ent, fun _ h => by simp at h, fun _ _ => by simp⟩
      · rename_i values _
        split
        · exact ⟨M13.ByteFrame.refl Rl ent, fun _ h => by simp at h, fun _ _ => by simp⟩
        · rename_i body' callee ret' hl
          have hsame := lookupCodeHOLFinite_installed_body ent.code.lookup (ofString "u256_byte_length")
            [(ofString "a", .comb [.one, .one, .one, .one])]
            (sourceFnBody Guest.Software.guestFn_u256_byte_length) body' .one ret' values callee
            (by rw [hent_code]; exact M13.lookup_u256_byte_length) hl
          subst hsame
          split
          · exact ⟨(M13.ByteFrame.refl Rl ent).emptyLocals, fun _ h => by simp at h, fun _ _ => by simp⟩
          · dsimp only
            have hlf_bl := M13.locFrame_u256_byte_length_body (callEntryStateHOLFinite ent callee) hent_code
            have hno_exc_bl := u256_byte_length_no_exc (callEntryStateHOLFinite ent callee) hent_code
            rcases hrun_bl : evaluateHOLFiniteState (callEntryStateHOLFinite ent callee)
                (sourceFnBody Guest.Software.guestFn_u256_byte_length) with ⟨rbl, post_bl⟩
            rw [hrun_bl] at hlf_bl hno_exc_bl
            have hbf_bl : M13.ByteFrame Rl ent post_bl :=
              M13.ByteFrame.of_locFrame Rl (by unfold M13.LocFrame at hlf_bl ⊢; dsimp only at hlf_bl; rw [hlf_bl]; rfl)
            rcases rbl with _ | rbl
            · exact ⟨hbf_bl, fun _ h => by simp at h, fun _ _ => by simp⟩
            · cases rbl with
              | returned vbl =>
                obtain ⟨len, rfl, hlen_le⟩ := M13.u256_byte_length_body_le_32
                  (callEntryStateHOLFinite ent callee) hent_code vbl (by rw [hrun_bl])
                dsimp only
                split
                · dsimp only
                  set s1 := setVarHOLFinite (ofString "len") (.val (.word len)) { post_bl with locals := ent.locals }
                  have hs1_bf : M13.ByteFrame Rl ent s1 := (hbf_bl.locals _).setVar _ _
                  rw [evaluateHOLFiniteState_dec_total]; dsimp only
                  have h0_ev : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
                      (.const 0#64) = some (.val (.word 0#64)) := rfl
                  rw [h0_ev]; dsimp only
                  have hsh0 : shapeEqHOL .one (shapeOfHOLExact (.val (.word 0#64))) = true := by
                    simp [shapeEqHOL, shapeOfHOLExact]
                  rw [if_pos hsh0]; dsimp only
                  set s2 := setVarHOLFinite (ofString "i") (.val (.word 0#64)) s1
                  have hs2_bf : M13.ByteFrame Rl ent s2 := hs1_bf.setVar _ _
                  have hs2_code : s2.code = originalRuntimeCode := by rw [hs2_bf.1]; exact hent_code
                  have hs2_dom : s2.memaddrs = ordinaryDomain := by rw [hs2_bf.1]; exact hent_dom
                  have hs2_len : s2.locals.lookup (ofString "len") = some (.val (.word len)) := by
                    simp [s2, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                      show ofString "i" ≠ ofString "len" from M13.mls_ne rfl]
                  have hs2_i : s2.locals.lookup (ofString "i") = some (.val (.word 0#64)) := by
                    simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                  have hs2_out : s2.locals.lookup (ofString "out") = some (.val (.word out0)) := by
                    simp [s2, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hent_out,
                      show ofString "i" ≠ ofString "out" from M13.mls_ne rfl,
                      show ofString "len" ≠ ofString "out" from M13.mls_ne rfl]
                  have hR_mem : ∀ outW : BitVec 64,
                      some (.val (.word out0) : ValueHOL 64) = some (.val (.word outW)) →
                      (outW.toNat, 32) ∈ Rl := by
                    intro outW h; injection h with h1; injection h1 with h2; injection h2 with h3
                    subst h3; exact hin_ivl
                  have hseq_run :
                      let sq := evaluateHOLFiniteState s2 (.seq toBeMinWhile_hh (.return (.var .local (ofString "len"))))
                      M13.ByteFrame Rl s2 sq.2 ∧
                      (∀ rv, sq.1 = some (.returned rv) → ∃ nw : BitVec 64, rv = .val (.word nw) ∧ nw.toNat ≤ 32) ∧
                      (∀ eid ev, sq.1 ≠ some (.exception eid ev)) := by
                    dsimp only
                    rw [evaluateHOLFiniteState_seq_line780]
                    have hw_run_p := toBeMinWhile_run_hh s2 Rl len 0#64 (some (.val (.word out0)))
                      hs2_code hs2_dom hlen_le hs2_len hs2_i hs2_out hR_mem
                    rcases hw_run : evaluateHOLFiniteState s2 toBeMinWhile_hh with ⟨rw_res, s3⟩
                    rw [hw_run] at hw_run_p
                    dsimp only at hw_run_p ⊢
                    cases rw_res with
                    | some rw0 =>
                      dsimp only
                      refine ⟨hw_run_p.1, ?_, ?_⟩
                      · intro rv hret
                        exact absurd (Or.inl ⟨rv, hret⟩) (hw_run_p.2.2.2 rw0 rfl)
                      · intro eid ev hexc
                        injection hexc with hexc'; subst hexc'
                        exact hw_run_p.2.2.1 eid ev rfl
                    | none =>
                      dsimp only
                      have hs3_len := hw_run_p.2.1 rfl
                      rw [evaluateHOLFiniteState_return]
                      have hev_ret : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
                          (.var .local (ofString "len")) = some (.val (.word len)) := hs3_len
                      rw [hev_ret]; dsimp only
                      have hsz : sizeOfShapeWithContextHOL s3.structs (shapeOfHOLExact (.val (.word len) : ValueHOL 64)) ≤ 32 := by
                        simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
                      rw [if_pos hsz]; dsimp only
                      refine ⟨hw_run_p.1.emptyLocals,
                        fun rv hret => ?_, fun _ _ h => by simp at h⟩
                      · injection hret with hret'; injection hret' with hret''
                        exact ⟨len, hret''.symm, hlen_le⟩
                  have hwh_def : toBeMinWhile_hh =
                      .while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "len")))
                        (.dec (ofString "pos") .one
                          (.op .sub [.op .sub [.var .local (ofString "len"), .const 1#64], .var .local (ofString "i")])
                          (.decCall (ofString "l") .one (ofString "u256_limb")
                            [.var .local (ofString "a"), .shift .lsr (.var .local (ofString "pos")) (.const 3#64)]
                            (.seq
                              (.storeByte (.op .add [.var .local (ofString "out"), .var .local (ofString "i")])
                                (.op .and
                                  [.shift .lsr (.var .local (ofString "l"))
                                    (.panop .mul [.op .and [.var .local (ofString "pos"), .const 7#64], .const 8#64]),
                                   .const 255#64]))
                              (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1#64]))))) := rfl
                  rw [← hwh_def]
                  rcases hsq_eq : evaluateHOLFiniteState s2 (.seq toBeMinWhile_hh (.return (.var .local (ofString "len")))) with ⟨rsq, s4⟩
                  rw [hsq_eq] at hseq_run
                  dsimp only at hseq_run ⊢
                  exact ⟨(hs2_bf.trans hseq_run.1).locals _ |>.locals _, hseq_run.2.1, hseq_run.2.2⟩
                · exact ⟨hbf_bl, fun _ h => by simp at h, fun _ _ => by simp⟩
              | exception eid ev => exact absurd rfl (hno_exc_bl eid ev)
              | «break» | «continue» => exact ⟨hbf_bl, fun _ h => by simp at h, fun _ _ => by simp⟩
              | _ => exact ⟨hbf_bl.emptyLocals, fun _ h => by simp at h, fun _ _ => by simp⟩
    rcases htm : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_u256_to_be_min) with ⟨rtm, stm⟩
    rw [htm] at hbody_run hnt hres
    dsimp only at hbody_run hnt hres ⊢
    cases rtm with
    | none => exact False.elim (not_resumes_error hres)
    | some r =>
      cases r with
      | timeOut => exact absurd rfl hnt
      | exception eid ev => exact absurd rfl (hbody_run.2.2 eid ev)
      | «break» | «continue» | error => exact False.elim (not_resumes_error hres)
      | finalFfi _ =>
        rcases hres with ⟨_, hc⟩ | ⟨_, _, hc, _⟩ <;> simp at hc
      | returned rv =>
        obtain ⟨nw, rfl, hnw_le⟩ := hbody_run.2.1 rv rfl
        have hsh : (shapeEqHOL (shapeOfHOLExact (.val (.word nw) : ValueHOL 64)) .one &&
            shapeEqHOL (shapeOfHOLExact (.val (.word nw) : ValueHOL 64)) .one) = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        dsimp only at hnt hres ⊢
        rw [if_pos hsh] at hnt hres ⊢
        dsimp only at hnt hres ⊢
        let mid := setVarHOLFinite (ofString lname) (.val (.word nw)) { stm with locals := s.locals }
        have hbf_ent : M13.ByteFrame Rl s ent := by
          refine ⟨by cases s; rfl, fun _ h => False.elim (h rfl), fun _ _ h => False.elim (h rfl)⟩
        have hbf_mid : M13.ByteFrame Rl s mid :=
          ((hbf_ent.trans hbody_run.1).locals s.locals).setVar (ofString lname) (.val (.word nw))
        have heff_mid : HeapByteEff s mid Rl gw := byteFrame_to_heapByteEff hAR hbf_mid
        have hmid_g : mid.globals = s.globals := by rw [hbf_mid.1]
        exact ⟨nw, mid, hnw_le, hmid_g, rfl, heff_mid, hnt, hres, rfl⟩

private theorem eval_call_local_rlp_put_u256 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (lname : String) (dstExp vExp : ExpHOL 64)
    (dst0 w0 w1 w2 w3 : BitVec 64) (Rl : List Ivl) (gw : List String)
    (hcode : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hgw : "heap_ptr" ∈ gw)
    (hl_old : ∃ w_old : BitVec 64, s.locals.lookup (ofString lname) = some (.val (.word w_old)))
    (hdst : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dstExp =
      some (.val (.word dst0)))
    (hv : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) vExp =
      some (.rStruct [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3)]))
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ dst0.toNat ∧ dst0.toNat + 33 ≤ ivl.1 + ivl.2)
    (hnt : (evaluateHOLFiniteState s
      (.call (some (some (VarKind.local, ofString lname), none)) (ofString "rlp_put_u256")
        [dstExp, vExp])).1 ≠ some .timeOut) :
    let out := evaluateHOLFiniteState s
      (.call (some (some (VarKind.local, ofString lname), none)) (ofString "rlp_put_u256")
        [dstExp, vExp])
    (out.1 = none →
      ∃ len : BitVec 64,
        len.toNat ≤ 33 ∧ dst0.toNat < heapEnd ∧
        out.2.globals = s.globals ∧
        out.2.locals = s.locals.update (ofString lname, .val (.word len)) ∧
        HeapByteEff s out.2 Rl gw) ∧
    (out.1 ≠ none → ¬ Resumes out.1) := by
  intro out; dsimp only [out]
  obtain ⟨w_old, hw_old⟩ := hl_old
  let vval : ValueHOL 64 := .rStruct [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3)]
  rw [evaluateHOLFiniteState_call] at hnt ⊢
  have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [dstExp, vExp] = some [.val (.word dst0), vval] := by
    simp [evalListHOLFinite, evalListHOLExact, hdst, hv, vval]
  have hlk := pan_word_u256_lookup s.code.lookup (ofString "rlp_put_u256")
    (ofString "dst") (ofString "v")
    (sourceFnBody Guest.Software.guestFn_rlp_put_u256) dst0 w0 w1 w2 w3 (by decide)
    (by rw [hcode]; exact lookup_rlp_put_u256)
  dsimp only at hlk
  rw [ha] at hnt ⊢; dsimp only at hnt ⊢
  rw [hlk] at hnt ⊢; dsimp only at hnt ⊢
  by_cases hcz : s.clock = 0
  · simp [hcz] at hnt
  · simp only [hcz, ↓reduceIte] at hnt ⊢
    set cmap := (HolFiniteMapExact.empty.update (ofString "dst", ValueHOL.val (.word dst0))).update
      (ofString "v", vval)
    set ent := callEntryStateHOLFinite s cmap
    have hAR_ent : ArenaReady ent := ⟨guestInv_callEntry s cmap hAR.1, hAR.2⟩
    have hent_dst : ent.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "v" ≠ ofString "dst" by decide]
    have hent_v : ent.locals.lookup (ofString "v") = some vval := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hb : sourceFnBody Guest.Software.guestFn_rlp_put_u256 =
        .decCall (ofString "mark") .one (ofString "heap_mark") []
          (.decCall (ofString "tmp") .one (ofString "alloc") [.const 32]
            (.decCall (ofString "n") .one (ofString "u256_to_be_min")
              [.var .local (ofString "v"), .var .local (ofString "tmp")]
              (.decCall (ofString "w") .one (ofString "rlp_encode_bytes")
                [.var .local (ofString "dst"), .var .local (ofString "tmp"), .var .local (ofString "n")]
                (.seq (.call (some (none, none)) (ofString "heap_release") [.var .local (ofString "mark")])
                  (.return (.var .local (ofString "w"))))))) := rfl
    rcases hrun_eq : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_rlp_put_u256) with ⟨rpu, spu⟩
    have hnt_pu : rpu ≠ some .timeOut := by
      rintro rfl; simp [hrun_eq] at hnt
    have hbody : Resumes rpu →
        ∃ len : BitVec 64,
          rpu = some (.returned (.val (.word len))) ∧
          len.toNat ≤ 33 ∧ dst0.toNat < heapEnd ∧
          spu.globals = s.globals ∧
          HeapByteEff s spu Rl gw := by
      intro hres_pu
      have hnt_b : (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_rlp_put_u256)).1 ≠ some .timeOut := by
        rw [hrun_eq]; exact hnt_pu
      have hres_b : Resumes (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_rlp_put_u256)).1 := by
        rw [hrun_eq]; exact hres_pu
      have hrun := hrun_eq
      rw [hb] at hnt_b hres_b hrun
      obtain ⟨mark, p1, hhp_ent, hmark_nat, hp1_g, hp1_m, hp1_loc, heff01, hnt1, heq1⟩ :=
        eval_decCall_heap_mark ent "mark" _ Rl gw hcode hAR_ent hnt_b
      rw [heq1] at hres_b hrun; dsimp only at hres_b
      have hp1_mark : p1.locals.lookup (ofString "mark") = some (.val (.word mark)) := by
        rw [hp1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
      have hp1_dst : p1.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
        rw [hp1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hent_dst,
          show ofString "mark" ≠ ofString "dst" by decide]
      have hp1_v : p1.locals.lookup (ofString "v") = some vval := by
        rw [hp1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hent_v,
          show ofString "mark" ≠ ofString "v" by decide]
      obtain ⟨tmp, n32, q1, p2, h32_ev, htmp_hp, htmp8, hq1_nat, _, hq1_hi, hq1_8, hp2_hp, hp2_g, hp2_m, hp2_loc,
          heff12, hnt2, hres2, heq2⟩ :=
        eval_decCall_alloc_resumes p1 "tmp" (.const 32) _ Rl gw heff01.arena.1.code heff01.arena
          hgw hnt1 hres_b
      have hn32 : n32 = 32 := by simp [evalHOLExact] at h32_ev; exact h32_ev.symm
      subst hn32
      have h32_val : (32 : BitVec 64).toNat = 32 := by decide
      rw [h32_val] at hq1_nat
      have htmp_eq_mark : tmp.toNat = mark.toNat := by
        rw [htmp_hp, hmark_nat]; simp [globN, hp1_g]
      have hq1_eq : q1.toNat = tmp.toNat + 32 := by omega
      rw [heq2] at hrun
      let Rtmp : List Ivl := (tmp.toNat, 32) :: Rl
      have hp2_tmp : p2.locals.lookup (ofString "tmp") = some (.val (.word tmp)) := by
        rw [hp2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
      have hp2_mark : p2.locals.lookup (ofString "mark") = some (.val (.word mark)) := by
        rw [hp2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hp1_mark,
          show ofString "tmp" ≠ ofString "mark" by decide]
      have hp2_dst : p2.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
        rw [hp2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hp1_dst,
          show ofString "tmp" ≠ ofString "dst" by decide]
      have hp2_v : p2.locals.lookup (ofString "v") = some vval := by
        rw [hp2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hp1_v,
          show ofString "tmp" ≠ ofString "v" by decide]
      obtain ⟨nw, p3, hnw_le, hp3_g, hp3_loc, heff23, hnt3, hres3, heq3⟩ :=
        eval_decCall_u256_to_be_min p2 "n" (.var .local (ofString "v")) (.var .local (ofString "tmp"))
          w0 w1 w2 w3 tmp _ Rtmp gw heff12.arena.1.code heff12.arena hp2_v hp2_tmp
          List.mem_cons_self hnt2 hres2
      rw [heq3] at hrun
      have hp3_n : p3.locals.lookup (ofString "n") = some (.val (.word nw)) := by
        rw [hp3_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
      have hp3_tmp : p3.locals.lookup (ofString "tmp") = some (.val (.word tmp)) := by
        rw [hp3_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hp2_tmp,
          show ofString "n" ≠ ofString "tmp" by decide]
      have hp3_mark : p3.locals.lookup (ofString "mark") = some (.val (.word mark)) := by
        rw [hp3_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hp2_mark,
          show ofString "n" ≠ ofString "mark" by decide]
      have hp3_dst : p3.locals.lookup (ofString "dst") = some (.val (.word dst0)) := by
        rw [hp3_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hp2_dst,
          show ofString "n" ≠ ofString "dst" by decide]
      have hhl_nw : rlpHeaderLenPure nw.toNat = 1 := rlpHeaderLenPure_of_le55 (by omega)
      obtain ⟨ivl0, hivl0, hivl_lo, hivl_hi⟩ := hin_ivl
      obtain ⟨len, p4, hlen_le', hdst_lt, hp4_g, hp4_loc, heff34, hnt4, hres4, heq4⟩ :=
        eval_decCall_rlp_encode_bytes p3 "w"
          (.var .local (ofString "dst")) (.var .local (ofString "tmp")) (.var .local (ofString "n"))
          dst0 tmp nw _ Rtmp gw heff23.arena.1.code heff23.arena hp3_dst hp3_tmp hp3_n
          ⟨ivl0, List.mem_cons_of_mem _ hivl0, hivl_lo, by omega⟩ hnt3 hres3
      have hlen_le : len.toNat ≤ 33 := by omega
      rw [heq4] at hrun
      have hp4_w : p4.locals.lookup (ofString "w") = some (.val (.word len)) := by
        rw [hp4_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
      have hp4_mark : p4.locals.lookup (ofString "mark") = some (.val (.word mark)) := by
        rw [hp4_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hp3_mark,
          show ofString "w" ≠ ofString "mark" by decide]
      have heff_s_ent : HeapByteEff s ent Rtmp gw :=
        (HeapByteEff.refl hAR Rtmp gw).locals_clock ent.locals ent.clock
      have heff_s_p4 : HeapByteEff s p4 Rtmp gw :=
        (((heff_s_ent.trans (heff01.mono (fun i hi _ => Or.inl ⟨i, List.mem_cons_of_mem _ hi, le_rfl, le_rfl⟩) (fun _ hg => hg))).trans
          (heff12.mono (fun i hi _ => Or.inl ⟨i, List.mem_cons_of_mem _ hi, le_rfl, le_rfl⟩) (fun _ hg => hg))).trans
          heff23).trans heff34
      rw [evaluateHOLFiniteState_seq_line780] at hnt4 hres4 hrun
      rcases hrel : evaluateHOLFiniteState p4
          (.call (some (none, none)) (ofString "heap_release") [.var .local (ofString "mark")]) with ⟨r5, p5⟩
      have hnt_rel : r5 ≠ some .timeOut := by
        rintro rfl; rw [hrel] at hnt4; exact hnt4 rfl
      have h5 := eval_call_heap_release p4 (.var .local (ofString "mark")) mark Rtmp gw
        heff34.arena.1.code heff_s_p4 hgw hp4_mark
        (by rw [hmark_nat]; rfl) (by rw [hmark_nat]; exact hAR.2.1)
        (by rw [hmark_nat]; exact hAR.2.2.1)
        (by rw [hmark_nat]; exact hAR.2.2.2.2.2.2.1) (by rw [hrel]; exact hnt_rel)
      dsimp only at h5
      rw [hrel] at h5 hnt4 hres4 hrun
      obtain ⟨rfl, hp5_loc, hp5_g, _, heff_s_p5⟩ := h5
      dsimp only at hrun
      have hp5_w : p5.locals.lookup (ofString "w") = some (.val (.word len)) := by
        rw [hp5_loc]; exact hp4_w
      have hret_eval : evaluateHOLFiniteState p5 (.return (.var .local (ofString "w"))) =
          (some (.returned (.val (.word len))), p5.emptyLocalsHOLFinite) := by
        rw [evaluateHOLFiniteState_return]
        have hev_w : @evalHOLExact 64 F _ p5.toExact (fun a => Classical.propDecidable (p5.memaddrs a))
            (.var .local (ofString "w")) = some (.val (.word len)) := hp5_w
        rw [hev_w]; simp [shapeOfHOLExact]
      rw [hret_eval] at hrun
      dsimp only at hrun
      injection hrun with hr_eq hs_eq
      have hp5_g_eq : p5.globals = s.globals := by
        rw [hp5_g, hp4_g, hp3_g, hp2_g, hp1_g]
        have hent_g : ent.globals = s.globals := rfl
        rw [hent_g]
        apply HolFiniteMapExact.ext
        funext k
        by_cases hk : k = ofString "heap_ptr"
        · subst hk; simp [HolFiniteMapExact.lookup_update, FUPDATE]; exact hhp_ent.symm
        · simp [HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk]
      have hspu_g : spu.globals = s.globals := by
        rw [← hs_eq]; exact hp5_g_eq
      have heff_ret : HeapByteEff p5 p5.emptyLocalsHOLFinite Rtmp gw :=
        (HeapByteEff.refl heff_s_p5.arena Rtmp gw).locals_clock _ _
      have heff_spu_tmp : HeapByteEff s spu Rtmp gw := by
        rw [← hs_eq]
        exact ((((heff_s_p5.trans heff_ret).locals_clock _ _).locals_clock _ _).locals_clock _ _).locals_clock _ _
      have heff_spu : HeapByteEff s spu Rl gw :=
        heff_spu_tmp.mono
          (fun i hi _ => by
            simp only [Rtmp, List.mem_cons] at hi
            rcases hi with rfl | hi_rl
            · exact Or.inr (Or.inr ⟨by rw [htmp_eq_mark, hmark_nat]; rfl, by omega⟩)
            · exact Or.inl ⟨i, hi_rl, le_rfl, le_rfl⟩)
          (fun _ hg => hg)
      exact ⟨len, hr_eq.symm, hlen_le, hdst_lt, hspu_g, heff_spu⟩
    cases rpu with
    | none => exact ⟨fun h => by simp at h, fun _ => not_resumes_error⟩
    | some r =>
      cases r with
      | timeOut => exact absurd rfl hnt_pu
      | exception eid ev =>
        refine ⟨fun h => by simp at h, fun _ hres_out => ?_⟩
        dsimp only at hres_out
        have hres_pu : Resumes (some (.exception eid ev)) := by
          rcases hres_out with ⟨_, hc⟩ | ⟨e', v', hc, hne⟩
          · simp at hc
          · injection hc with hc'; injection hc' with he1 he2; subst he1 he2
            exact Or.inr ⟨eid, ev, rfl, hne⟩
        obtain ⟨_, hcontra, _⟩ := hbody hres_pu
        simp at hcontra
      | returned rv =>
        obtain ⟨len, hrv_eq, hlen_le, hdst_lt, hspu_g, heff_spu⟩ := hbody (Or.inl ⟨rv, rfl⟩)
        injection hrv_eq with hrv_eq'; injection hrv_eq' with hrv_eq''; subst hrv_eq''
        have hsh : shapeEqHOL (shapeOfHOLExact (.val (.word len) : ValueHOL 64)) .one = true := by
          simp [shapeOfHOLExact, shapeEqHOL]
        have hval : isValidValueHOLExact s.toExact VarKind.local (ofString lname) (.val (.word len)) = true := by
          simp [isValidValueHOLExact, lookupKvarHOLExact, hw_old, shapeOfHOLExact, shapeEqHOL]
        dsimp only
        rw [if_pos hsh]
        rw [if_pos hval]
        let mid := setVarHOLFinite (ofString lname) (.val (.word len)) { spu with locals := s.locals }
        exact ⟨fun _ => ⟨len, hlen_le, hdst_lt, hspu_g, rfl,
          (heff_spu.locals_clock s.locals spu.clock).locals_clock mid.locals mid.clock⟩,
          fun h => False.elim (h rfl)⟩
      | «break» | «continue» | error =>
        exact ⟨fun h => by simp at h, fun _ => not_resumes_error⟩
      | finalFfi _ =>
        exact ⟨fun h => by simp at h, fun _ hr => by rcases hr with ⟨_, hc⟩ | ⟨_, _, hc, _⟩ <;> simp at hc⟩

private theorem ivlUnhit_of_heapByteEff_below_hp {F : Type}
    {s0 st : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {gw : List String}
    (hAR0 : ArenaReady s0)
    (heff : HeapByteEff s0 st Rl gw)
    {h len : Nat} (hh_ins : Inside (h, len) sourceBase (globN s0 "heap_ptr"))
    (hRl_ge : ∀ i ∈ Rl, 0 < i.2 → globN s0 "heap_ptr" ≤ i.1) :
    IvlUnhit s0 st (h, len) := by
  intro a ha8 hhit
  obtain ⟨ha_lo, ha_hi⟩ := hhit
  dsimp only at ha_lo ha_hi
  obtain ⟨hh_lo, hh_hi⟩ := hh_ins
  dsimp only at hh_lo hh_hi
  by_contra hne
  have hsep : heapLimit = scratchStart := rfl
  have hhp8 : globN s0 "heap_ptr" % 8 = 0 := hAR0.2.2.2.2.2.2.1
  have hfp8 : globN s0 "frame_mem_ptr" % 8 = 0 := hAR0.2.2.2.2.2.2.2.1
  have hhp_hi : globN s0 "heap_ptr" ≤ heapLimit := hAR0.2.2.1
  have hfp_lo : scratchStart ≤ globN s0 "frame_mem_ptr" := hAR0.2.2.2.1
  rcases heff.cell_frame a hne with ⟨i, hi, hipos, hc1, hc2⟩ | ⟨_, g1, _⟩ | ⟨_, f1, _⟩
  · have := hRl_ge i hi hipos
    omega
  · unfold freeGap at g1
    dsimp only at g1
    omega
  · unfold heapFree at f1
    dsimp only at f1
    omega

private theorem eval_load_header_word {F : Type}
    {s0 st : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {gw : List String}
    (hAR0 : ArenaReady s0)
    (heff : HeapByteEff s0 st Rl gw)
    {hw : BitVec 64} (hH0 : HeaderAtStrong s0 hw.toNat)
    (hRl_ge : ∀ i ∈ Rl, 0 < i.2 → globN s0 "heap_ptr" ≤ i.1)
    (hst_h : st.locals.lookup (ofString "h") = some (.val (.word hw)))
    (off : Nat) (hoff8 : off % 8 = 0) (hoff_hi : off + 8 ≤ 248) :
    @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a))
      (.load .one (.op .add [.var .local (ofString "h"), .const (BitVec.ofNat 64 off)])) =
      some (.val (.word (BitVec.ofNat 64 (memW s0 (hw.toNat + off))))) := by
  have hhl264 : heapLimit < 2 ^ 64 := by decide
  have hh_bound : hw.toNat + 248 ≤ 2 ^ 64 := by
    have := hAR0.2.2.1; obtain ⟨_, hh_hi⟩ := hH0.2; dsimp only at hh_hi; omega
  have hu : IvlUnhit s0 st (hw.toNat, 248) :=
    ivlUnhit_of_heapByteEff_below_hp hAR0 heff hH0.2 hRl_ge
  have hH_st : HeaderAt st hw.toNat :=
    headerAt_of_ivlUnhit hAR0.1 heff.arena.1 hh_bound hu hH0.1
  have hk : off / 8 < 248 / 8 := by omega
  have hwa : WordAt st (hw.toNat + off) := by
    have h := hH_st.1.2.2 (off / 8) hk
    have heq : hw.toNat + 8 * (off / 8) = hw.toNat + off := by omega
    rwa [heq] at h
  obtain ⟨w, hdom, hmem⟩ := hwa
  have hlt : hw.toNat + off < 2 ^ 64 := by omega
  have hadd : hw + BitVec.ofNat 64 off = BitVec.ofNat 64 (hw.toNat + off) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have hmw_st : memW st (hw.toNat + off) = memW s0 (hw.toNat + off) :=
    R10Shards.Fast_GbodyC17ToC21.memW_eq_of_ivlUnhit hu
      (by have := hH0.1.1.1; omega) hh_bound ⟨by omega, by omega⟩
  have hmw : BitVec.ofNat 64 (memW s0 (hw.toNat + off)) = w := by
    rw [← hmw_st]; unfold memW; rw [hmem]; simp
  simp [evalHOLExact, evalListHOLExact, hst_h, valueIsWord, valueWord, wordOpHOL, wordOp,
    isWfShapeExactHOL, memLoadHOLExact, hadd, hdom, hmem, hmw]

private theorem eval_load_header_u256 {F : Type}
    {s0 st : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {gw : List String}
    (hAR0 : ArenaReady s0)
    (heff : HeapByteEff s0 st Rl gw)
    {hw : BitVec 64} (hH0 : HeaderAtStrong s0 hw.toNat)
    (hRl_ge : ∀ i ∈ Rl, 0 < i.2 → globN s0 "heap_ptr" ≤ i.1)
    (hst_h : st.locals.lookup (ofString "h") = some (.val (.word hw)))
    (off : Nat) (hoff8 : off % 8 = 0) (hoff_hi : off + 32 ≤ 248) :
    ∃ w0 w1 w2 w3 : BitVec 64,
      @evalHOLExact 64 F _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a))
        (.load (.comb [.one, .one, .one, .one])
          (.op .add [.var .local (ofString "h"), .const (BitVec.ofNat 64 off)])) =
        some (.rStruct [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3)]) := by
  have hhl264 : heapLimit < 2 ^ 64 := by decide
  have hh_bound : hw.toNat + 248 ≤ 2 ^ 64 := by
    have := hAR0.2.2.1; obtain ⟨_, hh_hi⟩ := hH0.2; dsimp only at hh_hi; omega
  have hu : IvlUnhit s0 st (hw.toNat, 248) :=
    ivlUnhit_of_heapByteEff_below_hp hAR0 heff hH0.2 hRl_ge
  have hH_st : HeaderAt st hw.toNat :=
    headerAt_of_ivlUnhit hAR0.1 heff.arena.1 hh_bound hu hH0.1
  have hwa_at : ∀ j : Nat, j < 4 → WordAt st (hw.toNat + off + 8 * j) := by
    intro j hj
    have hk : (off + 8 * j) / 8 < 248 / 8 := by omega
    have h := hH_st.1.2.2 ((off + 8 * j) / 8) hk
    have heq : hw.toNat + 8 * ((off + 8 * j) / 8) = hw.toNat + off + 8 * j := by omega
    rwa [heq] at h
  obtain ⟨w0, hdom0, hmem0⟩ := hwa_at 0 (by omega)
  obtain ⟨w1, hdom1, hmem1⟩ := hwa_at 1 (by omega)
  obtain ⟨w2, hdom2, hmem2⟩ := hwa_at 2 (by omega)
  obtain ⟨w3, hdom3, hmem3⟩ := hwa_at 3 (by omega)
  let base : BitVec 64 := BitVec.ofNat 64 (hw.toNat + off)
  have hadd : hw + BitVec.ofNat 64 off = base := by
    apply BitVec.eq_of_toNat_eq
    simp only [base, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have hb8 : base + 8#64 = BitVec.ofNat 64 (hw.toNat + off + 8) := by
    apply BitVec.eq_of_toNat_eq
    simp only [base, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have hb16 : base + 16#64 = BitVec.ofNat 64 (hw.toNat + off + 16) := by
    apply BitVec.eq_of_toNat_eq
    simp only [base, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have hb24 : base + 24#64 = BitVec.ofNat 64 (hw.toNat + off + 24) := by
    apply BitVec.eq_of_toNat_eq
    simp only [base, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have hd0 : st.memaddrs base := by simpa [base] using hdom0
  have hd1 : st.memaddrs (base + 8#64) := by rw [hb8]; simpa using hdom1
  have hd2 : st.memaddrs (base + 16#64) := by rw [hb16]; simpa using hdom2
  have hd3 : st.memaddrs (base + 24#64) := by rw [hb24]; simpa using hdom3
  have hv0 : st.memory base = .word w0 := by simpa [base] using hmem0
  have hv1 : st.memory (base + 8#64) = .word w1 := by rw [hb8]; simpa using hmem1
  have hv2 : st.memory (base + 16#64) = .word w2 := by rw [hb16]; simpa using hmem2
  have hv3 : st.memory (base + 24#64) = .word w3 := by rw [hb24]; simpa using hmem3
  refine ⟨w0, w1, w2, w3, ?_⟩
  simp [evalHOLExact, evalListHOLExact, hst_h, valueIsWord, valueWord, wordOpHOL, wordOp,
    isWfShapeExactHOL, memLoadHOLExact, memLoadsHOLExact, sizeOfShapeWithContextHOL,
    bytesInWordHOL, BitVec.add_assoc, hadd, hd0, hd1, hd2, hd3, hv0, hv1, hv2, hv3]

/-! ## Section 5: Sequential field steppers for `encode_header` -/

private theorem step_enc_bytes_const {F : Type}
    {s0 st : PanSemStateFiniteExact 64 F}
    {hw buf p_cur w_prev : BitVec 64} {Rl : List Ivl} {gw : List String}
    (hAR0 : ArenaReady s0)
    (heff : HeapByteEff s0 st Rl gw)
    (hH0 : HeaderAtStrong s0 hw.toNat)
    (hRl_ge : ∀ i ∈ Rl, 0 < i.2 → globN s0 "heap_ptr" ≤ i.1)
    (hst_h : st.locals.lookup (ofString "h") = some (.val (.word hw)))
    (hst_buf : st.locals.lookup (ofString "buf") = some (.val (.word buf)))
    (hst_p : st.locals.lookup (ofString "p") = some (.val (.word p_cur)))
    (hst_w : st.locals.lookup (ofString "w") = some (.val (.word w_prev)))
    (off n : Nat) (hoff8 : off % 8 = 0) (hoff_hi : off + 8 ≤ 248) (hn_lt : n < 2 ^ 64)
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ p_cur.toNat ∧
      p_cur.toNat + rlpHeaderLenPure n + n ≤ ivl.1 + ivl.2)
    (hp_add_lt : p_cur.toNat + rlpHeaderLenPure n + n < 2 ^ 64)
    (rest : ProgHOL 64)
    (hnt : (evaluateHOLFiniteState st
      (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_bytes")
          [.var .local (ofString "p"),
           .load .one (.op .add [.var .local (ofString "h"), .const (BitVec.ofNat 64 off)]),
           .const (BitVec.ofNat 64 n)])
        (.seq (.assign .local (ofString "p") (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
          rest))).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState st
      (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_bytes")
          [.var .local (ofString "p"),
           .load .one (.op .add [.var .local (ofString "h"), .const (BitVec.ofNat 64 off)]),
           .const (BitVec.ofNat 64 n)])
        (.seq (.assign .local (ofString "p") (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
          rest))).1) :
    ∃ (p_next w_next : BitVec 64) (st' : PanSemStateFiniteExact 64 F),
      p_cur.toNat ≤ p_next.toNat ∧
      p_next.toNat ≤ p_cur.toNat + rlpHeaderLenPure n + n ∧
      HeapByteEff s0 st' Rl gw ∧
      st'.locals.lookup (ofString "h") = some (.val (.word hw)) ∧
      st'.locals.lookup (ofString "buf") = some (.val (.word buf)) ∧
      st'.locals.lookup (ofString "p") = some (.val (.word p_next)) ∧
      st'.locals.lookup (ofString "w") = some (.val (.word w_next)) ∧
      (evaluateHOLFiniteState st' rest).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState st' rest).1 ∧
      evaluateHOLFiniteState st
        (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_bytes")
            [.var .local (ofString "p"),
             .load .one (.op .add [.var .local (ofString "h"), .const (BitVec.ofNat 64 off)]),
             .const (BitVec.ofNat 64 n)])
          (.seq (.assign .local (ofString "p") (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
            rest)) =
        evaluateHOLFiniteState st' rest := by
  have hev_src := eval_load_header_word hAR0 heff hH0 hRl_ge hst_h off hoff8 hoff_hi
  have hn_nat : (BitVec.ofNat 64 n).toNat = n := Nat.mod_eq_of_lt hn_lt
  rw [evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
  rcases hc : evaluateHOLFiniteState st
    (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_bytes")
      [.var .local (ofString "p"),
       .load .one (.op .add [.var .local (ofString "h"), .const (BitVec.ofNat 64 off)]),
       .const (BitVec.ofNat 64 n)]) with ⟨rc, sc⟩
  have hnt_c : rc ≠ some .timeOut := by rintro rfl; simp [hc] at hnt
  have hc_prop := eval_call_local_rlp_encode_bytes st "w"
    (.var .local (ofString "p"))
    (.load .one (.op .add [.var .local (ofString "h"), .const (BitVec.ofNat 64 off)]))
    (.const (BitVec.ofNat 64 n))
    p_cur (BitVec.ofNat 64 (memW s0 (hw.toNat + off))) (BitVec.ofNat 64 n)
    Rl [] heff.arena.1.code heff.arena ⟨w_prev, hst_w⟩
    hst_p hev_src rfl (by rwa [hn_nat]) (by rw [hc]; exact hnt_c)
  dsimp only at hc_prop
  rw [hc] at hc_prop
  simp only [hc] at hnt hres ⊢
  cases rc with
  | some rc0 =>
    exfalso
    exact hc_prop.2 (by simp) hres
  | none =>
    dsimp only at hnt hres ⊢
    obtain ⟨w_next, hw_le, _, _, hsc_loc, heff_sc⟩ := hc_prop.1 rfl
    rw [hn_nat] at hw_le
    have hsc_w : sc.locals.lookup (ofString "w") = some (.val (.word w_next)) := by
      rw [hsc_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
    have hsc_p : sc.locals.lookup (ofString "p") = some (.val (.word p_cur)) := by
      rw [hsc_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hst_p,
        show ofString "w" ≠ ofString "p" by decide]
    have hsc_buf : sc.locals.lookup (ofString "buf") = some (.val (.word buf)) := by
      rw [hsc_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hst_buf,
        show ofString "w" ≠ ofString "buf" by decide]
    have hsc_h : sc.locals.lookup (ofString "h") = some (.val (.word hw)) := by
      rw [hsc_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hst_h,
        show ofString "w" ≠ ofString "h" by decide]
    let p_next : BitVec 64 := p_cur + w_next
    have hp_next_nat : p_next.toNat = p_cur.toNat + w_next.toNat := by
      change (p_cur + w_next).toNat = p_cur.toNat + w_next.toNat
      rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
    have hass : evaluateHOLFiniteState sc
        (.assign .local (ofString "p") (.op .add [.var .local (ofString "p"), .var .local (ofString "w")])) =
        (none, setVarHOLFinite (ofString "p") (.val (.word p_next)) sc) := by
      rw [evaluateHOLFiniteState_assign]
      have hev : @evalHOLExact 64 F _ sc.toExact (fun a => Classical.propDecidable (sc.memaddrs a))
          (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]) = some (.val (.word p_next)) := by
        simp [evalHOLExact, evalListHOLExact, hsc_p, hsc_w, wordOpHOL, wordOp, valueIsWord, valueWord, p_next]
      have hval : sc.isValidValueHOLFinite .local (ofString "p") (.val (.word p_next)) = true := by
        simp [PanSemStateFiniteExact.isValidValueHOLFinite, lookupKvarHOLExact, hsc_p, shapeOfHOLExact, shapeEqHOL]
      rw [hev]; dsimp only; rw [if_pos hval]; rfl
    rw [evaluateHOLFiniteState_seq_line780, hass] at hnt hres ⊢
    dsimp only at hnt hres ⊢
    set st' := setVarHOLFinite (ofString "p") (.val (.word p_next)) sc
    have heff_st' : HeapByteEff s0 st' Rl gw := by
      have hm : HeapByteEff st sc Rl gw :=
        heff_sc.mono (fun i hi _ => Or.inl ⟨i, hi, le_rfl, le_rfl⟩) (fun _ h => by cases h)
      exact (heff.trans hm).locals_clock st'.locals st'.clock
    refine ⟨p_next, w_next, st', by omega, by omega, heff_st', ?_, ?_, ?_, ?_, hnt, hres, rfl⟩
    · simp [st', setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsc_h,
        show ofString "p" ≠ ofString "h" by decide]
    · simp [st', setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsc_buf,
        show ofString "p" ≠ ofString "buf" by decide]
    · simp [st', setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    · simp [st', setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsc_w,
        show ofString "p" ≠ ofString "w" by decide]

private theorem step_enc_word {F : Type}
    {s0 st : PanSemStateFiniteExact 64 F}
    {hw buf p_cur w_prev : BitVec 64} {Rl : List Ivl} {gw : List String}
    (hAR0 : ArenaReady s0)
    (heff : HeapByteEff s0 st Rl gw)
    (hH0 : HeaderAtStrong s0 hw.toNat)
    (hRl_ge : ∀ i ∈ Rl, 0 < i.2 → globN s0 "heap_ptr" ≤ i.1)
    (hst_h : st.locals.lookup (ofString "h") = some (.val (.word hw)))
    (hst_buf : st.locals.lookup (ofString "buf") = some (.val (.word buf)))
    (hst_p : st.locals.lookup (ofString "p") = some (.val (.word p_cur)))
    (hst_w : st.locals.lookup (ofString "w") = some (.val (.word w_prev)))
    (off : Nat) (hoff8 : off % 8 = 0) (hoff_hi : off + 8 ≤ 248)
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ p_cur.toNat ∧ p_cur.toNat + 9 ≤ ivl.1 + ivl.2)
    (hp_add_lt : p_cur.toNat + 9 < 2 ^ 64)
    (rest : ProgHOL 64)
    (hnt : (evaluateHOLFiniteState st
      (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_word")
          [.var .local (ofString "p"),
           .load .one (.op .add [.var .local (ofString "h"), .const (BitVec.ofNat 64 off)])])
        (.seq (.assign .local (ofString "p") (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
          rest))).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState st
      (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_word")
          [.var .local (ofString "p"),
           .load .one (.op .add [.var .local (ofString "h"), .const (BitVec.ofNat 64 off)])])
        (.seq (.assign .local (ofString "p") (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
          rest))).1) :
    ∃ (p_next w_next : BitVec 64) (st' : PanSemStateFiniteExact 64 F),
      p_cur.toNat ≤ p_next.toNat ∧
      p_next.toNat ≤ p_cur.toNat + 9 ∧
      HeapByteEff s0 st' Rl gw ∧
      st'.locals.lookup (ofString "h") = some (.val (.word hw)) ∧
      st'.locals.lookup (ofString "buf") = some (.val (.word buf)) ∧
      st'.locals.lookup (ofString "p") = some (.val (.word p_next)) ∧
      st'.locals.lookup (ofString "w") = some (.val (.word w_next)) ∧
      (evaluateHOLFiniteState st' rest).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState st' rest).1 ∧
      evaluateHOLFiniteState st
        (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_word")
            [.var .local (ofString "p"),
             .load .one (.op .add [.var .local (ofString "h"), .const (BitVec.ofNat 64 off)])])
          (.seq (.assign .local (ofString "p") (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
            rest)) =
        evaluateHOLFiniteState st' rest := by
  have hev_v := eval_load_header_word hAR0 heff hH0 hRl_ge hst_h off hoff8 hoff_hi
  rw [evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
  rcases hc : evaluateHOLFiniteState st
    (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_word")
      [.var .local (ofString "p"),
       .load .one (.op .add [.var .local (ofString "h"), .const (BitVec.ofNat 64 off)])]) with ⟨rc, sc⟩
  have hnt_c : rc ≠ some .timeOut := by rintro rfl; simp [hc] at hnt
  have hc_prop := eval_call_local_rlp_encode_word st "w"
    (.var .local (ofString "p"))
    (.load .one (.op .add [.var .local (ofString "h"), .const (BitVec.ofNat 64 off)]))
    p_cur (BitVec.ofNat 64 (memW s0 (hw.toNat + off)))
    Rl [] heff.arena.1.code heff.arena ⟨w_prev, hst_w⟩
    hst_p hev_v hin_ivl (by rw [hc]; exact hnt_c)
  dsimp only at hc_prop
  rw [hc] at hc_prop
  simp only [hc] at hnt hres ⊢
  cases rc with
  | some rc0 =>
    exfalso
    exact hc_prop.2 (by simp) hres
  | none =>
    dsimp only at hnt hres ⊢
    obtain ⟨w_next, _, hw_le, _, _, hsc_loc, heff_sc⟩ := hc_prop.1 rfl
    have hsc_w : sc.locals.lookup (ofString "w") = some (.val (.word w_next)) := by
      rw [hsc_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
    have hsc_p : sc.locals.lookup (ofString "p") = some (.val (.word p_cur)) := by
      rw [hsc_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hst_p,
        show ofString "w" ≠ ofString "p" by decide]
    have hsc_buf : sc.locals.lookup (ofString "buf") = some (.val (.word buf)) := by
      rw [hsc_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hst_buf,
        show ofString "w" ≠ ofString "buf" by decide]
    have hsc_h : sc.locals.lookup (ofString "h") = some (.val (.word hw)) := by
      rw [hsc_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hst_h,
        show ofString "w" ≠ ofString "h" by decide]
    let p_next : BitVec 64 := p_cur + w_next
    have hp_next_nat : p_next.toNat = p_cur.toNat + w_next.toNat := by
      change (p_cur + w_next).toNat = p_cur.toNat + w_next.toNat
      rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
    have hass : evaluateHOLFiniteState sc
        (.assign .local (ofString "p") (.op .add [.var .local (ofString "p"), .var .local (ofString "w")])) =
        (none, setVarHOLFinite (ofString "p") (.val (.word p_next)) sc) := by
      rw [evaluateHOLFiniteState_assign]
      have hev : @evalHOLExact 64 F _ sc.toExact (fun a => Classical.propDecidable (sc.memaddrs a))
          (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]) = some (.val (.word p_next)) := by
        simp [evalHOLExact, evalListHOLExact, hsc_p, hsc_w, wordOpHOL, wordOp, valueIsWord, valueWord, p_next]
      have hval : sc.isValidValueHOLFinite .local (ofString "p") (.val (.word p_next)) = true := by
        simp [PanSemStateFiniteExact.isValidValueHOLFinite, lookupKvarHOLExact, hsc_p, shapeOfHOLExact, shapeEqHOL]
      rw [hev]; dsimp only; rw [if_pos hval]; rfl
    rw [evaluateHOLFiniteState_seq_line780, hass] at hnt hres ⊢
    dsimp only at hnt hres ⊢
    set st' := setVarHOLFinite (ofString "p") (.val (.word p_next)) sc
    have heff_st' : HeapByteEff s0 st' Rl gw := by
      have hm : HeapByteEff st sc Rl gw :=
        heff_sc.mono (fun i hi _ => Or.inl ⟨i, hi, le_rfl, le_rfl⟩) (fun _ h => by cases h)
      exact (heff.trans hm).locals_clock st'.locals st'.clock
    refine ⟨p_next, w_next, st', by omega, by omega, heff_st', ?_, ?_, ?_, ?_, hnt, hres, rfl⟩
    · simp [st', setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsc_h,
        show ofString "p" ≠ ofString "h" by decide]
    · simp [st', setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsc_buf,
        show ofString "p" ≠ ofString "buf" by decide]
    · simp [st', setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    · simp [st', setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsc_w,
        show ofString "p" ≠ ofString "w" by decide]

private theorem step_enc_word_tail {F : Type}
    {s0 st : PanSemStateFiniteExact 64 F}
    {hw buf p_cur w_prev : BitVec 64} {Rl : List Ivl} {gw : List String}
    (hAR0 : ArenaReady s0)
    (heff : HeapByteEff s0 st Rl gw)
    (hH0 : HeaderAtStrong s0 hw.toNat)
    (hRl_ge : ∀ i ∈ Rl, 0 < i.2 → globN s0 "heap_ptr" ≤ i.1)
    (hst_h : st.locals.lookup (ofString "h") = some (.val (.word hw)))
    (hst_buf : st.locals.lookup (ofString "buf") = some (.val (.word buf)))
    (hst_p : st.locals.lookup (ofString "p") = some (.val (.word p_cur)))
    (hst_w : st.locals.lookup (ofString "w") = some (.val (.word w_prev)))
    (off : Nat) (hoff8 : off % 8 = 0) (hoff_hi : off + 8 ≤ 248)
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ p_cur.toNat ∧ p_cur.toNat + 9 ≤ ivl.1 + ivl.2)
    (hp_add_lt : p_cur.toNat + 9 < 2 ^ 64)
    (hnt : (evaluateHOLFiniteState st
      (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_word")
          [.var .local (ofString "p"),
           .load .one (.op .add [.var .local (ofString "h"), .const (BitVec.ofNat 64 off)])])
        (.assign .local (ofString "p") (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
      )).1 ≠ some .timeOut) :
    let out := evaluateHOLFiniteState st
      (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_word")
          [.var .local (ofString "p"),
           .load .one (.op .add [.var .local (ofString "h"), .const (BitVec.ofNat 64 off)])])
        (.assign .local (ofString "p") (.op .add [.var .local (ofString "p"), .var .local (ofString "w")])))
    (out.1 = none →
      ∃ (p_next w_next : BitVec 64),
        p_cur.toNat ≤ p_next.toNat ∧
        p_next.toNat ≤ p_cur.toNat + 9 ∧
        HeapByteEff s0 out.2 Rl gw ∧
        out.2.locals.lookup (ofString "h") = some (.val (.word hw)) ∧
        out.2.locals.lookup (ofString "buf") = some (.val (.word buf)) ∧
        out.2.locals.lookup (ofString "p") = some (.val (.word p_next)) ∧
        out.2.locals.lookup (ofString "w") = some (.val (.word w_next))) ∧
    (out.1 ≠ none → ¬ Resumes out.1) := by
  intro out; dsimp only [out]
  have hev_v := eval_load_header_word hAR0 heff hH0 hRl_ge hst_h off hoff8 hoff_hi
  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
  rcases hc : evaluateHOLFiniteState st
    (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_word")
      [.var .local (ofString "p"),
       .load .one (.op .add [.var .local (ofString "h"), .const (BitVec.ofNat 64 off)])]) with ⟨rc, sc⟩
  have hnt_c : rc ≠ some .timeOut := by rintro rfl; simp [hc] at hnt
  have hc_prop := eval_call_local_rlp_encode_word st "w"
    (.var .local (ofString "p"))
    (.load .one (.op .add [.var .local (ofString "h"), .const (BitVec.ofNat 64 off)]))
    p_cur (BitVec.ofNat 64 (memW s0 (hw.toNat + off)))
    Rl [] heff.arena.1.code heff.arena ⟨w_prev, hst_w⟩
    hst_p hev_v hin_ivl (by rw [hc]; exact hnt_c)
  dsimp only at hc_prop
  rw [hc] at hc_prop
  simp only [hc] at hnt ⊢
  cases rc with
  | some rc0 =>
    dsimp only
    exact ⟨fun h => by simp at h, fun _ => hc_prop.2 (by simp)⟩
  | none =>
    dsimp only at hnt ⊢
    obtain ⟨w_next, _, hw_le, _, _, hsc_loc, heff_sc⟩ := hc_prop.1 rfl
    have hsc_w : sc.locals.lookup (ofString "w") = some (.val (.word w_next)) := by
      rw [hsc_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
    have hsc_p : sc.locals.lookup (ofString "p") = some (.val (.word p_cur)) := by
      rw [hsc_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hst_p,
        show ofString "w" ≠ ofString "p" by decide]
    have hsc_buf : sc.locals.lookup (ofString "buf") = some (.val (.word buf)) := by
      rw [hsc_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hst_buf,
        show ofString "w" ≠ ofString "buf" by decide]
    have hsc_h : sc.locals.lookup (ofString "h") = some (.val (.word hw)) := by
      rw [hsc_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hst_h,
        show ofString "w" ≠ ofString "h" by decide]
    let p_next : BitVec 64 := p_cur + w_next
    have hp_next_nat : p_next.toNat = p_cur.toNat + w_next.toNat := by
      change (p_cur + w_next).toNat = p_cur.toNat + w_next.toNat
      rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
    have hass : evaluateHOLFiniteState sc
        (.assign .local (ofString "p") (.op .add [.var .local (ofString "p"), .var .local (ofString "w")])) =
        (none, setVarHOLFinite (ofString "p") (.val (.word p_next)) sc) := by
      rw [evaluateHOLFiniteState_assign]
      have hev : @evalHOLExact 64 F _ sc.toExact (fun a => Classical.propDecidable (sc.memaddrs a))
          (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]) = some (.val (.word p_next)) := by
        simp [evalHOLExact, evalListHOLExact, hsc_p, hsc_w, wordOpHOL, wordOp, valueIsWord, valueWord, p_next]
      have hval : sc.isValidValueHOLFinite .local (ofString "p") (.val (.word p_next)) = true := by
        simp [PanSemStateFiniteExact.isValidValueHOLFinite, lookupKvarHOLExact, hsc_p, shapeOfHOLExact, shapeEqHOL]
      rw [hev]; dsimp only; rw [if_pos hval]; rfl
    rw [hass]; dsimp only
    set st' := setVarHOLFinite (ofString "p") (.val (.word p_next)) sc
    have heff_st' : HeapByteEff s0 st' Rl gw := by
      have hm : HeapByteEff st sc Rl gw :=
        heff_sc.mono (fun i hi _ => Or.inl ⟨i, hi, le_rfl, le_rfl⟩) (fun _ h => by cases h)
      exact (heff.trans hm).locals_clock st'.locals st'.clock
    refine ⟨fun _ => ⟨p_next, w_next, by omega, by omega, heff_st', ?_, ?_, ?_, ?_⟩,
      fun h => False.elim (h rfl)⟩
    · simp [st', setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsc_h,
        show ofString "p" ≠ ofString "h" by decide]
    · simp [st', setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsc_buf,
        show ofString "p" ≠ ofString "buf" by decide]
    · simp [st', setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    · simp [st', setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsc_w,
        show ofString "p" ≠ ofString "w" by decide]

private theorem step_enc_u256 {F : Type}
    {s0 st : PanSemStateFiniteExact 64 F}
    {hw buf p_cur w_prev : BitVec 64} {Rl : List Ivl} {gw : List String}
    (hAR0 : ArenaReady s0)
    (heff : HeapByteEff s0 st Rl gw)
    (hgw : "heap_ptr" ∈ gw)
    (hH0 : HeaderAtStrong s0 hw.toNat)
    (hRl_ge : ∀ i ∈ Rl, 0 < i.2 → globN s0 "heap_ptr" ≤ i.1)
    (hst_h : st.locals.lookup (ofString "h") = some (.val (.word hw)))
    (hst_buf : st.locals.lookup (ofString "buf") = some (.val (.word buf)))
    (hst_p : st.locals.lookup (ofString "p") = some (.val (.word p_cur)))
    (hst_w : st.locals.lookup (ofString "w") = some (.val (.word w_prev)))
    (off : Nat) (hoff8 : off % 8 = 0) (hoff_hi : off + 32 ≤ 248)
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ p_cur.toNat ∧ p_cur.toNat + 33 ≤ ivl.1 + ivl.2)
    (hp_add_lt : p_cur.toNat + 33 < 2 ^ 64)
    (rest : ProgHOL 64)
    (hnt : (evaluateHOLFiniteState st
      (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_put_u256")
          [.var .local (ofString "p"),
           .load (.comb [.one, .one, .one, .one])
             (.op .add [.var .local (ofString "h"), .const (BitVec.ofNat 64 off)])])
        (.seq (.assign .local (ofString "p") (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
          rest))).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState st
      (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_put_u256")
          [.var .local (ofString "p"),
           .load (.comb [.one, .one, .one, .one])
             (.op .add [.var .local (ofString "h"), .const (BitVec.ofNat 64 off)])])
        (.seq (.assign .local (ofString "p") (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
          rest))).1) :
    ∃ (p_next w_next : BitVec 64) (st' : PanSemStateFiniteExact 64 F),
      p_cur.toNat ≤ p_next.toNat ∧
      p_next.toNat ≤ p_cur.toNat + 33 ∧
      HeapByteEff s0 st' Rl gw ∧
      st'.locals.lookup (ofString "h") = some (.val (.word hw)) ∧
      st'.locals.lookup (ofString "buf") = some (.val (.word buf)) ∧
      st'.locals.lookup (ofString "p") = some (.val (.word p_next)) ∧
      st'.locals.lookup (ofString "w") = some (.val (.word w_next)) ∧
      (evaluateHOLFiniteState st' rest).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState st' rest).1 ∧
      evaluateHOLFiniteState st
        (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_put_u256")
            [.var .local (ofString "p"),
             .load (.comb [.one, .one, .one, .one])
               (.op .add [.var .local (ofString "h"), .const (BitVec.ofNat 64 off)])])
          (.seq (.assign .local (ofString "p") (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
            rest)) =
        evaluateHOLFiniteState st' rest := by
  obtain ⟨u0, u1, u2, u3, hev_v⟩ := eval_load_header_u256 hAR0 heff hH0 hRl_ge hst_h off hoff8 hoff_hi
  rw [evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
  rcases hc : evaluateHOLFiniteState st
    (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_put_u256")
      [.var .local (ofString "p"),
       .load (.comb [.one, .one, .one, .one])
         (.op .add [.var .local (ofString "h"), .const (BitVec.ofNat 64 off)])]) with ⟨rc, sc⟩
  have hnt_c : rc ≠ some .timeOut := by rintro rfl; simp [hc] at hnt
  have hc_prop := eval_call_local_rlp_put_u256 st "w"
    (.var .local (ofString "p"))
    (.load (.comb [.one, .one, .one, .one])
      (.op .add [.var .local (ofString "h"), .const (BitVec.ofNat 64 off)]))
    p_cur u0 u1 u2 u3
    Rl gw heff.arena.1.code heff.arena hgw ⟨w_prev, hst_w⟩
    hst_p hev_v hin_ivl (by rw [hc]; exact hnt_c)
  dsimp only at hc_prop
  rw [hc] at hc_prop
  simp only [hc] at hnt hres ⊢
  cases rc with
  | some rc0 =>
    exfalso
    exact hc_prop.2 (by simp) hres
  | none =>
    dsimp only at hnt hres ⊢
    obtain ⟨w_next, hw_le, _, _, hsc_loc, heff_sc⟩ := hc_prop.1 rfl
    have hsc_w : sc.locals.lookup (ofString "w") = some (.val (.word w_next)) := by
      rw [hsc_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
    have hsc_p : sc.locals.lookup (ofString "p") = some (.val (.word p_cur)) := by
      rw [hsc_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hst_p,
        show ofString "w" ≠ ofString "p" by decide]
    have hsc_buf : sc.locals.lookup (ofString "buf") = some (.val (.word buf)) := by
      rw [hsc_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hst_buf,
        show ofString "w" ≠ ofString "buf" by decide]
    have hsc_h : sc.locals.lookup (ofString "h") = some (.val (.word hw)) := by
      rw [hsc_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hst_h,
        show ofString "w" ≠ ofString "h" by decide]
    let p_next : BitVec 64 := p_cur + w_next
    have hp_next_nat : p_next.toNat = p_cur.toNat + w_next.toNat := by
      change (p_cur + w_next).toNat = p_cur.toNat + w_next.toNat
      rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
    have hass : evaluateHOLFiniteState sc
        (.assign .local (ofString "p") (.op .add [.var .local (ofString "p"), .var .local (ofString "w")])) =
        (none, setVarHOLFinite (ofString "p") (.val (.word p_next)) sc) := by
      rw [evaluateHOLFiniteState_assign]
      have hev : @evalHOLExact 64 F _ sc.toExact (fun a => Classical.propDecidable (sc.memaddrs a))
          (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]) = some (.val (.word p_next)) := by
        simp [evalHOLExact, evalListHOLExact, hsc_p, hsc_w, wordOpHOL, wordOp, valueIsWord, valueWord, p_next]
      have hval : sc.isValidValueHOLFinite .local (ofString "p") (.val (.word p_next)) = true := by
        simp [PanSemStateFiniteExact.isValidValueHOLFinite, lookupKvarHOLExact, hsc_p, shapeOfHOLExact, shapeEqHOL]
      rw [hev]; dsimp only; rw [if_pos hval]; rfl
    rw [evaluateHOLFiniteState_seq_line780, hass] at hnt hres ⊢
    dsimp only at hnt hres ⊢
    set st' := setVarHOLFinite (ofString "p") (.val (.word p_next)) sc
    have heff_st' : HeapByteEff s0 st' Rl gw :=
      (heff.trans heff_sc).locals_clock st'.locals st'.clock
    refine ⟨p_next, w_next, st', by omega, by omega, heff_st', ?_, ?_, ?_, ?_, hnt, hres, rfl⟩
    · simp [st', setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsc_h,
        show ofString "p" ≠ ofString "h" by decide]
    · simp [st', setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsc_buf,
        show ofString "p" ≠ ofString "buf" by decide]
    · simp [st', setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    · simp [st', setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsc_w,
        show ofString "p" ≠ ofString "w" by decide]

private theorem step_enc_extra_bytes {F : Type}
    {s0 st : PanSemStateFiniteExact 64 F}
    {hw buf p_cur w_prev : BitVec 64} {Rl : List Ivl} {gw : List String}
    (hAR0 : ArenaReady s0)
    (heff : HeapByteEff s0 st Rl gw)
    (hH0 : HeaderAtStrong s0 hw.toNat)
    (hRl_ge : ∀ i ∈ Rl, 0 < i.2 → globN s0 "heap_ptr" ≤ i.1)
    (hst_h : st.locals.lookup (ofString "h") = some (.val (.word hw)))
    (hst_buf : st.locals.lookup (ofString "buf") = some (.val (.word buf)))
    (hst_p : st.locals.lookup (ofString "p") = some (.val (.word p_cur)))
    (hst_w : st.locals.lookup (ofString "w") = some (.val (.word w_prev)))
    (hin_ivl : ∃ ivl ∈ Rl, ivl.1 ≤ p_cur.toNat ∧ p_cur.toNat + 33 ≤ ivl.1 + ivl.2)
    (hp_add_lt : p_cur.toNat + 33 < 2 ^ 64)
    (rest : ProgHOL 64)
    (hnt : (evaluateHOLFiniteState st
      (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_bytes")
          [.var .local (ofString "p"),
           .load .one (.op .add [.var .local (ofString "h"), .const (BitVec.ofNat 64 128)]),
           .load .one (.op .add [.var .local (ofString "h"), .const (BitVec.ofNat 64 136)])])
        (.seq (.assign .local (ofString "p") (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
          rest))).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState st
      (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_bytes")
          [.var .local (ofString "p"),
           .load .one (.op .add [.var .local (ofString "h"), .const (BitVec.ofNat 64 128)]),
           .load .one (.op .add [.var .local (ofString "h"), .const (BitVec.ofNat 64 136)])])
        (.seq (.assign .local (ofString "p") (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
          rest))).1) :
    ∃ (p_next w_next : BitVec 64) (st' : PanSemStateFiniteExact 64 F),
      p_cur.toNat ≤ p_next.toNat ∧
      p_next.toNat ≤ p_cur.toNat + 33 ∧
      HeapByteEff s0 st' Rl gw ∧
      st'.locals.lookup (ofString "h") = some (.val (.word hw)) ∧
      st'.locals.lookup (ofString "buf") = some (.val (.word buf)) ∧
      st'.locals.lookup (ofString "p") = some (.val (.word p_next)) ∧
      st'.locals.lookup (ofString "w") = some (.val (.word w_next)) ∧
      (evaluateHOLFiniteState st' rest).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState st' rest).1 ∧
      evaluateHOLFiniteState st
        (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_bytes")
            [.var .local (ofString "p"),
             .load .one (.op .add [.var .local (ofString "h"), .const (BitVec.ofNat 64 128)]),
             .load .one (.op .add [.var .local (ofString "h"), .const (BitVec.ofNat 64 136)])])
          (.seq (.assign .local (ofString "p") (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
            rest)) =
        evaluateHOLFiniteState st' rest := by
  have hev_src := eval_load_header_word hAR0 heff hH0 hRl_ge hst_h 128 (by decide) (by decide)
  have hev_len := eval_load_header_word hAR0 heff hH0 hRl_ge hst_h 136 (by decide) (by decide)
  have h136_le : memW s0 (hw.toNat + 136) ≤ 32 := hH0.1.2
  have hn_nat : (BitVec.ofNat 64 (memW s0 (hw.toNat + 136))).toNat = memW s0 (hw.toNat + 136) :=
    Nat.mod_eq_of_lt (by omega)
  have hrlp_le : rlpHeaderLenPure (memW s0 (hw.toNat + 136)) + memW s0 (hw.toNat + 136) ≤ 33 := by
    have h55 : memW s0 (hw.toNat + 136) ≤ 55 := by omega
    simp only [rlpHeaderLenPure, h55, ↓reduceIte]; omega
  have hin_ivl' : ∃ ivl ∈ Rl, ivl.1 ≤ p_cur.toNat ∧
      p_cur.toNat + rlpHeaderLenPure (BitVec.ofNat 64 (memW s0 (hw.toNat + 136))).toNat +
        (BitVec.ofNat 64 (memW s0 (hw.toNat + 136))).toNat ≤ ivl.1 + ivl.2 := by
    obtain ⟨ivl, hivl, h1, h2⟩ := hin_ivl
    exact ⟨ivl, hivl, h1, by rw [hn_nat]; omega⟩
  rw [evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
  rcases hc : evaluateHOLFiniteState st
    (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_bytes")
      [.var .local (ofString "p"),
       .load .one (.op .add [.var .local (ofString "h"), .const (BitVec.ofNat 64 128)]),
       .load .one (.op .add [.var .local (ofString "h"), .const (BitVec.ofNat 64 136)])]) with ⟨rc, sc⟩
  have hnt_c : rc ≠ some .timeOut := by rintro rfl; simp [hc] at hnt
  have hc_prop := eval_call_local_rlp_encode_bytes st "w"
    (.var .local (ofString "p"))
    (.load .one (.op .add [.var .local (ofString "h"), .const (BitVec.ofNat 64 128)]))
    (.load .one (.op .add [.var .local (ofString "h"), .const (BitVec.ofNat 64 136)]))
    p_cur (BitVec.ofNat 64 (memW s0 (hw.toNat + 128))) (BitVec.ofNat 64 (memW s0 (hw.toNat + 136)))
    Rl [] heff.arena.1.code heff.arena ⟨w_prev, hst_w⟩
    hst_p hev_src hev_len hin_ivl' (by rw [hc]; exact hnt_c)
  dsimp only at hc_prop
  rw [hc] at hc_prop
  simp only [hc] at hnt hres ⊢
  cases rc with
  | some rc0 =>
    exfalso
    exact hc_prop.2 (by simp) hres
  | none =>
    dsimp only at hnt hres ⊢
    obtain ⟨w_next, hw_le, _, _, hsc_loc, heff_sc⟩ := hc_prop.1 rfl
    rw [hn_nat] at hw_le
    have hsc_w : sc.locals.lookup (ofString "w") = some (.val (.word w_next)) := by
      rw [hsc_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
    have hsc_p : sc.locals.lookup (ofString "p") = some (.val (.word p_cur)) := by
      rw [hsc_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hst_p,
        show ofString "w" ≠ ofString "p" by decide]
    have hsc_buf : sc.locals.lookup (ofString "buf") = some (.val (.word buf)) := by
      rw [hsc_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hst_buf,
        show ofString "w" ≠ ofString "buf" by decide]
    have hsc_h : sc.locals.lookup (ofString "h") = some (.val (.word hw)) := by
      rw [hsc_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hst_h,
        show ofString "w" ≠ ofString "h" by decide]
    let p_next : BitVec 64 := p_cur + w_next
    have hp_next_nat : p_next.toNat = p_cur.toNat + w_next.toNat := by
      change (p_cur + w_next).toNat = p_cur.toNat + w_next.toNat
      rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
    have hass : evaluateHOLFiniteState sc
        (.assign .local (ofString "p") (.op .add [.var .local (ofString "p"), .var .local (ofString "w")])) =
        (none, setVarHOLFinite (ofString "p") (.val (.word p_next)) sc) := by
      rw [evaluateHOLFiniteState_assign]
      have hev : @evalHOLExact 64 F _ sc.toExact (fun a => Classical.propDecidable (sc.memaddrs a))
          (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]) = some (.val (.word p_next)) := by
        simp [evalHOLExact, evalListHOLExact, hsc_p, hsc_w, wordOpHOL, wordOp, valueIsWord, valueWord, p_next]
      have hval : sc.isValidValueHOLFinite .local (ofString "p") (.val (.word p_next)) = true := by
        simp [PanSemStateFiniteExact.isValidValueHOLFinite, lookupKvarHOLExact, hsc_p, shapeOfHOLExact, shapeEqHOL]
      rw [hev]; dsimp only; rw [if_pos hval]; rfl
    rw [evaluateHOLFiniteState_seq_line780, hass] at hnt hres ⊢
    dsimp only at hnt hres ⊢
    set st' := setVarHOLFinite (ofString "p") (.val (.word p_next)) sc
    have heff_st' : HeapByteEff s0 st' Rl gw := by
      have hm : HeapByteEff st sc Rl gw :=
        heff_sc.mono (fun i hi _ => Or.inl ⟨i, hi, le_rfl, le_rfl⟩) (fun _ h => by cases h)
      exact (heff.trans hm).locals_clock st'.locals st'.clock
    refine ⟨p_next, w_next, st', by omega, by omega, heff_st', ?_, ?_, ?_, ?_, hnt, hres, rfl⟩
    · simp [st', setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsc_h,
        show ofString "p" ≠ ofString "h" by decide]
    · simp [st', setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsc_buf,
        show ofString "p" ≠ ofString "buf" by decide]
    · simp [st', setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    · simp [st', setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hsc_w,
        show ofString "p" ≠ ofString "w" by decide]

/-! ## Section 6: `eval_decCall_encode_header` and `wk_header_hash_inside` -/

private theorem heapByteEff_of_seq_none_hh {F : Type}
    {s0 s m : PanSemStateFiniteExact 64 F} {a b : ProgHOL 64} {Rl : List Ivl} {gw : List String}
    (ha : evaluateHOLFiniteState s a = (none, m))
    (hb : HeapByteEff s0 (evaluateHOLFiniteState m b).2 Rl gw) :
    HeapByteEff s0 (evaluateHOLFiniteState s (.seq a b)).2 Rl gw := by
  rw [evaluateHOLFiniteState_seq_line780, ha]
  exact hb

private theorem heapByteEff_of_seq_some_hh {F : Type}
    {s0 s m : PanSemStateFiniteExact 64 F} {a b : ProgHOL 64} {r : PanSemResultExact 64}
    {Rl : List Ivl} {gw : List String}
    (ha : evaluateHOLFiniteState s a = (some r, m))
    (hm : HeapByteEff s0 m Rl gw) :
    HeapByteEff s0 (evaluateHOLFiniteState s (.seq a b)).2 Rl gw := by
  rw [evaluateHOLFiniteState_seq_line780, ha]
  exact hm

private theorem heapByteEff_of_eq_resVar_hh {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {p : ProgHOL 64}
    {r' : Option (PanSemResultExact 64)} {q : PanSemStateFiniteExact 64 F}
    {L : HolFiniteMapExact MlS (ValueHOL 64)} {Rl : List Ivl} {gw : List String}
    (heq : evaluateHOLFiniteState s p = (r', { q with locals := L }))
    (hq : HeapByteEff s0 q Rl gw) :
    HeapByteEff s0 (evaluateHOLFiniteState s p).2 Rl gw := by
  rw [heq]
  exact hq.locals_clock L q.clock

private theorem eval_encode_header_body {F : Type}
    {ent : PanSemStateFiniteExact 64 F} {hw : BitVec 64}
    (hcode : ent.code = originalRuntimeCode) (hAR : ArenaReady ent)
    (hH : HeaderAtStrong ent hw.toNat)
    (hent_h : ent.locals.lookup (ofString "h") = some (.val (.word hw)))
    (hnt : (evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_encode_header)).1 ≠
      some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState ent
      (sourceFnBody Guest.Software.guestFn_encode_header)).1) :
    ∃ (startw totalw : BitVec 64) (q : PanSemStateFiniteExact 64 F)
      (L : HolFiniteMapExact MlS (ValueHOL 64)),
      HeapByteEff ent q [] ["heap_ptr"] ∧
      evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_encode_header) =
        (some (.returned (.rStruct [.val (.word startw), .val (.word totalw)])),
         { q with locals := L }) := by
  have hhl264 : heapLimit < 2 ^ 64 := by rw [heapLimit_val]; decide
  have hb : sourceFnBody Guest.Software.guestFn_encode_header =
      .decCall (ofString "buf") .one (ofString "alloc") [.const 1024]
        (.dec (ofString "p") .one (.op .add [.var .local (ofString "buf"), .const 9])
          (.decCall (ofString "w") .one (ofString "rlp_encode_bytes")
            [.var .local (ofString "p"),
             .load .one (.op .add [.var .local (ofString "h"), .const 8]),
             .const 32]
            (.seq (.assign .local (ofString "p") (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
              (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_bytes")
                  [.var .local (ofString "p"), .load .one (.op .add [.var .local (ofString "h"), .const 16]), .const 32])
                (.seq (.assign .local (ofString "p") (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
                  (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_bytes")
                      [.var .local (ofString "p"), .load .one (.op .add [.var .local (ofString "h"), .const 24]), .const 20])
                    (.seq (.assign .local (ofString "p") (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
                      (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_bytes")
                          [.var .local (ofString "p"), .load .one (.op .add [.var .local (ofString "h"), .const 32]), .const 32])
                        (.seq (.assign .local (ofString "p") (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
                          (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_bytes")
                              [.var .local (ofString "p"), .load .one (.op .add [.var .local (ofString "h"), .const 40]), .const 32])
                            (.seq (.assign .local (ofString "p") (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
                              (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_bytes")
                                  [.var .local (ofString "p"), .load .one (.op .add [.var .local (ofString "h"), .const 48]), .const 32])
                                (.seq (.assign .local (ofString "p") (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
                                  (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_bytes")
                                      [.var .local (ofString "p"), .load .one (.op .add [.var .local (ofString "h"), .const 56]), .const 256])
                                    (.seq (.assign .local (ofString "p") (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
                                      (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_put_u256")
                                          [.var .local (ofString "p"),
                                           .load (.comb [.one, .one, .one, .one]) (.op .add [.var .local (ofString "h"), .const 64])])
                                        (.seq (.assign .local (ofString "p") (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
                                          (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_word")
                                              [.var .local (ofString "p"), .load .one (.op .add [.var .local (ofString "h"), .const 96])])
                                            (.seq (.assign .local (ofString "p") (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
                                              (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_word")
                                                  [.var .local (ofString "p"), .load .one (.op .add [.var .local (ofString "h"), .const 104])])
                                                (.seq (.assign .local (ofString "p") (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
                                                  (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_word")
                                                      [.var .local (ofString "p"), .load .one (.op .add [.var .local (ofString "h"), .const 112])])
                                                    (.seq (.assign .local (ofString "p") (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
                                                      (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_word")
                                                          [.var .local (ofString "p"), .load .one (.op .add [.var .local (ofString "h"), .const 120])])
                                                        (.seq (.assign .local (ofString "p") (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
                                                          (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_bytes")
                                                              [.var .local (ofString "p"),
                                                               .load .one (.op .add [.var .local (ofString "h"), .const 128]),
                                                               .load .one (.op .add [.var .local (ofString "h"), .const 136])])
                                                            (.seq (.assign .local (ofString "p") (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
                                                              (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_bytes")
                                                                  [.var .local (ofString "p"), .load .one (.op .add [.var .local (ofString "h"), .const 144]), .const 32])
                                                                (.seq (.assign .local (ofString "p") (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
                                                                  (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_bytes")
                                                                      [.var .local (ofString "p"), .load .one (.op .add [.var .local (ofString "h"), .const 152]), .const 8])
                                                                    (.seq (.assign .local (ofString "p") (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
                                                                      (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_put_u256")
                                                                          [.var .local (ofString "p"),
                                                                           .load (.comb [.one, .one, .one, .one]) (.op .add [.var .local (ofString "h"), .const 160])])
                                                                        (.seq (.assign .local (ofString "p") (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
                                                                          (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_bytes")
                                                                              [.var .local (ofString "p"), .load .one (.op .add [.var .local (ofString "h"), .const 192]), .const 32])
                                                                            (.seq (.assign .local (ofString "p") (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
                                                                              (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_word")
                                                                                  [.var .local (ofString "p"), .load .one (.op .add [.var .local (ofString "h"), .const 200])])
                                                                                (.seq (.assign .local (ofString "p") (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
                                                                                  (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_word")
                                                                                      [.var .local (ofString "p"), .load .one (.op .add [.var .local (ofString "h"), .const 208])])
                                                                                    (.seq (.assign .local (ofString "p") (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
                                                                                      (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_bytes")
                                                                                          [.var .local (ofString "p"), .load .one (.op .add [.var .local (ofString "h"), .const 216]), .const 32])
                                                                                        (.seq (.assign .local (ofString "p") (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
                                                                                          (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_bytes")
                                                                                              [.var .local (ofString "p"), .load .one (.op .add [.var .local (ofString "h"), .const 224]), .const 32])
                                                                                            (.seq (.assign .local (ofString "p") (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
                                                                                              (.seq
                                                                                                (.ite (.cmp .notEqual (.load .one (.op .add [.var .local (ofString "h"), .const 0])) (.const 0))
                                                                                                  (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_bytes")
                                                                                                      [.var .local (ofString "p"), .load .one (.op .add [.var .local (ofString "h"), .const 232]), .const 32])
                                                                                                    (.seq (.assign .local (ofString "p") (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
                                                                                                      (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_word")
                                                                                                          [.var .local (ofString "p"), .load .one (.op .add [.var .local (ofString "h"), .const 240])])
                                                                                                        (.assign .local (ofString "p") (.op .add [.var .local (ofString "p"), .var .local (ofString "w")])))))
                                                                                                  .skip)
                                                                                                (.dec (ofString "payload_len") .one
                                                                                                  (.op .sub [.var .local (ofString "p"), .op .add [.var .local (ofString "buf"), .const 9]])
                                                                                                  (.decCall (ofString "hl") .one (ofString "rlp_list_header_len") [.var .local (ofString "payload_len")]
                                                                                                    (.dec (ofString "start") .one
                                                                                                      (.op .sub [.op .add [.var .local (ofString "buf"), .const 9], .var .local (ofString "hl")])
                                                                                                      (.seq (.call (some (none, none)) (ofString "rlp_encode_list_header")
                                                                                                          [.var .local (ofString "start"), .var .local (ofString "payload_len")])
                                                                                                          (.return (.rstruct [.var .local (ofString "start"),
                                                                                                            .op .add [.var .local (ofString "payload_len"), .var .local (ofString "hl")]])))))))))))))))))))))))))))))))))))))))))))))))))) := rfl
  rw [hb] at hnt hres ⊢
  obtain ⟨buf, n1024, q1, s1, h1024_ev, hbuf_hp, hbuf8, hq1_nat, _, hq1_hi, hq1_8, hs1_hp,
      hs1_g, hs1_m, hs1_loc, heff01_nil, hnt1, hres1, heq1⟩ :=
    eval_decCall_alloc_resumes ent "buf" (.const 1024) _ ([] : List Ivl) ["heap_ptr"] hcode hAR
      (by simp) hnt hres
  have hn1024 : n1024 = 1024 := by simp [evalHOLExact] at h1024_ev; exact h1024_ev.symm
  subst hn1024
  have h1024_val : (1024 : BitVec 64).toNat = 1024 := by decide
  rw [h1024_val] at hq1_nat
  have hq1_eq : q1.toNat = buf.toNat + 1024 := by omega
  have hbuf_hi : buf.toNat + 1024 ≤ heapLimit := by omega
  let Rbuf : List Ivl := [(buf.toNat, 1024)]
  have hRl_ge : ∀ i ∈ Rbuf, 0 < i.2 → globN ent "heap_ptr" ≤ i.1 := by
    intro i hi _; simp only [Rbuf, List.mem_singleton] at hi; subst hi; omega
  have heff01 : HeapByteEff ent s1 Rbuf ["heap_ptr"] :=
    heff01_nil.mono (fun _ h => by cases h) (fun _ h => h)
  have hs1_buf : s1.locals.lookup (ofString "buf") = some (.val (.word buf)) := by
    rw [hs1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hs1_h : s1.locals.lookup (ofString "h") = some (.val (.word hw)) := by
    rw [hs1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hent_h,
      show ofString "buf" ≠ ofString "h" by decide]
  rw [evaluateHOLFiniteState_dec_total] at hnt1 hres1
  let p0 : BitVec 64 := buf + 9
  have hp0_nat : p0.toNat = buf.toNat + 9 := by
    change (buf + 9).toNat = buf.toNat + 9
    rw [BitVec.toNat_add]; change (buf.toNat + 9) % 2 ^ 64 = _
    exact Nat.mod_eq_of_lt (by omega)
  have hev_p0 : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
      (.op .add [.var .local (ofString "buf"), .const 9]) = some (.val (.word p0)) := by
    simp [evalHOLExact, evalListHOLExact, hs1_buf, wordOpHOL, wordOp, valueIsWord, valueWord, p0]
  have hsh_p0 : shapeEqHOL .one (shapeOfHOLExact (.val (.word p0) : ValueHOL 64)) = true := by
    simp [shapeOfHOLExact, shapeEqHOL]
  dsimp only at hnt1 hres1
  rw [hev_p0] at hnt1 hres1; dsimp only at hnt1 hres1; rw [if_pos hsh_p0] at hnt1 hres1
  set s2 := setVarHOLFinite (ofString "p") (.val (.word p0)) s1
  have heff02 : HeapByteEff ent s2 Rbuf ["heap_ptr"] := heff01.locals_clock s2.locals s2.clock
  have hs2_p : s2.locals.lookup (ofString "p") = some (.val (.word p0)) := by
    simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs2_buf : s2.locals.lookup (ofString "buf") = some (.val (.word buf)) := by
    simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs1_buf,
      show ofString "p" ≠ ofString "buf" by decide]
  have hs2_h : s2.locals.lookup (ofString "h") = some (.val (.word hw)) := by
    simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs1_h,
      show ofString "p" ≠ ofString "h" by decide]
  have hev_h8 := eval_load_header_word hAR heff02 hH hRl_ge hs2_h 8 (by decide) (by decide)
  have hrlp32 : rlpHeaderLenPure 32 = 1 := by decide
  have hrlp20 : rlpHeaderLenPure 20 = 1 := by decide
  have hrlp256 : rlpHeaderLenPure 256 = 3 := by decide
  have hrlp8 : rlpHeaderLenPure 8 = 1 := by decide
  obtain ⟨w3, s3a, hw3_le, _, _, hs3a_loc, heff23a, hnt3a, hres3a, heq3a⟩ :=
    eval_decCall_rlp_encode_bytes s2 "w"
      (.var .local (ofString "p"))
      (.load .one (.op .add [.var .local (ofString "h"), .const 8]))
      (.const 32)
      p0 (BitVec.ofNat 64 (memW ent (hw.toNat + 8))) 32 _ Rbuf ["heap_ptr"]
      heff02.arena.1.code heff02.arena hs2_p hev_h8 rfl
      ⟨(buf.toNat, 1024), List.mem_singleton.mpr rfl, by omega,
        by change p0.toNat + rlpHeaderLenPure 32 + 32 ≤ buf.toNat + 1024; rw [hrlp32]; omega⟩
      hnt1 hres1
  change w3.toNat ≤ rlpHeaderLenPure 32 + 32 at hw3_le
  rw [hrlp32] at hw3_le
  have hs3a_w : s3a.locals.lookup (ofString "w") = some (.val (.word w3)) := by
    rw [hs3a_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hs3a_p : s3a.locals.lookup (ofString "p") = some (.val (.word p0)) := by
    rw [hs3a_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs2_p,
      show ofString "w" ≠ ofString "p" by decide]
  have hs3a_buf : s3a.locals.lookup (ofString "buf") = some (.val (.word buf)) := by
    rw [hs3a_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs2_buf,
      show ofString "w" ≠ ofString "buf" by decide]
  have hs3a_h : s3a.locals.lookup (ofString "h") = some (.val (.word hw)) := by
    rw [hs3a_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs2_h,
      show ofString "w" ≠ ofString "h" by decide]
  let p1 : BitVec 64 := p0 + w3
  have hp1_nat : p1.toNat = p0.toNat + w3.toNat := by
    change (p0 + w3).toNat = p0.toNat + w3.toNat
    rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  have hass1 : evaluateHOLFiniteState s3a
      (.assign .local (ofString "p") (.op .add [.var .local (ofString "p"), .var .local (ofString "w")])) =
      (none, setVarHOLFinite (ofString "p") (.val (.word p1)) s3a) := by
    rw [evaluateHOLFiniteState_assign]
    have hev : @evalHOLExact 64 F _ s3a.toExact (fun a => Classical.propDecidable (s3a.memaddrs a))
        (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]) = some (.val (.word p1)) := by
      simp [evalHOLExact, evalListHOLExact, hs3a_p, hs3a_w, wordOpHOL, wordOp, valueIsWord, valueWord, p1]
    have hval : s3a.isValidValueHOLFinite .local (ofString "p") (.val (.word p1)) = true := by
      simp [PanSemStateFiniteExact.isValidValueHOLFinite, lookupKvarHOLExact, hs3a_p, shapeOfHOLExact, shapeEqHOL]
    rw [hev]; dsimp only; rw [if_pos hval]; rfl
  rw [evaluateHOLFiniteState_seq_line780, hass1] at hnt3a hres3a
  dsimp only at hnt3a hres3a
  set st1 := setVarHOLFinite (ofString "p") (.val (.word p1)) s3a
  have heff_st1 : HeapByteEff ent st1 Rbuf ["heap_ptr"] :=
    (heff02.trans heff23a).locals_clock st1.locals st1.clock
  have hst1_h : st1.locals.lookup (ofString "h") = some (.val (.word hw)) := by
    simp [st1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3a_h,
      show ofString "p" ≠ ofString "h" by decide]
  have hst1_buf : st1.locals.lookup (ofString "buf") = some (.val (.word buf)) := by
    simp [st1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3a_buf,
      show ofString "p" ≠ ofString "buf" by decide]
  have hst1_p : st1.locals.lookup (ofString "p") = some (.val (.word p1)) := by
    simp [st1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hst1_w : st1.locals.lookup (ofString "w") = some (.val (.word w3)) := by
    simp [st1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3a_w,
      show ofString "p" ≠ ofString "w" by decide]
  obtain ⟨p2, w_2, st2, hp2_lo, hp2_hi, heff_st2, hst2_h, hst2_buf, hst2_p, hst2_w, hnt_2, hres_2, heq_2⟩ :=
    step_enc_bytes_const hAR heff_st1 hH hRl_ge hst1_h hst1_buf hst1_p hst1_w 16 32
      (by decide) (by decide) (by decide)
      ⟨(buf.toNat, 1024), List.mem_singleton.mpr rfl, by omega, by rw [hrlp32]; omega⟩
      (by rw [hrlp32]; omega) _ hnt3a hres3a
  rw [hrlp32] at hp2_hi
  obtain ⟨p3, w_3, st3, hp3_lo, hp3_hi, heff_st3, hst3_h, hst3_buf, hst3_p, hst3_w, hnt_3, hres_3, heq_3⟩ :=
    step_enc_bytes_const hAR heff_st2 hH hRl_ge hst2_h hst2_buf hst2_p hst2_w 24 20
      (by decide) (by decide) (by decide)
      ⟨(buf.toNat, 1024), List.mem_singleton.mpr rfl, by omega, by rw [hrlp20]; omega⟩
      (by rw [hrlp20]; omega) _ hnt_2 hres_2
  rw [hrlp20] at hp3_hi
  obtain ⟨p4, w_4, st4, hp4_lo, hp4_hi, heff_st4, hst4_h, hst4_buf, hst4_p, hst4_w, hnt_4, hres_4, heq_4⟩ :=
    step_enc_bytes_const hAR heff_st3 hH hRl_ge hst3_h hst3_buf hst3_p hst3_w 32 32
      (by decide) (by decide) (by decide)
      ⟨(buf.toNat, 1024), List.mem_singleton.mpr rfl, by omega, by rw [hrlp32]; omega⟩
      (by rw [hrlp32]; omega) _ hnt_3 hres_3
  rw [hrlp32] at hp4_hi
  obtain ⟨p5, w_5, st5, hp5_lo, hp5_hi, heff_st5, hst5_h, hst5_buf, hst5_p, hst5_w, hnt_5, hres_5, heq_5⟩ :=
    step_enc_bytes_const hAR heff_st4 hH hRl_ge hst4_h hst4_buf hst4_p hst4_w 40 32
      (by decide) (by decide) (by decide)
      ⟨(buf.toNat, 1024), List.mem_singleton.mpr rfl, by omega, by rw [hrlp32]; omega⟩
      (by rw [hrlp32]; omega) _ hnt_4 hres_4
  rw [hrlp32] at hp5_hi
  obtain ⟨p6, w_6, st6, hp6_lo, hp6_hi, heff_st6, hst6_h, hst6_buf, hst6_p, hst6_w, hnt_6, hres_6, heq_6⟩ :=
    step_enc_bytes_const hAR heff_st5 hH hRl_ge hst5_h hst5_buf hst5_p hst5_w 48 32
      (by decide) (by decide) (by decide)
      ⟨(buf.toNat, 1024), List.mem_singleton.mpr rfl, by omega, by rw [hrlp32]; omega⟩
      (by rw [hrlp32]; omega) _ hnt_5 hres_5
  rw [hrlp32] at hp6_hi
  obtain ⟨p7, w_7, st7, hp7_lo, hp7_hi, heff_st7, hst7_h, hst7_buf, hst7_p, hst7_w, hnt_7, hres_7, heq_7⟩ :=
    step_enc_bytes_const hAR heff_st6 hH hRl_ge hst6_h hst6_buf hst6_p hst6_w 56 256
      (by decide) (by decide) (by decide)
      ⟨(buf.toNat, 1024), List.mem_singleton.mpr rfl, by omega, by rw [hrlp256]; omega⟩
      (by rw [hrlp256]; omega) _ hnt_6 hres_6
  rw [hrlp256] at hp7_hi
  obtain ⟨p8, w_8, st8, hp8_lo, hp8_hi, heff_st8, hst8_h, hst8_buf, hst8_p, hst8_w, hnt_8, hres_8, heq_8⟩ :=
    step_enc_u256 hAR heff_st7 (by simp) hH hRl_ge hst7_h hst7_buf hst7_p hst7_w 64
      (by decide) (by decide)
      ⟨(buf.toNat, 1024), List.mem_singleton.mpr rfl, by omega, by omega⟩
      (by omega) _ hnt_7 hres_7
  obtain ⟨p9, w_9, st9, hp9_lo, hp9_hi, heff_st9, hst9_h, hst9_buf, hst9_p, hst9_w, hnt_9, hres_9, heq_9⟩ :=
    step_enc_word hAR heff_st8 hH hRl_ge hst8_h hst8_buf hst8_p hst8_w 96
      (by decide) (by decide)
      ⟨(buf.toNat, 1024), List.mem_singleton.mpr rfl, by omega, by omega⟩
      (by omega) _ hnt_8 hres_8
  obtain ⟨p10, w_10, st10, hp10_lo, hp10_hi, heff_st10, hst10_h, hst10_buf, hst10_p, hst10_w, hnt_10, hres_10, heq_10⟩ :=
    step_enc_word hAR heff_st9 hH hRl_ge hst9_h hst9_buf hst9_p hst9_w 104
      (by decide) (by decide)
      ⟨(buf.toNat, 1024), List.mem_singleton.mpr rfl, by omega, by omega⟩
      (by omega) _ hnt_9 hres_9
  obtain ⟨p11, w_11, st11, hp11_lo, hp11_hi, heff_st11, hst11_h, hst11_buf, hst11_p, hst11_w, hnt_11, hres_11, heq_11⟩ :=
    step_enc_word hAR heff_st10 hH hRl_ge hst10_h hst10_buf hst10_p hst10_w 112
      (by decide) (by decide)
      ⟨(buf.toNat, 1024), List.mem_singleton.mpr rfl, by omega, by omega⟩
      (by omega) _ hnt_10 hres_10
  obtain ⟨p12, w_12, st12, hp12_lo, hp12_hi, heff_st12, hst12_h, hst12_buf, hst12_p, hst12_w, hnt_12, hres_12, heq_12⟩ :=
    step_enc_word hAR heff_st11 hH hRl_ge hst11_h hst11_buf hst11_p hst11_w 120
      (by decide) (by decide)
      ⟨(buf.toNat, 1024), List.mem_singleton.mpr rfl, by omega, by omega⟩
      (by omega) _ hnt_11 hres_11
  obtain ⟨p13, w_13, st13, hp13_lo, hp13_hi, heff_st13, hst13_h, hst13_buf, hst13_p, hst13_w, hnt_13, hres_13, heq_13⟩ :=
    step_enc_extra_bytes hAR heff_st12 hH hRl_ge hst12_h hst12_buf hst12_p hst12_w
      ⟨(buf.toNat, 1024), List.mem_singleton.mpr rfl, by omega, by omega⟩
      (by omega) _ hnt_12 hres_12
  obtain ⟨p14, w_14, st14, hp14_lo, hp14_hi, heff_st14, hst14_h, hst14_buf, hst14_p, hst14_w, hnt_14, hres_14, heq_14⟩ :=
    step_enc_bytes_const hAR heff_st13 hH hRl_ge hst13_h hst13_buf hst13_p hst13_w 144 32
      (by decide) (by decide) (by decide)
      ⟨(buf.toNat, 1024), List.mem_singleton.mpr rfl, by omega, by rw [hrlp32]; omega⟩
      (by rw [hrlp32]; omega) _ hnt_13 hres_13
  rw [hrlp32] at hp14_hi
  obtain ⟨p15, w_15, st15, hp15_lo, hp15_hi, heff_st15, hst15_h, hst15_buf, hst15_p, hst15_w, hnt_15, hres_15, heq_15⟩ :=
    step_enc_bytes_const hAR heff_st14 hH hRl_ge hst14_h hst14_buf hst14_p hst14_w 152 8
      (by decide) (by decide) (by decide)
      ⟨(buf.toNat, 1024), List.mem_singleton.mpr rfl, by omega, by rw [hrlp8]; omega⟩
      (by rw [hrlp8]; omega) _ hnt_14 hres_14
  rw [hrlp8] at hp15_hi
  obtain ⟨p16, w_16, st16, hp16_lo, hp16_hi, heff_st16, hst16_h, hst16_buf, hst16_p, hst16_w, hnt_16, hres_16, heq_16⟩ :=
    step_enc_u256 hAR heff_st15 (by simp) hH hRl_ge hst15_h hst15_buf hst15_p hst15_w 160
      (by decide) (by decide)
      ⟨(buf.toNat, 1024), List.mem_singleton.mpr rfl, by omega, by omega⟩
      (by omega) _ hnt_15 hres_15
  obtain ⟨p17, w_17, st17, hp17_lo, hp17_hi, heff_st17, hst17_h, hst17_buf, hst17_p, hst17_w, hnt_17, hres_17, heq_17⟩ :=
    step_enc_bytes_const hAR heff_st16 hH hRl_ge hst16_h hst16_buf hst16_p hst16_w 192 32
      (by decide) (by decide) (by decide)
      ⟨(buf.toNat, 1024), List.mem_singleton.mpr rfl, by omega, by rw [hrlp32]; omega⟩
      (by rw [hrlp32]; omega) _ hnt_16 hres_16
  rw [hrlp32] at hp17_hi
  obtain ⟨p18, w_18, st18, hp18_lo, hp18_hi, heff_st18, hst18_h, hst18_buf, hst18_p, hst18_w, hnt_18, hres_18, heq_18⟩ :=
    step_enc_word hAR heff_st17 hH hRl_ge hst17_h hst17_buf hst17_p hst17_w 200
      (by decide) (by decide)
      ⟨(buf.toNat, 1024), List.mem_singleton.mpr rfl, by omega, by omega⟩
      (by omega) _ hnt_17 hres_17
  obtain ⟨p19, w_19, st19, hp19_lo, hp19_hi, heff_st19, hst19_h, hst19_buf, hst19_p, hst19_w, hnt_19, hres_19, heq_19⟩ :=
    step_enc_word hAR heff_st18 hH hRl_ge hst18_h hst18_buf hst18_p hst18_w 208
      (by decide) (by decide)
      ⟨(buf.toNat, 1024), List.mem_singleton.mpr rfl, by omega, by omega⟩
      (by omega) _ hnt_18 hres_18
  obtain ⟨p20, w_20, st20, hp20_lo, hp20_hi, heff_st20, hst20_h, hst20_buf, hst20_p, hst20_w, hnt_20, hres_20, heq_20⟩ :=
    step_enc_bytes_const hAR heff_st19 hH hRl_ge hst19_h hst19_buf hst19_p hst19_w 216 32
      (by decide) (by decide) (by decide)
      ⟨(buf.toNat, 1024), List.mem_singleton.mpr rfl, by omega, by rw [hrlp32]; omega⟩
      (by rw [hrlp32]; omega) _ hnt_19 hres_19
  rw [hrlp32] at hp20_hi
  obtain ⟨p21, w_21, st21, hp21_lo, hp21_hi, heff_st21, hst21_h, hst21_buf, hst21_p, hst21_w, hnt_21, hres_21, heq_21⟩ :=
    step_enc_bytes_const hAR heff_st20 hH hRl_ge hst20_h hst20_buf hst20_p hst20_w 224 32
      (by decide) (by decide) (by decide)
      ⟨(buf.toNat, 1024), List.mem_singleton.mpr rfl, by omega, by rw [hrlp32]; omega⟩
      (by rw [hrlp32]; omega) _ hnt_20 hres_20
  rw [hrlp32] at hp21_hi
  let tailProg : ProgHOL 64 :=
    .dec (ofString "payload_len") .one
      (.op .sub [.var .local (ofString "p"), .op .add [.var .local (ofString "buf"), .const 9]])
      (.decCall (ofString "hl") .one (ofString "rlp_list_header_len") [.var .local (ofString "payload_len")]
        (.dec (ofString "start") .one
          (.op .sub [.op .add [.var .local (ofString "buf"), .const 9], .var .local (ofString "hl")])
          (.seq (.call (some (none, none)) (ofString "rlp_encode_list_header")
              [.var .local (ofString "start"), .var .local (ofString "payload_len")])
            (.return (.rstruct [.var .local (ofString "start"),
              .op .add [.var .local (ofString "payload_len"), .var .local (ofString "hl")]])))))
  let iteProg : ProgHOL 64 :=
    .ite (.cmp .notEqual (.load .one (.op .add [.var .local (ofString "h"), .const 0])) (.const 0))
      (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_bytes")
          [.var .local (ofString "p"), .load .one (.op .add [.var .local (ofString "h"), .const 232]), .const 32])
        (.seq (.assign .local (ofString "p") (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
          (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_word")
              [.var .local (ofString "p"), .load .one (.op .add [.var .local (ofString "h"), .const 240])])
            (.assign .local (ofString "p") (.op .add [.var .local (ofString "p"), .var .local (ofString "w")])))))
      .skip
  have hite_step : ∃ (p_fin : BitVec 64) (st_fin : PanSemStateFiniteExact 64 F),
      p0.toNat ≤ p_fin.toNat ∧
      p_fin.toNat ≤ buf.toNat + 790 ∧
      HeapByteEff ent st_fin Rbuf ["heap_ptr"] ∧
      st_fin.locals.lookup (ofString "buf") = some (.val (.word buf)) ∧
      st_fin.locals.lookup (ofString "p") = some (.val (.word p_fin)) ∧
      (evaluateHOLFiniteState st_fin tailProg).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState st_fin tailProg).1 ∧
      evaluateHOLFiniteState st21 (.seq iteProg tailProg) =
        evaluateHOLFiniteState st_fin tailProg := by
    have hev_h0 := eval_load_header_word hAR heff_st21 hH hRl_ge hst21_h 0 (by decide) (by decide)
    let w0 := BitVec.ofNat 64 (memW ent (hw.toNat + 0))
    have hev_cond : @evalHOLExact 64 F _ st21.toExact
        (fun a => Classical.propDecidable (st21.memaddrs a))
        (.cmp .notEqual (.load .one (.op .add [.var .local (ofString "h"), .const 0])) (.const 0)) =
        some (.val (.word (if w0 ≠ 0 then 1 else 0))) := by
      conv_lhs => rw [evalHOLExact.eq_def]
      dsimp only
      have h0eq : (0 : BitVec 64) = BitVec.ofNat 64 0 := rfl
      rw [h0eq, hev_h0]
      simp [evalHOLExact, Compiler.Encoders.Asm.wordCmpHOL, w0]
    have hseq_assoc : ∀ (s : PanSemStateFiniteExact 64 F) (a b c d e : ProgHOL 64),
        evaluateHOLFiniteState s (.seq (.seq a (.seq b (.seq c d))) e) =
        evaluateHOLFiniteState s (.seq a (.seq b (.seq c (.seq d e)))) := by
      intro s a b c d e
      simp only [evaluateHOLFiniteState_seq_line780]
      cases evaluateHOLFiniteState s a with | mk ra sa =>
      cases ra with
      | some _ => rfl
      | none =>
        dsimp only
        cases evaluateHOLFiniteState sa b with | mk rb sb =>
        cases rb with
        | some _ => rfl
        | none =>
          dsimp only
          cases evaluateHOLFiniteState sb c with | mk rc sc =>
          cases rc with
          | some _ => rfl
          | none => rfl
    by_cases hw0 : w0 ≠ 0
    · have hite_eq : evaluateHOLFiniteState st21 (.seq iteProg tailProg) =
          evaluateHOLFiniteState st21
            (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_bytes")
                [.var .local (ofString "p"), .load .one (.op .add [.var .local (ofString "h"), .const 232]), .const 32])
              (.seq (.assign .local (ofString "p") (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
                (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_word")
                    [.var .local (ofString "p"), .load .one (.op .add [.var .local (ofString "h"), .const 240])])
                  (.seq (.assign .local (ofString "p") (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
                    tailProg)))) := by
        rw [evaluateHOLFiniteState_seq_line780]
        have hi : evaluateHOLFiniteState st21 iteProg =
            evaluateHOLFiniteState st21
              (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_bytes")
                  [.var .local (ofString "p"), .load .one (.op .add [.var .local (ofString "h"), .const 232]), .const 32])
                (.seq (.assign .local (ofString "p") (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))
                  (.seq (.call (some (some (VarKind.local, ofString "w"), none)) (ofString "rlp_encode_word")
                      [.var .local (ofString "p"), .load .one (.op .add [.var .local (ofString "h"), .const 240])])
                    (.assign .local (ofString "p") (.op .add [.var .local (ofString "p"), .var .local (ofString "w")]))))) := by
          dsimp only [iteProg]; rw [evaluateHOLFiniteState_ite, hev_cond, if_pos hw0]; simp
        rw [hi, ← evaluateHOLFiniteState_seq_line780]
        exact hseq_assoc st21 _ _ _ _ tailProg
      change (evaluateHOLFiniteState st21 (.seq iteProg tailProg)).1 ≠ some .timeOut at hnt_21
      change Resumes (evaluateHOLFiniteState st21 (.seq iteProg tailProg)).1 at hres_21
      rw [hite_eq] at hnt_21 hres_21 ⊢
      obtain ⟨p22, w_22, st22, hp22_lo, hp22_hi, heff_st22, hst22_h, hst22_buf, hst22_p, hst22_w, hnt_22, hres_22, heq_22⟩ :=
        step_enc_bytes_const hAR heff_st21 hH hRl_ge hst21_h hst21_buf hst21_p hst21_w 232 32
          (by decide) (by decide) (by decide)
          ⟨(buf.toNat, 1024), List.mem_singleton.mpr rfl, by omega, by rw [hrlp32]; omega⟩
          (by rw [hrlp32]; omega) _ hnt_21 hres_21
      rw [hrlp32] at hp22_hi
      obtain ⟨p23, w_23, st23, hp23_lo, hp23_hi, heff_st23, _, hst23_buf, hst23_p, _, hnt_23, hres_23, heq_23⟩ :=
        step_enc_word hAR heff_st22 hH hRl_ge hst22_h hst22_buf hst22_p hst22_w 240
          (by decide) (by decide)
          ⟨(buf.toNat, 1024), List.mem_singleton.mpr rfl, by omega, by omega⟩
          (by omega) _ hnt_22 hres_22
      exact ⟨p23, st23, by omega, by omega, heff_st23, hst23_buf, hst23_p, hnt_23, hres_23,
        heq_22.trans heq_23⟩
    · have hite_eq : evaluateHOLFiniteState st21 (.seq iteProg tailProg) =
          evaluateHOLFiniteState st21 tailProg := by
        rw [evaluateHOLFiniteState_seq_line780]
        have hi : evaluateHOLFiniteState st21 iteProg = (none, st21) := by
          dsimp only [iteProg]; rw [evaluateHOLFiniteState_ite, hev_cond, if_neg hw0]
          simp [evaluateHOLFiniteState_skip]
        rw [hi]
      change (evaluateHOLFiniteState st21 (.seq iteProg tailProg)).1 ≠ some .timeOut at hnt_21
      change Resumes (evaluateHOLFiniteState st21 (.seq iteProg tailProg)).1 at hres_21
      rw [hite_eq] at hnt_21 hres_21 ⊢
      exact ⟨p21, st21, by omega, by omega, heff_st21, hst21_buf, hst21_p, hnt_21, hres_21, rfl⟩
  obtain ⟨p_fin, st_fin, hp_fin_lo, hp_fin_hi, heff_fin, hfin_buf, hfin_p, hnt_tail, hres_tail, heq_ite⟩ := hite_step
  dsimp only [tailProg] at hnt_tail hres_tail
  rw [evaluateHOLFiniteState_dec_total] at hnt_tail hres_tail
  let payw : BitVec 64 := p_fin - (buf + 9)
  have hpayw_nat : payw.toNat = p_fin.toNat - (buf.toNat + 9) := by
    change (p_fin - p0).toNat = p_fin.toNat - (buf.toNat + 9)
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr hp_fin_lo), hp0_nat]
  have hev_pay : @evalHOLExact 64 F _ st_fin.toExact
      (fun a => Classical.propDecidable (st_fin.memaddrs a))
      (.op .sub [.var .local (ofString "p"), .op .add [.var .local (ofString "buf"), .const 9]]) =
      some (.val (.word payw)) := by
    simp [evalHOLExact, evalListHOLExact, hfin_p, hfin_buf, wordOpHOL, wordOp, valueIsWord, valueWord, payw]
  have hsh_pay : shapeEqHOL .one (shapeOfHOLExact (.val (.word payw) : ValueHOL 64)) = true := by
    simp [shapeOfHOLExact, shapeEqHOL]
  dsimp only at hnt_tail hres_tail
  rw [hev_pay] at hnt_tail hres_tail; dsimp only at hnt_tail hres_tail
  rw [if_pos hsh_pay] at hnt_tail hres_tail
  set t1 := setVarHOLFinite (ofString "payload_len") (.val (.word payw)) st_fin
  have heff_t1 : HeapByteEff ent t1 Rbuf ["heap_ptr"] := heff_fin.locals_clock t1.locals t1.clock
  have ht1_pay : t1.locals.lookup (ofString "payload_len") = some (.val (.word payw)) := by
    simp [t1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have ht1_buf : t1.locals.lookup (ofString "buf") = some (.val (.word buf)) := by
    simp [t1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hfin_buf,
      show ofString "payload_len" ≠ ofString "buf" by decide]
  obtain ⟨t2, hhl_nat, hhl1, hhl9, ht2_g, ht2_m, ht2_loc, heff_t12, hnt_t2, heq_lhl⟩ :=
    eval_decCall_rlp_list_header_len t1 "hl" (.var .local (ofString "payload_len")) payw _ Rbuf ["heap_ptr"]
      heff_t1.arena.1.code heff_t1.arena ht1_pay hnt_tail
  rw [heq_lhl] at hres_tail; dsimp only at hres_tail
  set hlw := BitVec.ofNat 64 (rlpHeaderLenPure payw.toNat)
  have heff_t2 : HeapByteEff ent t2 Rbuf ["heap_ptr"] := heff_t1.trans heff_t12
  have ht2_hl : t2.locals.lookup (ofString "hl") = some (.val (.word hlw)) := by
    rw [ht2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have ht2_pay : t2.locals.lookup (ofString "payload_len") = some (.val (.word payw)) := by
    rw [ht2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, ht1_pay,
      show ofString "hl" ≠ ofString "payload_len" by decide]
  have ht2_buf : t2.locals.lookup (ofString "buf") = some (.val (.word buf)) := by
    rw [ht2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, ht1_buf,
      show ofString "hl" ≠ ofString "buf" by decide]
  rw [evaluateHOLFiniteState_dec_total] at hnt_t2 hres_tail
  let startw : BitVec 64 := p0 - hlw
  have hstart_nat : startw.toNat = buf.toNat + 9 - hlw.toNat := by
    change (p0 - hlw).toNat = buf.toNat + 9 - hlw.toNat
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega)), hp0_nat]
  have hev_start : @evalHOLExact 64 F _ t2.toExact
      (fun a => Classical.propDecidable (t2.memaddrs a))
      (.op .sub [.op .add [.var .local (ofString "buf"), .const 9], .var .local (ofString "hl")]) =
      some (.val (.word startw)) := by
    simp [evalHOLExact, evalListHOLExact, ht2_buf, ht2_hl, wordOpHOL, wordOp, valueIsWord, valueWord, startw, p0]
  have hsh_start : shapeEqHOL .one (shapeOfHOLExact (.val (.word startw) : ValueHOL 64)) = true := by
    simp [shapeOfHOLExact, shapeEqHOL]
  dsimp only at hnt_t2 hres_tail
  rw [hev_start] at hnt_t2 hres_tail; dsimp only at hnt_t2 hres_tail
  rw [if_pos hsh_start] at hnt_t2 hres_tail
  set t3 := setVarHOLFinite (ofString "start") (.val (.word startw)) t2
  have heff_t3 : HeapByteEff ent t3 Rbuf ["heap_ptr"] := heff_t2.locals_clock t3.locals t3.clock
  have ht3_start : t3.locals.lookup (ofString "start") = some (.val (.word startw)) := by
    simp [t3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have ht3_pay : t3.locals.lookup (ofString "payload_len") = some (.val (.word payw)) := by
    simp [t3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht2_pay,
      show ofString "start" ≠ ofString "payload_len" by decide]
  have ht3_hl : t3.locals.lookup (ofString "hl") = some (.val (.word hlw)) := by
    simp [t3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ht2_hl,
      show ofString "start" ≠ ofString "hl" by decide]
  rw [evaluateHOLFiniteState_seq_line780] at hnt_t2 hres_tail
  rcases hc_lh : evaluateHOLFiniteState t3
    (.call (some (none, none)) (ofString "rlp_encode_list_header")
      [.var .local (ofString "start"), .var .local (ofString "payload_len")]) with ⟨rlh, t4⟩
  have hnt_lh : rlh ≠ some .timeOut := by
    rintro rfl; rw [hc_lh] at hnt_t2; exact hnt_t2 rfl
  have hlh := eval_call_rlp_encode_list_header t3
    (.var .local (ofString "start")) (.var .local (ofString "payload_len"))
    startw payw Rbuf [] heff_t3.arena.1.code heff_t3.arena ht3_start ht3_pay
    ⟨(buf.toNat, 1024), List.mem_singleton.mpr rfl, by omega, by omega⟩
    (by rw [hc_lh]; exact hnt_lh)
  dsimp only at hlh; rw [hc_lh] at hlh
  simp only [hc_lh] at hnt_t2 hres_tail
  cases rlh with
  | some _ =>
    exfalso
    exact hlh.2 (by simp) hres_tail
  | none =>
    dsimp only at hnt_t2 hres_tail
    obtain ⟨_, heff_t34, ht4_loc⟩ := hlh.1 rfl
    have heff_t4 : HeapByteEff ent t4 Rbuf ["heap_ptr"] :=
      heff_t3.trans (heff_t34.mono (fun i hi _ => Or.inl ⟨i, hi, le_rfl, le_rfl⟩) (fun _ h => by cases h))
    have ht4_start : t4.locals.lookup (ofString "start") = some (.val (.word startw)) := by
      rw [ht4_loc]; exact ht3_start
    have ht4_pay : t4.locals.lookup (ofString "payload_len") = some (.val (.word payw)) := by
      rw [ht4_loc]; exact ht3_pay
    have ht4_hl : t4.locals.lookup (ofString "hl") = some (.val (.word hlw)) := by
      rw [ht4_loc]; exact ht3_hl
    let totalw : BitVec 64 := payw + hlw
    have hret_t4 : evaluateHOLFiniteState t4
        (.return (.rstruct [.var .local (ofString "start"),
          .op .add [.var .local (ofString "payload_len"), .var .local (ofString "hl")]])) =
        (some (.returned (.rStruct [.val (.word startw), .val (.word totalw)])),
         t4.emptyLocalsHOLFinite) := by
      rw [evaluateHOLFiniteState_return]
      have hev_ret : @evalHOLExact 64 F _ t4.toExact
          (fun a => Classical.propDecidable (t4.memaddrs a))
          (.rstruct [.var .local (ofString "start"),
            .op .add [.var .local (ofString "payload_len"), .var .local (ofString "hl")]]) =
          some (.rStruct [.val (.word startw), .val (.word totalw)]) := by
        simp [evalHOLExact, evalListHOLExact, ht4_start, ht4_pay, ht4_hl,
          wordOpHOL, wordOp, valueIsWord, valueWord, totalw]
      rw [hev_ret]; dsimp only
      have hsz : sizeOfShapeWithContextHOL t4.structs
          (shapeOfHOLExact (.rStruct [.val (.word startw), .val (.word totalw)] : ValueHOL 64)) ≤ 32 := by
        simp [shapeOfHOLExact]
      rw [if_pos hsz]
    have htail_eq : evaluateHOLFiniteState st_fin tailProg =
        (some (.returned (.rStruct [.val (.word startw), .val (.word totalw)])),
         { t4.emptyLocalsHOLFinite with
           locals := HolFiniteMapExact.resVarEq
             (HolFiniteMapExact.resVarEq
               (HolFiniteMapExact.resVarEq t4.emptyLocalsHOLFinite.locals
                 (ofString "start", t2.locals.lookup (ofString "start")))
               (ofString "hl", t1.locals.lookup (ofString "hl")))
             (ofString "payload_len", st_fin.locals.lookup (ofString "payload_len")) }) := by
      dsimp only [tailProg]
      rw [evaluateHOLFiniteState_dec_total]; dsimp only
      rw [hev_pay]; dsimp only; rw [if_pos hsh_pay]
      rw [heq_lhl]; dsimp only
      rw [evaluateHOLFiniteState_dec_total]; dsimp only
      rw [hev_start]; dsimp only; rw [if_pos hsh_start]
      rw [evaluateHOLFiniteState_seq_line780, hc_lh]; dsimp only
      rw [hret_t4]
    have hst1_eq :=
      heq_2.trans (heq_3.trans (heq_4.trans (heq_5.trans (heq_6.trans (heq_7.trans
        (heq_8.trans (heq_9.trans (heq_10.trans (heq_11.trans (heq_12.trans (heq_13.trans
          (heq_14.trans (heq_15.trans (heq_16.trans (heq_17.trans (heq_18.trans (heq_19.trans
            (heq_20.trans (heq_21.trans heq_ite)))))))))))))))))))
    have hseq_step : ∀ (p2 : ProgHOL 64),
        evaluateHOLFiniteState s3a
          (.seq (.assign .local (ofString "p") (.op .add [.var .local (ofString "p"), .var .local (ofString "w")])) p2) =
        evaluateHOLFiniteState st1 p2 := by
      intro p2
      rw [evaluateHOLFiniteState_seq_line780, hass1]
    have hs3a_eq := (hseq_step _).trans (hst1_eq.trans htail_eq)
    have hres_wrap : ∀ {r1 r2 : Option (PanSemResultExact 64)} {q1 q2 : PanSemStateFiniteExact 64 F}
        (k : MlS) (old : Option (ValueHOL 64)),
        (r1, q1) = (r2, q2) →
        (r1, { q1 with locals := HolFiniteMapExact.resVarEq q1.locals (k, old) }) =
        (r2, { q2 with locals := HolFiniteMapExact.resVarEq q2.locals (k, old) }) := by
      intro _ _ _ _ _ _ h; cases h; rfl
    have hs2_eq := heq3a.trans (hres_wrap (ofString "w") (s2.locals.lookup (ofString "w")) hs3a_eq)
    have hdec_step : ∀ (p_body : ProgHOL 64),
        evaluateHOLFiniteState s1 (.dec (ofString "p") .one (.op .add [.var .local (ofString "buf"), .const 9]) p_body) =
        ((evaluateHOLFiniteState s2 p_body).1,
         { (evaluateHOLFiniteState s2 p_body).2 with
           locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState s2 p_body).2.locals
             (ofString "p", s1.locals.lookup (ofString "p")) }) := by
      intro p_body
      rw [evaluateHOLFiniteState_dec_total]; dsimp only
      rw [hev_p0]; dsimp only; rw [if_pos hsh_p0]
    have hs1_eq := (hdec_step _).trans (hres_wrap (ofString "p") (s1.locals.lookup (ofString "p")) hs2_eq)
    have hfinal_eq := heq1.trans (hres_wrap (ofString "buf") (ent.locals.lookup (ofString "buf")) hs1_eq)
    have heff_t4_nil : HeapByteEff ent t4.emptyLocalsHOLFinite [] ["heap_ptr"] := by
      have hm : HeapByteEff ent t4 [] ["heap_ptr"] :=
        heff_t4.mono
          (fun i hi _ => by
            simp only [Rbuf, List.mem_singleton] at hi; subst hi
            exact Or.inr (Or.inr ⟨by omega, by omega⟩))
          (fun _ h => h)
      exact hm.locals_clock _ _
    exact ⟨startw, totalw, t4.emptyLocalsHOLFinite, _, heff_t4_nil, hfinal_eq⟩

theorem eval_decCall_encode_header {F : Type}
    (s : PanSemStateFiniteExact 64 F) (lname : String) (hExp : ExpHOL 64)
    (hw : BitVec 64) (cont : ProgHOL 64) (Rl : List Ivl) (gw : List String)
    (hcode : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hgw : "heap_ptr" ∈ gw)
    (hh_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) hExp =
      some (.val (.word hw)))
    (hH : HeaderAtStrong s hw.toNat)
    (hnt : (evaluateHOLFiniteState s
      (.decCall (ofString lname) (.comb [.one, .one]) (ofString "encode_header") [hExp] cont)).1 ≠
      some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s
      (.decCall (ofString lname) (.comb [.one, .one]) (ofString "encode_header") [hExp] cont)).1) :
    ∃ (startw totalw : BitVec 64) (mid : PanSemStateFiniteExact 64 F),
      mid.locals = s.locals.update (ofString lname,
        .rStruct [.val (.word startw), .val (.word totalw)]) ∧
      HeapByteEff s mid Rl gw ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState mid cont).1 ∧
      evaluateHOLFiniteState s
        (.decCall (ofString lname) (.comb [.one, .one]) (ofString "encode_header") [hExp] cont) =
        ((evaluateHOLFiniteState mid cont).1,
         { (evaluateHOLFiniteState mid cont).2 with
           locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState mid cont).2.locals
             (ofString lname, s.locals.lookup (ofString lname)) }) := by
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt hres ⊢
  have ha : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [hExp] =
      some [.val (.word hw)] := by simp [evalListHOLFinite, evalListHOLExact, hh_ev]
  have hlk := pan_one_word_lookup_any s.code.lookup (ofString "encode_header") (ofString "h")
    (sourceFnBody Guest.Software.guestFn_encode_header) (.comb [.one, .one]) hw
    (by rw [hcode]; exact lookup_encode_header)
  simp only [ha, hlk] at hnt hres ⊢
  by_cases hcz : s.clock = 0
  · simp [hcz] at hnt
  · simp only [hcz, ↓reduceIte] at hnt hres ⊢
    set cmap := HolFiniteMapExact.empty.update (ofString "h", ValueHOL.val (.word hw))
    set ent := callEntryStateHOLFinite s cmap
    have hAR_ent : ArenaReady ent := ⟨guestInv_callEntry s cmap hAR.1, hAR.2⟩
    have hent_h : ent.locals.lookup (ofString "h") = some (.val (.word hw)) := by
      simp [ent, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hH_ent : HeaderAtStrong ent hw.toNat :=
      (headerAtStrong_with_locals s ent.locals ent.clock hw.toNat).2 hH
    rcases henc : evaluateHOLFiniteState ent (sourceFnBody Guest.Software.guestFn_encode_header) with ⟨renc, senc⟩
    have hnt_enc : renc ≠ some .timeOut := by
      rintro rfl; rw [henc] at hnt; exact hnt rfl
    have hres_enc : Resumes renc := by
      cases renc with
      | none => simp [henc] at hres; exact False.elim (not_resumes_error hres)
      | some r =>
        cases r with
        | returned rv => exact Or.inl ⟨rv, rfl⟩
        | exception eid ev =>
          simp only [henc] at hres
          rcases hres with ⟨_, h⟩ | ⟨e', v', h, hne⟩
          · simp at h
          · injection h with h'; injection h' with he1 he2; subst he1 he2
            exact Or.inr ⟨eid, ev, rfl, hne⟩
        | timeOut => exact absurd rfl hnt_enc
        | finalFfi _ =>
          simp only [henc] at hres
          rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
        | _ => simp [henc] at hres; exact False.elim (not_resumes_error hres)
    obtain ⟨startw, totalw, q, L, heff_ent_q, hbody_eq⟩ :=
      eval_encode_header_body (show ent.code = originalRuntimeCode from hcode) hAR_ent hH_ent hent_h
        (by rw [henc]; exact hnt_enc) (by rw [henc]; exact hres_enc)
    rw [henc] at hbody_eq
    injection hbody_eq with hr_eq hs_eq
    subst hr_eq hs_eq
    let rv : ValueHOL 64 := .rStruct [.val (.word startw), .val (.word totalw)]
    have hsh : (shapeEqHOL (shapeOfHOLExact rv) (.comb [.one, .one]) &&
        shapeEqHOL (shapeOfHOLExact rv) (.comb [.one, .one])) = true := by
      simp [rv, shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL]
    change (shapeEqHOL
          (shapeOfHOLExact (.rStruct [.val (.word startw), .val (.word totalw)]))
          (.comb [.one, .one]) &&
        shapeEqHOL
          (shapeOfHOLExact (.rStruct [.val (.word startw), .val (.word totalw)]))
          (.comb [.one, .one])) = true at hsh
    simp only [henc, hsh, ↓reduceIte] at hnt hres ⊢
    let mid := setVarHOLFinite (ofString lname) rv { q with locals := s.locals }
    have heff_s_ent : HeapByteEff s ent [] ["heap_ptr"] :=
      (HeapByteEff.refl hAR [] ["heap_ptr"]).locals_clock ent.locals ent.clock
    have heff_s_mid_nil : HeapByteEff s mid [] ["heap_ptr"] :=
      (heff_s_ent.trans heff_ent_q).locals_clock mid.locals mid.clock
    have heff_s_mid : HeapByteEff s mid Rl gw :=
      heff_s_mid_nil.mono
        (fun _ h => by cases h)
        (fun g hg => by simp at hg; subst hg; exact hgw)
    exact ⟨startw, totalw, mid, rfl, heff_s_mid, hnt, hres, rfl⟩

/-- `header_hash` (AST line 9460) relational world step under `WorldOK s ∧ HeaderOKStrong s`
(`HeaderAt s h ∧ Inside (h, 248) sourceBase (globN s "heap_ptr")`). -/
theorem «wk_header_hash_inside» :
    WorldKeeps (fun s => WorldOK s ∧ HeaderOKStrong s)
      (fun s => [(locN s "out", 32),
        (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
        (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "header_hash") := by
  refine ⟨_, _, _, lookup_header_hash, fun {F} s hcode ⟨hW, hHOK⟩ hparams hnt hres => ?_⟩
  have hAR : ArenaReady s := hW.1
  have hhl264 : heapLimit < 2 ^ 64 := by rw [heapLimit_val]; decide
  obtain ⟨vals, hl_args⟩ := hparams
  obtain ⟨hw, out0, _, hh_lk, hout⟩ :=
    R13Shards.Keccak256.lookupCode_two_words (by decide) lookup_header_hash hl_args
  have hh_locN : locN s "h" = hw.toNat := by simp [locN, hh_lk]
  have hout_locN : locN s "out" = out0.toNat := by simp [locN, hout]
  have hH : HeaderAtStrong s hw.toNat := by rwa [HeaderOKStrong, hh_locN] at hHOK
  let Rs : List Ivl :=
    [(locN s "out", 32),
     (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
     (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)]
  suffices hmain : HeapByteEff s
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_header_hash)).2
      (Rs ++ ([] : List (String × Nat)).map (bufferRegion s)) ["heap_ptr"] by
    exact hmain.to_worldStep (R := fun t =>
        [(locN t "out", 32),
         (globN t "keccak_pad", if globN t "keccak_pad" = 0 then 0 else 136),
         (globN t "keccak_st", if globN t "keccak_st" = 0 then 0 else 200)])
      (B := [])
      (by intro _ h; cases h)
      (by intro g hg; simp at hg; exact Or.inl hg)
      hW (fun _ _ _ _ _ => trivial)
  have hb : sourceFnBody Guest.Software.guestFn_header_hash =
      .decCall (ofString "mark") .one (ofString "heap_mark") []
        (.decCall (ofString "e") (.comb [.one, .one]) (ofString "encode_header")
          [.var .local (ofString "h")]
          (.seq
            (.call (some (none, none)) (ofString "keccak256")
              [.rfield 0 (.var .local (ofString "e")),
               .rfield 1 (.var .local (ofString "e")),
               .var .local (ofString "out")])
            (.seq
              (.call (some (none, none)) (ofString "heap_release")
                [.var .local (ofString "mark")])
              (.return (.const 0))))) := rfl
  rw [hb] at hnt hres ⊢
  set Rall : List Ivl := Rs ++ ([] : List (String × Nat)).map (bufferRegion s)
  -- Step 1: `var 1 mark = heap_mark()`
  obtain ⟨mark, s1, hhp_s, hmark_nat, hs1_g, hs1_m, hs1_loc, heff01_nil, hnt1, heq1⟩ :=
    eval_decCall_heap_mark s "mark" _ ([] : List Ivl) ["heap_ptr"] hcode hAR hnt
  have heff01 : HeapByteEff s s1 Rall ["heap_ptr"] :=
    heff01_nil.mono (fun _ h => by cases h) (fun _ h => h)
  rw [heq1] at hres; dsimp only at hres
  refine heapByteEff_of_eq_resVar_hh heq1 ?_
  have hs1_mark : s1.locals.lookup (ofString "mark") = some (.val (.word mark)) := by
    rw [hs1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hs1_h : s1.locals.lookup (ofString "h") = some (.val (.word hw)) := by
    rw [hs1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hh_lk,
      show ofString "mark" ≠ ofString "h" by decide]
  have hs1_out : s1.locals.lookup (ofString "out") = some (.val (.word out0)) := by
    rw [hs1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hout,
      show ofString "mark" ≠ ofString "out" by decide]
  have hH_s1 : HeaderAtStrong s1 hw.toNat := by
    have hu : IvlUnhit s s1 (hw.toNat, 248) :=
      ivlUnhit_of_heapByteEff_below_hp hAR heff01_nil hH.2 (fun _ h => by cases h)
    exact headerAtStrong_of_ivlUnhit hAR.1 heff01.arena.1 heff01.hp_le
      (by have := hH.2.2; have := hAR.2.2.1; omega) hu hH
  -- Step 2: `var {1, 1} e = encode_header(h)`
  obtain ⟨startw, totalw, s2, hs2_loc, heff12, hnt2, hres2, heq2⟩ :=
    eval_decCall_encode_header s1 "e" (.var .local (ofString "h")) hw _ Rall ["heap_ptr"]
      heff01.arena.1.code heff01.arena (by simp) hs1_h hH_s1 hnt1 hres
  refine heapByteEff_of_eq_resVar_hh heq2 ?_
  have heff02 : HeapByteEff s s2 Rall ["heap_ptr"] := heff01.trans heff12
  have hs2_e : s2.locals.lookup (ofString "e") =
      some (.rStruct [.val (.word startw), .val (.word totalw)]) := by
    rw [hs2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hs2_mark : s2.locals.lookup (ofString "mark") = some (.val (.word mark)) := by
    rw [hs2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs1_mark,
      show ofString "e" ≠ ofString "mark" by decide]
  have hs2_out : s2.locals.lookup (ofString "out") = some (.val (.word out0)) := by
    rw [hs2_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs1_out,
      show ofString "e" ≠ ofString "out" by decide]
  have hkpad_eq : globN s2 "keccak_pad" = globN s "keccak_pad" := by
    unfold globN
    rw [← heff02.globals (ofString "keccak_pad") (by decide)]
  have hkst_eq : globN s2 "keccak_st" = globN s "keccak_st" := by
    unfold globN
    rw [← heff02.globals (ofString "keccak_st") (by decide)]
  -- Step 3: `keccak256(e.0, e.1, out)`
  rw [evaluateHOLFiniteState_seq_line780] at hnt2 hres2
  rcases hc3 : evaluateHOLFiniteState s2
    (.call (some (none, none)) (ofString "keccak256")
      [.rfield 0 (.var .local (ofString "e")),
       .rfield 1 (.var .local (ofString "e")),
       .var .local (ofString "out")]) with ⟨r3, s3⟩
  have hnt_c3 : r3 ≠ some .timeOut := by
    rintro rfl; rw [hc3] at hnt2; exact hnt2 rfl
  have hor_c3 : r3 = none ∨ Resumes r3 := by
    cases r3 with
    | none => exact Or.inl rfl
    | some rk =>
      right
      rw [hc3] at hres2; dsimp only at hres2
      exact hres2
  have h3 := eval_call_keccak256_heap s2
    (.rfield 0 (.var .local (ofString "e")))
    (.rfield 1 (.var .local (ofString "e")))
    (.var .local (ofString "out"))
    startw totalw out0 Rall [] heff02.arena.1.code heff02.arena
    (by simp [evalHOLExact, hs2_e])
    (by simp [evalHOLExact, hs2_e])
    hs2_out
    ⟨(locN s "out", 32), by simp [Rall, Rs], by rw [hout_locN], by rw [hout_locN]⟩
    (fun hnz => by
      rw [hkpad_eq] at hnz ⊢
      exact ⟨(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
        by simp [Rall, Rs], le_rfl, by simp [hnz]⟩)
    (fun hnz => by
      rw [hkst_eq] at hnz ⊢
      exact ⟨(globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
        by simp [Rall, Rs], le_rfl, by simp [hnz]⟩)
    (by rw [hc3]; exact hnt_c3)
    (by rw [hc3]; exact hor_c3)
  rw [hc3] at h3 hnt2 hres2
  cases r3 with
  | some _ =>
    refine heapByteEff_of_seq_some_hh hc3 ?_
    exact heff02.trans (h3.1.mono (fun i hi _ => Or.inl ⟨i, hi, le_rfl, le_rfl⟩) (fun _ h => by cases h))
  | none =>
    dsimp only at hnt2 hres2
    refine heapByteEff_of_seq_none_hh hc3 ?_
    obtain ⟨hs3_loc, _⟩ := h3.2 rfl
    have hs3_mark : s3.locals.lookup (ofString "mark") = some (.val (.word mark)) := by
      rw [hs3_loc]; exact hs2_mark
    have heff03 : HeapByteEff s s3 Rall ["heap_ptr"] :=
      heff02.trans (h3.1.mono (fun i hi _ => Or.inl ⟨i, hi, le_rfl, le_rfl⟩) (fun _ h => by cases h))
    -- Step 4: `heap_release(mark)`
    rw [evaluateHOLFiniteState_seq_line780] at hnt2 hres2
    rcases hc4 : evaluateHOLFiniteState s3
      (.call (some (none, none)) (ofString "heap_release")
        [.var .local (ofString "mark")]) with ⟨r4, s4⟩
    have hnt_c4 : r4 ≠ some .timeOut := by
      rintro rfl; rw [hc4] at hnt2; exact hnt2 rfl
    have h4 := eval_call_heap_release s3 (.var .local (ofString "mark")) mark
      Rall ["heap_ptr"] heff03.arena.1.code heff03 (by simp) hs3_mark
      (by rw [hmark_nat]) (by rw [hmark_nat]; exact hAR.2.1)
      (by rw [hmark_nat]; exact hAR.2.2.1)
      (by rw [hmark_nat]; exact hAR.2.2.2.2.2.2.1) (by rw [hc4]; exact hnt_c4)
    dsimp only at h4
    rw [hc4] at h4
    obtain ⟨rfl, _, _, _, heff04⟩ := h4
    refine heapByteEff_of_seq_none_hh hc4 ?_
    have heff_ret : HeapByteEff s4 (evaluateHOLFiniteState s4 (.return (.const 0))).2 Rall ["heap_ptr"] :=
      HeapByteEff.of_byteEff heff04.arena
        (R13Shards.Keccak256.byteEff_return s4 (.const 0) Rall)
    exact heff04.trans heff_ret

/-- Caller-disjointness variant of `wk_header_hash_inside` (adding explicit disjointness of
`(out, 32)` from `(h, 248) :: headerSlices s h`). -/
theorem «wk_header_hash_strong» :
    WorldKeeps
      (fun s => WorldOK s ∧ HeaderOKStrong s ∧
        IvlsDisj [(locN s "out", 32)] ((locN s "h", 248) :: headerSlices s (locN s "h")))
      (fun s => [(locN s "out", 32),
        (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
        (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "header_hash") := by
  obtain ⟨params, body, rs, hlk, hbody⟩ := wk_header_hash_inside
  exact ⟨params, body, rs, hlk, fun s hcode ⟨hW, hH, _⟩ hparams hnt hres =>
    hbody s hcode ⟨hW, hH⟩ hparams hnt hres⟩

end InitECandidate.Solver.Wave8GuestInv.R16Shards.HeaderHashRecover
