import InitECandidate.Solver.Wave8GuestInv.R10Shards.P13DivMod
import InitECandidate.Solver.Wave8GuestInv.R10Shards.FastGen.FG_13

/-! Standalone bounded termination proofs on `GuestInv` for:
- `fb_bn_mul` (`guestFn_bn_mul`, AST index 626)
- `fb_bn_divmnu` (`guestFn_bn_divmnu`, AST index 627)
- `fb_bn_mod` (`guestFn_bn_mod`, AST index 628)
- `fb_modexp` (`guestFn_modexp`, AST index 630)

Zero `LeafStatements.lean` dependency, standard Lean kernel foundations only. -/

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.R16ArithPort

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup InitECandidate.Solver.GuestUniformClockBound
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.P13.Common
open InitECandidate.Solver.Wave8GuestInv.P13.Callees
open InitECandidate.Solver.Wave8GuestInv.P13.DivMod

/-! ### 1. Scaled-8 ordinary-domain memory walks -/

private theorem evaluate_seq_split {F : Type} (s : PanSemStateFiniteExact 64 F) (p1 p2 : ProgHOL 64) :
    evaluateHOLFiniteState s (.seq p1 p2) =
      match (evaluateHOLFiniteState s p1).1 with
      | none => evaluateHOLFiniteState (evaluateHOLFiniteState s p1).2 p2
      | some v => (some v, (evaluateHOLFiniteState s p1).2) := by
  rw [evaluateHOLFiniteState_seq_line780]
  rcases evaluateHOLFiniteState s p1 with ⟨r, m⟩
  cases r <;> rfl

def scaled8UpRank (a : BitVec 64) : Nat :=
  if sourceBase ≤ a.toNat ∧ a.toNat < heapEnd then heapEnd - a.toNat + 15 else 0

theorem scaled8UpRank_bound (a : BitVec 64) : scaled8UpRank a ≤ domainBytes + 16 := by
  unfold scaled8UpRank domainBytes
  split_ifs <;> omega

theorem scaled8UpRank_add8_lt (a : BitVec 64) (ha : sourceBase ≤ a.toNat ∧ a.toNat < heapEnd) :
    scaled8UpRank (a + BitVec.ofNat 64 8) < scaled8UpRank a := by
  have hend : heapEnd + 8 < 2 ^ 64 := by decide
  have hadd : (a + BitVec.ofNat 64 8).toNat = a.toNat + 8 := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  unfold scaled8UpRank
  rw [if_pos ha, hadd]
  split_ifs <;> omega

def scaled8UpMu (base counter : MlS) {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat :=
  match s.locals.lookup base, s.locals.lookup counter with
  | some (.val (.word b)), some (.val (.word i)) => scaled8UpRank (b + i * 8)
  | _, _ => 0

theorem scaled8UpMu_le (base counter : MlS) {F : Type} (s : PanSemStateFiniteExact 64 F) :
    scaled8UpMu base counter s ≤ domainBytes + 16 := by
  unfold scaled8UpMu
  split
  · exact scaled8UpRank_bound _
  · omega

def scaled8DownRank16 (a : BitVec 64) : Nat :=
  if sourceBase ≤ a.toNat ∧ a.toNat < heapEnd then a.toNat - sourceBase + 16 else 0

theorem scaled8DownRank16_bound (a : BitVec 64) : scaled8DownRank16 a ≤ domainBytes + 16 := by
  unfold scaled8DownRank16 domainBytes
  split_ifs <;> omega

theorem scaled8DownRank16_sub8_lt (a : BitVec 64) (ha : sourceBase ≤ a.toNat ∧ a.toNat < heapEnd) :
    scaled8DownRank16 (a - BitVec.ofNat 64 8) < scaled8DownRank16 a := by
  have hs : 8 ≤ sourceBase := by decide
  have hsub : (a - BitVec.ofNat 64 8).toNat = a.toNat - 8 := by
    rw [BitVec.toNat_sub]
    change (18446744073709551616 - 8 + a.toNat) % 18446744073709551616 = a.toNat - 8
    have := a.isLt
    omega
  unfold scaled8DownRank16
  rw [if_pos ha, hsub]
  split_ifs <;> omega

def scaled8DownMu16 (base counter : MlS) {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat :=
  match s.locals.lookup base, s.locals.lookup counter with
  | some (.val (.word b)), some (.val (.word i)) => scaled8DownRank16 (b + i * 8)
  | _, _ => 0

theorem scaled8DownMu16_le (base counter : MlS) {F : Type} (s : PanSemStateFiniteExact 64 F) :
    scaled8DownMu16 base counter s ≤ domainBytes + 16 := by
  unfold scaled8DownMu16
  split
  · exact scaled8DownRank16_bound _
  · omega

def scaled8PreDecDownMu (base counter : MlS) {F : Type}
    (s : PanSemStateFiniteExact 64 F) : Nat :=
  match s.locals.lookup base, s.locals.lookup counter with
  | some (.val (.word b)), some (.val (.word j)) =>
    scaled8DownRank16 (b + (j - 1) * 8)
  | _, _ => 0

theorem scaled8PreDecDownMu_le (base counter : MlS) {F : Type}
    (s : PanSemStateFiniteExact 64 F) :
    scaled8PreDecDownMu base counter s ≤ domainBytes + 16 := by
  unfold scaled8PreDecDownMu
  split
  · exact scaled8DownRank16_bound _
  · omega

/-- Tight cell-counting downward rank (`domainBytes / 8 + 2`) for `bn_divmnu` Loop #3. -/
def scaled8CellDownRank (a : BitVec 64) : Nat :=
  if sourceBase ≤ a.toNat ∧ a.toNat < heapEnd then (a.toNat - sourceBase) / 8 + 1 else 0

theorem scaled8CellDownRank_bound (a : BitVec 64) : scaled8CellDownRank a ≤ domainBytes / 8 + 2 := by
  unfold scaled8CellDownRank domainBytes
  split_ifs <;> omega

theorem scaled8CellDownRank_sub8_lt (a : BitVec 64) (ha : sourceBase ≤ a.toNat ∧ a.toNat < heapEnd) :
    scaled8CellDownRank (a - BitVec.ofNat 64 8) < scaled8CellDownRank a := by
  have hs : 8 ≤ sourceBase := by decide
  have hsub : (a - BitVec.ofNat 64 8).toNat = a.toNat - 8 := by
    rw [BitVec.toNat_sub]
    change (18446744073709551616 - 8 + a.toNat) % 18446744073709551616 = a.toNat - 8
    have := a.isLt
    omega
  unfold scaled8CellDownRank
  rw [if_pos ha, hsub]
  split_ifs <;> omega

def scaled8PreDecAddCellMu (base counter off : MlS) {F : Type}
    (s : PanSemStateFiniteExact 64 F) : Nat :=
  match s.locals.lookup base, s.locals.lookup counter, s.locals.lookup off with
  | some (.val (.word b)), some (.val (.word j)), some (.val (.word n)) =>
    scaled8CellDownRank (b + ((j - 1) + n) * 8)
  | _, _, _ => 0

theorem scaled8PreDecAddCellMu_le (base counter off : MlS) {F : Type}
    (s : PanSemStateFiniteExact 64 F) :
    scaled8PreDecAddCellMu base counter off s ≤ domainBytes / 8 + 2 := by
  unfold scaled8PreDecAddCellMu
  split
  · exact scaled8CellDownRank_bound _
  · omega

def scaled8AddUpMu (base counter off : MlS) {F : Type}
    (s : PanSemStateFiniteExact 64 F) : Nat :=
  match s.locals.lookup base, s.locals.lookup counter, s.locals.lookup off with
  | some (.val (.word b)), some (.val (.word i)), some (.val (.word j)) =>
    scaled8UpRank (b + (i + j) * 8)
  | _, _, _ => 0

theorem scaled8AddUpMu_le (base counter off : MlS) {F : Type}
    (s : PanSemStateFiniteExact 64 F) :
    scaled8AddUpMu base counter off s ≤ domainBytes + 16 := by
  unfold scaled8AddUpMu
  split
  · exact scaled8UpRank_bound _
  · omega

private theorem scaled8_locals_inv' {F : Type} (s : PanSemStateFiniteExact 64 F)
    (base counter : MlS) (address : BitVec 64)
    (h : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .local base, .panop .mul [.var .local counter, .const 8#64]]) =
      some (.val (.word address))) :
    ∃ b i : BitVec 64, s.locals.lookup base = some (.val (.word b)) ∧
      s.locals.lookup counter = some (.val (.word i)) ∧ address = b + i * 8 := by
  cases hb : s.locals.lookup base with
  | none => simp [evalHOLExact, evalListHOLExact, hb] at h
  | some bv =>
    cases bv with
    | rStruct _ =>
      cases hi : s.locals.lookup counter with
      | none => simp [evalHOLExact, evalListHOLExact, hb, hi] at h
      | some v =>
        cases v with
        | val w => cases w; simp [evalHOLExact, evalListHOLExact, hb, hi, valueIsWord, valueWord, panOpHOL] at h
        | rStruct _ => simp [evalHOLExact, evalListHOLExact, hb, hi, valueIsWord] at h
        | nStruct _ _ => simp [evalHOLExact, evalListHOLExact, hb, hi, valueIsWord] at h
    | nStruct _ _ =>
      cases hi : s.locals.lookup counter with
      | none => simp [evalHOLExact, evalListHOLExact, hb, hi] at h
      | some v =>
        cases v with
        | val w => cases w; simp [evalHOLExact, evalListHOLExact, hb, hi, valueIsWord, valueWord, panOpHOL] at h
        | rStruct _ => simp [evalHOLExact, evalListHOLExact, hb, hi, valueIsWord] at h
        | nStruct _ _ => simp [evalHOLExact, evalListHOLExact, hb, hi, valueIsWord] at h
    | val bw =>
      cases bw with
      | word b =>
        cases hi : s.locals.lookup counter with
        | none => simp [evalHOLExact, evalListHOLExact, hb, hi] at h
        | some iv =>
          cases iv with
          | rStruct _ => simp [evalHOLExact, evalListHOLExact, hb, hi, valueIsWord] at h
          | nStruct _ _ => simp [evalHOLExact, evalListHOLExact, hb, hi, valueIsWord] at h
          | val iw =>
            cases iw with
            | word i =>
              refine ⟨b, i, rfl, rfl, ?_⟩
              simpa [evalHOLExact, evalListHOLExact, hb, hi, valueIsWord, valueWord,
                wordOpHOL, wordOp, panOpHOL] using h.symm

private theorem scaled8_add_locals_inv {F : Type} (s : PanSemStateFiniteExact 64 F)
    (base counter off : MlS) (address : BitVec 64)
    (h : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .local base, .panop .mul [.op .add [.var .local counter, .var .local off], .const 8#64]]) =
      some (.val (.word address))) :
    ∃ b j n : BitVec 64, s.locals.lookup base = some (.val (.word b)) ∧
      s.locals.lookup counter = some (.val (.word j)) ∧
      s.locals.lookup off = some (.val (.word n)) ∧
      address = b + (j + n) * 8 := by
  simp only [evalHOLExact] at h
  rcases he : @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local base, .panop .mul [.op .add [.var .local counter, .var .local off], .const 8#64]] with _ | vals
  · simp [he] at h
  · rw [he] at h
    rcases he1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) (.var .local base) with _ | v1
    · simp [evalListHOLExact, he1] at he
    · rcases he2 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
          (.panop .mul [.op .add [.var .local counter, .var .local off], .const 8#64]) with _ | v2
      · simp [evalListHOLExact, he1, he2] at he
      · have hvals : vals = [v1, v2] := by simpa [evalListHOLExact, he1, he2] using he.symm
        subst hvals
        cases v1 with
        | rStruct _ => simp [wordOpHOL, valueIsWord] at h
        | nStruct _ _ => simp [wordOpHOL, valueIsWord] at h
        | val w1 =>
          cases w1 with
          | word b =>
            have hb : s.locals.lookup base = some (.val (.word b)) := by simpa [evalHOLExact] using he1
            simp only [evalHOLExact] at he2
            rcases hm : @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
                [.op .add [.var .local counter, .var .local off], .const 8#64] with _ | mvals
            · simp [hm] at he2
            · rw [hm] at he2
              rcases ha : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
                  (.op .add [.var .local counter, .var .local off]) with _ | va
              · simp [evalListHOLExact, ha] at hm
              · have hmvals : mvals = [va, .val (.word 8#64)] := by
                  simp only [evalListHOLExact] at hm
                  rw [ha] at hm
                  simpa [evalHOLExact] using hm.symm
                subst hmvals
                simp only [evalHOLExact] at ha
                rcases hc : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) (.var .local counter) with _ | vc
                · simp [evalListHOLExact, hc] at ha
                · rcases ho : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) (.var .local off) with _ | vo
                  · simp [evalListHOLExact, hc, ho] at ha
                  · cases vc with
                    | rStruct _ => simp [evalListHOLExact, hc, ho, wordOpHOL, valueIsWord] at ha
                    | nStruct _ _ => simp [evalListHOLExact, hc, ho, wordOpHOL, valueIsWord] at ha
                    | val wc =>
                      cases wc with
                      | word j =>
                        cases vo with
                        | rStruct _ => simp [evalListHOLExact, hc, ho, wordOpHOL, valueIsWord] at ha
                        | nStruct _ _ => simp [evalListHOLExact, hc, ho, wordOpHOL, valueIsWord] at ha
                        | val wo =>
                          cases wo with
                          | word n =>
                            have hj : s.locals.lookup counter = some (.val (.word j)) := by simpa [evalHOLExact] using hc
                            have hn : s.locals.lookup off = some (.val (.word n)) := by simpa [evalHOLExact] using ho
                            have hva : va = .val (.word (j + n)) := by
                              simpa [evalListHOLExact, hc, ho, wordOpHOL, wordOp, valueIsWord, valueWord] using ha.symm
                            subst hva
                            have hv2 : v2 = .val (.word ((j + n) * 8#64)) := by
                              simpa [valueIsWord, valueWord, panOpHOL] using he2.symm
                            subst hv2
                            refine ⟨b, j, n, hb, hj, hn, ?_⟩
                            simpa [wordOpHOL, wordOp, valueIsWord, valueWord] using h.symm

/-! ### 2. `DomainTouch` helpers for `.load .one` -/

private theorem eval_load_one_domain {F : Type} (s : PanSemStateFiniteExact 64 F)
    (addrExp : ExpHOL 64) (val : ValueHOL 64)
    (h : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.load .one addrExp) = some val) :
    ∃ addr : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        addrExp = some (.val (.word addr)) ∧
      s.memaddrs addr := by
  simp only [evalHOLExact, isWfShapeExactHOL, ↓reduceIte] at h
  split at h
  · rename_i addr haddr
    refine ⟨addr, haddr, ?_⟩
    by_contra hnd
    simp [memLoadHOLExact, hnd] at h
  · cases h

theorem DomainTouch.dec_load_one (name : MlS) (addrExp : ExpHOL 64) (inner : ProgHOL 64) :
    DomainTouch addrExp (.dec name .one (.load .one addrExp) inner) := by
  intro F s hguest hflow
  rw [evaluateHOLFiniteState_dec_total] at hflow
  dsimp only at hflow
  split at hflow
  · simp at hflow
  · rename_i val hval
    obtain ⟨addr, haddr, hdom⟩ := eval_load_one_domain s addrExp val hval
    rw [hguest.memaddrs] at hdom
    have hi := ordinaryDomain_interval addr hdom
    exact ⟨addr, haddr, hi.1, by omega⟩

theorem DomainTouch.dec_panop_mul_load_one (name : MlS) (e1 addrExp : ExpHOL 64) (inner : ProgHOL 64) :
    DomainTouch addrExp (.dec name .one (.panop .mul [e1, .load .one addrExp]) inner) := by
  intro F s hguest hflow
  rw [evaluateHOLFiniteState_dec_total] at hflow
  dsimp only at hflow
  split at hflow
  · simp at hflow
  · rename_i val hval
    simp only [evalHOLExact] at hval
    rcases he1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e1 with _ | v1
    · simp [evalListHOLExact, he1] at hval
    · rcases he2 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) (.load .one addrExp) with _ | v2
      · simp [evalListHOLExact, he1, he2] at hval
      · obtain ⟨addr, haddr, hdom⟩ := eval_load_one_domain s addrExp v2 he2
        rw [hguest.memaddrs] at hdom
        have hi := ordinaryDomain_interval addr hdom
        exact ⟨addr, haddr, hi.1, by omega⟩

theorem DomainTouch.dec_op3_mid_load_one (name : MlS) (bop : BinOp)
    (e1 addrExp e3 : ExpHOL 64) (inner : ProgHOL 64) :
    DomainTouch addrExp (.dec name .one (.op bop [e1, .load .one addrExp, e3]) inner) := by
  intro F s hguest hflow
  rw [evaluateHOLFiniteState_dec_total] at hflow
  dsimp only at hflow
  split at hflow
  · simp at hflow
  · rename_i val hval
    simp only [evalHOLExact] at hval
    rcases he1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e1 with _ | v1
    · simp [evalListHOLExact, he1] at hval
    · rcases he2 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) (.load .one addrExp) with _ | v2
      · simp [evalListHOLExact, he1, he2] at hval
      · obtain ⟨addr, haddr, hdom⟩ := eval_load_one_domain s addrExp v2 he2
        rw [hguest.memaddrs] at hdom
        have hi := ordinaryDomain_interval addr hdom
        exact ⟨addr, haddr, hi.1, by omega⟩

theorem DomainTouch.decCall_arg2_load_one (name : MlS) (sh : ShapeHOL) (fname : MlS)
    (e1 addrExp e3 : ExpHOL 64) (cont : ProgHOL 64) :
    DomainTouch addrExp (.decCall name sh fname [e1, .load .one addrExp, e3] cont) := by
  intro F s hguest hflow
  rw [evaluateHOLFiniteState_decCall_total] at hflow
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [e1, .load .one addrExp, e3] with _ | vals
  · rw [hargs] at hflow; rcases hflow with h | h <;> simp at h
  · have hargs' : @evalListHOLExact 64 F _ s.toExact
        (fun a => Classical.propDecidable (s.memaddrs a)) [e1, .load .one addrExp, e3] = some vals := by
      simpa [evalListHOLFinite] using hargs
    rcases he1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e1 with _ | v1
    · simp [evalListHOLExact, he1] at hargs'
    · rcases he2 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) (.load .one addrExp) with _ | v2
      · simp [evalListHOLExact, he1, he2] at hargs'
      · obtain ⟨addr, haddr, hdom⟩ := eval_load_one_domain s addrExp v2 he2
        rw [hguest.memaddrs] at hdom
        have hi := ordinaryDomain_interval addr hdom
        exact ⟨addr, haddr, hi.1, by omega⟩

/-! ### 3. Loop combinators -/

private theorem bv64_scaled8_inc (b i : BitVec 64) :
    b + (i + 1#64) * 8 = (b + i * 8) + BitVec.ofNat 64 8 := by
  change b + (i + 1#64) * 8#64 = (b + i * 8#64) + 8#64
  rw [BitVec.add_mul, show (1#64 : BitVec 64) * 8#64 = 8#64 by decide, BitVec.add_assoc]

private theorem bv64_scaled8_dec (b i : BitVec 64) :
    b + (i - 1) * 8 = (b + i * 8) - BitVec.ofNat 64 8 := by
  change b + (i - 1#64) * 8#64 = (b + i * 8#64) - 8#64
  have h1 : i - 1#64 = i + (-1#64) := BitVec.sub_eq_add_neg i 1#64
  have h2 : (-1#64 : BitVec 64) * 8#64 = -8#64 := by decide
  rw [h1, BitVec.add_mul, h2, BitVec.sub_eq_add_neg (b + i * 8#64), BitVec.add_assoc]

private theorem bv64_scaled8_add_dec (b k n : BitVec 64) :
    b + ((k - 1) + n) * 8 = (b + (k + n) * 8) - BitVec.ofNat 64 8 := by
  have h0 : (k - 1 : BitVec 64) + n = (k + n) - 1 := by
    change (k - 1#64) + n = (k + n) - 1#64
    rw [BitVec.sub_eq_add_neg k, BitVec.sub_eq_add_neg (k + n),
      BitVec.add_assoc k (-1#64) n, BitVec.add_comm (-1#64) n, ← BitVec.add_assoc k n (-1#64)]
  rw [h0]
  exact bv64_scaled8_dec b (k + n)

theorem while_scaled8_up_walk_guestInv (base counter : MlS) (condition : ExpHOL 64)
    {body : ProgHOL 64} {B : Nat}
    (hbody : TerminatingProgBoundedOn GuestInv body B)
    (htouch : DomainTouch (.op .add [.var .local base, .panop .mul [.var .local counter, .const 8#64]]) body)
    (hadd : CounterStep counter 1#64 body)
    (hbase : avoidsLocal base body = true) :
    TerminatingProgBoundedOn GuestInv (.while condition body) ((domainBytes + 16 + 1) * (B + 1)) := by
  refine @TerminatingProgBoundedOn.while_rank GuestInv condition body B (domainBytes + 16)
    (scaled8UpMu base counter)
    (fun s hs => guestInv_decClock s hs) hbody
    (fun s _ _ _ => scaled8UpMu_le base counter s) ?_
  intro F s _ hguest _ hflow
  have hguest' := guestInv_decClock s hguest
  obtain ⟨addr, haddr, hlow, hhigh⟩ := htouch (decClockHOLFinite s) hguest' hflow
  obtain ⟨b, i, hb, hi, rfl⟩ := scaled8_locals_inv' (decClockHOLFinite s) base counter addr haddr
  have hipost := hadd (decClockHOLFinite s) i hi hflow
  have hbpost := evaluate_avoidsLocal_flowing base body hbase (decClockHOLFinite s)
    (hflow.elim Or.inl (fun h => Or.inr (Or.inr h)))
  change s.locals.lookup base = some (.val (.word b)) at hb
  change s.locals.lookup counter = some (.val (.word i)) at hi
  have hbpost' := hbpost.trans hb
  refine ⟨guestInv_evaluate (decClockHOLFinite s) body hguest', ?_⟩
  have heq : b + (i + 1#64) * 8 = (b + i * 8) + BitVec.ofNat 64 8 := bv64_scaled8_inc b i
  simpa only [scaled8UpMu, hipost, hbpost', hb, hi, heq]
    using scaled8UpRank_add8_lt (b + i * 8) ⟨hlow, hhigh⟩

theorem while_scaled8_down16_guestInv (base counter : MlS) (condition : ExpHOL 64)
    {body : ProgHOL 64} {B : Nat}
    (hbody : TerminatingProgBoundedOn GuestInv body B)
    (htouch : DomainTouch (.op .add [.var .local base, .panop .mul [.var .local counter, .const 8#64]]) body)
    (hsub : CounterStep counter (-1) body)
    (hbase : avoidsLocal base body = true) :
    TerminatingProgBoundedOn GuestInv (.while condition body) ((domainBytes + 16 + 1) * (B + 1)) := by
  refine @TerminatingProgBoundedOn.while_rank GuestInv condition body B (domainBytes + 16)
    (scaled8DownMu16 base counter)
    (fun s hs => guestInv_decClock s hs) hbody
    (fun s _ _ _ => scaled8DownMu16_le base counter s) ?_
  intro F s _ hguest _ hflow
  have hguest' := guestInv_decClock s hguest
  obtain ⟨addr, haddr, hlow, hhigh⟩ := htouch (decClockHOLFinite s) hguest' hflow
  obtain ⟨b, i, hb, hi, rfl⟩ := scaled8_locals_inv' (decClockHOLFinite s) base counter addr haddr
  have hipost := hsub (decClockHOLFinite s) i hi hflow
  have hipost' : (evaluateHOLFiniteState (decClockHOLFinite s) body).2.locals.lookup counter =
      some (.val (.word (i - 1))) := by simpa only [BitVec.sub_eq_add_neg] using hipost
  have hbpost := evaluate_avoidsLocal_flowing base body hbase (decClockHOLFinite s)
    (hflow.elim Or.inl (fun h => Or.inr (Or.inr h)))
  change s.locals.lookup base = some (.val (.word b)) at hb
  change s.locals.lookup counter = some (.val (.word i)) at hi
  have hbpost' := hbpost.trans hb
  refine ⟨guestInv_evaluate (decClockHOLFinite s) body hguest', ?_⟩
  have heq : b + (i - 1) * 8 = (b + i * 8) - BitVec.ofNat 64 8 := bv64_scaled8_dec b i
  simpa only [scaled8DownMu16, hipost', hbpost', hb, hi, heq]
    using scaled8DownRank16_sub8_lt (b + i * 8) ⟨hlow, hhigh⟩

theorem while_scaled8_predec_down_guestInv (base counter : MlS) (condition : ExpHOL 64)
    {tail : ProgHOL 64} {B : Nat}
    (htail : TerminatingProgBoundedOn GuestInv tail B)
    (htouch : DomainTouch (.op .add [.var .local base, .panop .mul [.var .local counter, .const 8#64]]) tail)
    (hjc : avoidsLocal counter tail = true)
    (hbase : avoidsLocal base tail = true)
    (hdistinct : base ≠ counter) :
    TerminatingProgBoundedOn GuestInv
      (.while condition (.seq (.assign .local counter (.op .sub [.var .local counter, .const 1#64])) tail))
      ((domainBytes + 16 + 1) * (B + 1)) := by
  have hbody : TerminatingProgBoundedOn GuestInv
      (.seq (.assign .local counter (.op .sub [.var .local counter, .const 1#64])) tail) B := by
    intro F s hc hP
    simpa only [Nat.zero_add] using
      (TerminatingProgBoundedOn.seq_guestInv
        (straightOn (.assign .local counter (.op .sub [.var .local counter, .const 1#64])) rfl)
        htail s hc hP)
  refine @TerminatingProgBoundedOn.while_rank GuestInv condition _ B (domainBytes + 16)
    (scaled8PreDecDownMu base counter)
    (fun s hs => guestInv_decClock s hs) hbody
    (fun s _ _ _ => scaled8PreDecDownMu_le base counter s) ?_
  intro F s _ hguest _ hflow
  have hguest' := guestInv_decClock s hguest
  refine ⟨guestInv_evaluate (decClockHOLFinite s) _ hguest', ?_⟩
  rw [evaluateHOLFiniteState_seq_line780] at hflow ⊢
  cases ha1 : evaluateHOLFiniteState (decClockHOLFinite s)
      (.assign .local counter (.op .sub [.var .local counter, .const 1#64])) with
  | mk r1 s1 =>
    rw [ha1] at hflow
    dsimp only at hflow ⊢
    cases r1 with
    | some r =>
      dsimp only at hflow
      rcases hflow with h | h
      · cases h
      · have hnc := evaluate_noTopContinue
          (.assign .local counter (.op .sub [.var .local counter, .const 1#64])) rfl (decClockHOLFinite s)
        rw [ha1] at hnc
        exact absurd h hnc
    | none =>
      dsimp only at hflow ⊢
      have hj_word : ∃ j : BitVec 64, s.locals.lookup counter = some (.val (.word j)) ∧
          s1 = setVarHOLFinite counter (.val (.word (j - 1#64))) (decClockHOLFinite s) := by
        rw [evaluateHOLFiniteState_assign] at ha1
        cases hj_lk : s.locals.lookup counter with
        | none =>
          simp [evalHOLExact, evalListHOLExact, decClockHOLFinite, hj_lk] at ha1
        | some vj =>
          cases vj with
          | rStruct _ =>
            simp [evalHOLExact, evalListHOLExact, decClockHOLFinite, hj_lk, wordOpHOL, valueIsWord] at ha1
          | nStruct _ _ =>
            simp [evalHOLExact, evalListHOLExact, decClockHOLFinite, hj_lk, wordOpHOL, valueIsWord] at ha1
          | val wj =>
            cases wj with
            | word j =>
              refine ⟨j, rfl, ?_⟩
              simp [evalHOLExact, evalListHOLExact, decClockHOLFinite, hj_lk, wordOpHOL, wordOp,
                valueIsWord, valueWord, lookupKvarHOLExact, isValidValueHOLExact, setKvarHOLFinite,
                shapeOfHOLExact, shapeEqHOL] at ha1
              exact ha1.symm
      obtain ⟨j, hj_lk, hs1_eq⟩ := hj_word
      rw [hs1_eq] at hflow ⊢
      have hg1 : GuestInv (setVarHOLFinite counter (.val (.word (j - 1#64))) (decClockHOLFinite s)) :=
        guestInv_setVar _ _ _ hguest'
      obtain ⟨addr, haddr, hlow, hhigh⟩ := htouch _ hg1 hflow
      obtain ⟨b, j1, hb1, hj1, rfl⟩ := scaled8_locals_inv' _ base counter addr haddr
      have hb_s : s.locals.lookup base = some (.val (.word b)) := by
        simpa [decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          Ne.symm hdistinct] using hb1
      have hj1_eq : j1 = j - 1#64 := by
        have : (some (.val (.word (j - 1#64))) : Option (ValueHOL 64)) = some (.val (.word j1)) := by
          simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE] using hj1
        cases this; rfl
      subst hj1_eq
      have hj_post := evaluate_avoidsLocal_flowing counter tail hjc _
        (hflow.elim Or.inl (fun h => Or.inr (Or.inr h)))
      have hb_post := evaluate_avoidsLocal_flowing base tail hbase _
        (hflow.elim Or.inl (fun h => Or.inr (Or.inr h)))
      have hj_post' := hj_post.trans hj1
      have hb_post' := hb_post.trans hb1
      have heq1 : (j - 1 : BitVec 64) = j - 1#64 := rfl
      have heq : b + (j - 1#64 - 1) * 8 = (b + (j - 1#64) * 8) - BitVec.ofNat 64 8 :=
        bv64_scaled8_dec b (j - 1#64)
      simpa only [scaled8PreDecDownMu, hb_post', hj_post', hb_s, hj_lk, heq1, heq]
        using scaled8DownRank16_sub8_lt (b + (j - 1#64) * 8) ⟨hlow, hhigh⟩

theorem while_scaled8_predec_add_cell_guestInv (base counter off : MlS) (condition : ExpHOL 64)
    {tail : ProgHOL 64} {B : Nat}
    (htail : TerminatingProgBoundedOn GuestInv tail B)
    (htouch : DomainTouch
      (.op .add [.var .local base, .panop .mul [.op .add [.var .local counter, .var .local off], .const 8#64]])
      tail)
    (hjc : avoidsLocal counter tail = true)
    (hbase : avoidsLocal base tail = true)
    (hoff : avoidsLocal off tail = true)
    (hbc : base ≠ counter) (hoc : off ≠ counter) :
    TerminatingProgBoundedOn GuestInv
      (.while condition (.seq (.assign .local counter (.op .sub [.var .local counter, .const 1#64])) tail))
      ((domainBytes / 8 + 2 + 1) * (B + 1)) := by
  have hbody : TerminatingProgBoundedOn GuestInv
      (.seq (.assign .local counter (.op .sub [.var .local counter, .const 1#64])) tail) B := by
    intro F s hc hP
    simpa only [Nat.zero_add] using
      (TerminatingProgBoundedOn.seq_guestInv
        (straightOn (.assign .local counter (.op .sub [.var .local counter, .const 1#64])) rfl)
        htail s hc hP)
  refine @TerminatingProgBoundedOn.while_rank GuestInv condition _ B (domainBytes / 8 + 2)
    (scaled8PreDecAddCellMu base counter off)
    (fun s hs => guestInv_decClock s hs) hbody
    (fun s _ _ _ => scaled8PreDecAddCellMu_le base counter off s) ?_
  intro F s _ hguest _ hflow
  have hguest' := guestInv_decClock s hguest
  refine ⟨guestInv_evaluate (decClockHOLFinite s) _ hguest', ?_⟩
  rw [evaluateHOLFiniteState_seq_line780] at hflow ⊢
  cases ha1 : evaluateHOLFiniteState (decClockHOLFinite s)
      (.assign .local counter (.op .sub [.var .local counter, .const 1#64])) with
  | mk r1 s1 =>
    rw [ha1] at hflow
    dsimp only at hflow ⊢
    cases r1 with
    | some r =>
      dsimp only at hflow
      rcases hflow with h | h
      · cases h
      · have hnc := evaluate_noTopContinue
          (.assign .local counter (.op .sub [.var .local counter, .const 1#64])) rfl (decClockHOLFinite s)
        rw [ha1] at hnc
        exact absurd h hnc
    | none =>
      dsimp only at hflow ⊢
      have hj_word : ∃ j : BitVec 64, s.locals.lookup counter = some (.val (.word j)) ∧
          s1 = setVarHOLFinite counter (.val (.word (j - 1#64))) (decClockHOLFinite s) := by
        rw [evaluateHOLFiniteState_assign] at ha1
        cases hj_lk : s.locals.lookup counter with
        | none =>
          simp [evalHOLExact, evalListHOLExact, decClockHOLFinite, hj_lk] at ha1
        | some vj =>
          cases vj with
          | rStruct _ =>
            simp [evalHOLExact, evalListHOLExact, decClockHOLFinite, hj_lk, wordOpHOL, valueIsWord] at ha1
          | nStruct _ _ =>
            simp [evalHOLExact, evalListHOLExact, decClockHOLFinite, hj_lk, wordOpHOL, valueIsWord] at ha1
          | val wj =>
            cases wj with
            | word j =>
              refine ⟨j, rfl, ?_⟩
              simp [evalHOLExact, evalListHOLExact, decClockHOLFinite, hj_lk, wordOpHOL, wordOp,
                valueIsWord, valueWord, lookupKvarHOLExact, isValidValueHOLExact, setKvarHOLFinite,
                shapeOfHOLExact, shapeEqHOL] at ha1
              exact ha1.symm
      obtain ⟨j, hj_lk, hs1_eq⟩ := hj_word
      rw [hs1_eq] at hflow ⊢
      have hg1 : GuestInv (setVarHOLFinite counter (.val (.word (j - 1#64))) (decClockHOLFinite s)) :=
        guestInv_setVar _ _ _ hguest'
      obtain ⟨addr, haddr, hlow, hhigh⟩ := htouch _ hg1 hflow
      obtain ⟨b, j1, n, hb1, hj1, hn1, rfl⟩ := scaled8_add_locals_inv _ base counter off addr haddr
      have hb_s : s.locals.lookup base = some (.val (.word b)) := by
        simpa [decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          Ne.symm hbc] using hb1
      have hn_s : s.locals.lookup off = some (.val (.word n)) := by
        simpa [decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          Ne.symm hoc] using hn1
      have hj1_eq : j1 = j - 1#64 := by
        have : (some (.val (.word (j - 1#64))) : Option (ValueHOL 64)) = some (.val (.word j1)) := by
          simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE] using hj1
        cases this; rfl
      subst hj1_eq
      have hj_post := evaluate_avoidsLocal_flowing counter tail hjc _
        (hflow.elim Or.inl (fun h => Or.inr (Or.inr h)))
      have hb_post := evaluate_avoidsLocal_flowing base tail hbase _
        (hflow.elim Or.inl (fun h => Or.inr (Or.inr h)))
      have hn_post := evaluate_avoidsLocal_flowing off tail hoff _
        (hflow.elim Or.inl (fun h => Or.inr (Or.inr h)))
      have hj_post' := hj_post.trans hj1
      have hb_post' := hb_post.trans hb1
      have hn_post' := hn_post.trans hn1
      have heq1 : (j - 1 : BitVec 64) = j - 1#64 := rfl
      have heq : b + ((j - 1#64 - 1) + n) * 8 = (b + ((j - 1#64) + n) * 8) - BitVec.ofNat 64 8 :=
        bv64_scaled8_add_dec b (j - 1#64) n
      simpa only [scaled8PreDecAddCellMu, hb_post', hj_post', hn_post', hb_s, hj_lk, hn_s, heq1, heq]
        using scaled8CellDownRank_sub8_lt (b + ((j - 1#64) + n) * 8) ⟨hlow, hhigh⟩

/-! ### 4. Tight Knuth D3 `qhat` correction bound (`2^32 + 1` iterations) via `qhat ≤ 2^32 - 1` -/

private theorem ite_flow_prop {F : Type} (s : PanSemStateFiniteExact 64 F)
    (condition : ExpHOL 64) (yes no : ProgHOL 64) (R : PanSemStateFiniteExact 64 F → Prop)
    (hyes : ∀ w : BitVec 64,
      evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) condition = some (.val (.word w)) →
      w ≠ 0 →
      ((evaluateHOLFiniteState s yes).1 = none ∨ (evaluateHOLFiniteState s yes).1 = some .continue) →
      R (evaluateHOLFiniteState s yes).2)
    (hno : ((evaluateHOLFiniteState s no).1 = none ∨ (evaluateHOLFiniteState s no).1 = some .continue) →
      R (evaluateHOLFiniteState s no).2) :
    ((evaluateHOLFiniteState s (.ite condition yes no)).1 = none ∨
      (evaluateHOLFiniteState s (.ite condition yes no)).1 = some .continue) →
    R (evaluateHOLFiniteState s (.ite condition yes no)).2 := by
  rw [evaluateHOLFiniteState_ite]
  split
  · rename_i w hw
    split
    · exact hno
    · rename_i hnz
      exact hyes w hw hnz
  · intro hf; rcases hf with h | h <;> simp at h

private theorem mul_nonzero_local' {F : Type} (s : PanSemStateFiniteExact 64 F)
    (counter : MlS) (factor : ExpHOL 64) (result : BitVec 64)
    (hr : evalAt s (.panop .mul [.var .local counter, factor]) = some (.val (.word result)))
    (hnz : result ≠ 0) :
    ∃ w : BitVec 64, s.locals.lookup counter = some (.val (.word w)) ∧ w ≠ 0 := by
  cases hl : s.locals.lookup counter with
  | none => simp [evalAt, evalHOLExact, evalListHOLExact, hl] at hr
  | some value =>
    cases value with
    | rStruct _ =>
      cases hf : evalAt s factor <;>
        simp [evalAt, evalHOLExact, evalListHOLExact, hl, hf, valueIsWord] at hr
    | nStruct _ _ =>
      cases hf : evalAt s factor <;>
        simp [evalAt, evalHOLExact, evalListHOLExact, hl, hf, valueIsWord] at hr
    | val wordval =>
      cases wordval with
      | word w =>
        refine ⟨w, rfl, ?_⟩
        intro hz; subst w
        cases hf : evalAt s factor with
        | none => simp [evalAt, evalHOLExact, evalListHOLExact, hl, hf] at hr
        | some v =>
          cases v with
          | rStruct _ => simp [evalAt, evalHOLExact, evalListHOLExact, hl, hf, valueIsWord] at hr
          | nStruct _ _ => simp [evalAt, evalHOLExact, evalListHOLExact, hl, hf, valueIsWord] at hr
          | val wv =>
            cases wv with
            | word z =>
              simp [evalAt, evalHOLExact, evalListHOLExact, hl, hf, valueIsWord, valueWord, panOpHOL] at hr
              subst result; exact hnz rfl

private theorem correction_test_nonzero' {F : Type} (s : PanSemStateFiniteExact 64 F)
    (counter : MlS) (factor left : ExpHOL 64) (result : BitVec 64)
    (hc : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .lower left (.panop .mul [.var .local counter, factor])) = some (.val (.word result)))
    (hnz : result ≠ 0) :
    ∃ w : BitVec 64, s.locals.lookup counter = some (.val (.word w)) ∧ w ≠ 0 := by
  change evalAt s _ = _ at hc
  obtain ⟨_, r, _, hr, hword⟩ := evalAt_cmp s .lower _ _ result hc
  apply mul_nonzero_local' s counter factor r hr
  intro hz; subst r
  simp [wordCmpHOL, BitVec.lt_def] at hword
  exact hnz hword

private def knuthCond : ExpHOL 64 := .cmp .equal (.var .local (ofString "again")) (.const 1)
private def knuthOuter : ExpHOL 64 := .cmp .lower (.var .local (ofString "rhat")) (.const 4294967296)
private def knuthInner : ExpHOL 64 :=
  .cmp .lower
    (.op .or [.shift .lsl (.var .local (ofString "rhat")) (.const 32), .var .local (ofString "ujn2")])
    (.panop .mul [.var .local (ofString "qhat"), .var .local (ofString "vsec")])
private def knuthDecr : ProgHOL 64 :=
  .seq (.assign .local (ofString "qhat") (.op .sub [.var .local (ofString "qhat"), .const 1]))
    (.seq (.assign .local (ofString "rhat") (.op .add [.var .local (ofString "rhat"), .var .local (ofString "vtop")]))
      (.assign .local (ofString "again") (.const 1)))
private def knuthBody : ProgHOL 64 :=
  .seq (.assign .local (ofString "again") (.const 0))
    (.ite knuthOuter (.ite knuthInner knuthDecr .skip) .skip)

def QhatCapInv : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => GuestInv s ∧ locN s "qhat" ≤ 4294967295

private noncomputable def knuthRank {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat := by
  classical
  exact if s.locals.lookup (ofString "again") = some (.val (.word 1#64)) then
    match s.locals.lookup (ofString "qhat") with
    | some (.val (.word w)) => w.toNat + 1
    | _ => 1
  else 0

theorem knuthCorrection_capped_bound :
    TerminatingProgBoundedOn QhatCapInv (.while knuthCond knuthBody)
      ((4294967296 + 1) * (0 + 1)) := by
  refine @TerminatingProgBoundedOn.while_rank QhatCapInv
    knuthCond knuthBody 0 4294967296
    knuthRank
    (fun s hP => ⟨guestInv_decClock s hP.1, hP.2⟩)
    (fun s hc hP => straightOn knuthBody rfl s hc hP.1)
    (fun s _ hP _ => by
      unfold knuthRank
      split
      · split
        · rename_i w hw
          have hcap := hP.2
          simp [locN, hw] at hcap
          omega
        · omega
      · omega)
    ?_
  intro F s _ ⟨hs, hqcap⟩ hact hflow
  obtain ⟨word, hw, hnz⟩ := hact
  change evalAt s _ = _ at hw
  obtain ⟨a, v, ha, hv, hword⟩ := evalAt_cmp s .equal _ _ word hw
  have hv1 : v = 1#64 := by simpa [evalAt, evalHOLExact] using hv.symm
  subst v
  have hla : s.locals.lookup (ofString "again") = some (.val (.word a)) := by
    simpa [evalAt, evalHOLExact] using ha
  have ha1 : a = 1#64 := by
    by_cases hcmp : wordCmpHOL .equal a 1#64 = true
    · simpa [wordCmpHOL] using hcmp
    · simp [hcmp] at hword; exact absurd hword hnz
  subst a
  have hpositive : 0 < knuthRank s := by
    unfold knuthRank
    rw [if_pos hla]
    split <;> omega
  let s0 := setVarHOLFinite (ofString "again") (.val (.word 0#64)) (decClockHOLFinite s)
  have hreset : evaluateHOLFiniteState (decClockHOLFinite s)
      (.assign .local (ofString "again") (.const 0)) = (none, s0) := by
    simp [s0, evaluateHOLFiniteState_assign, evalHOLExact, isValidValueHOLExact,
      setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL, lookupKvarHOLExact, decClockHOLFinite, hla]
  have hzero : knuthRank s0 = 0 := by
    simp [knuthRank, s0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hqcap0 : locN s0 "qhat" ≤ 4294967295 := by
    have hne : (ofString "again" == ofString "qhat") = false := by decide
    simpa [s0, locN, decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne] using hqcap
  refine ⟨⟨guestInv_evaluate _ _ (guestInv_decClock s hs), ?_⟩, ?_⟩
  · unfold knuthBody at hflow ⊢
    rw [evaluateHOLFiniteState_seq_line780, hreset] at hflow ⊢
    dsimp only at hflow ⊢
    refine ite_flow_prop s0 knuthOuter (.ite knuthInner knuthDecr .skip) .skip
      (fun t => locN t "qhat" ≤ 4294967295) ?_ ?_ hflow
    · intro _ _ _ hflowInner
      refine ite_flow_prop s0 knuthInner knuthDecr .skip
        (fun t => locN t "qhat" ≤ 4294967295) ?_ ?_ hflowInner
      · intro inner hin hinner hflowDec
        obtain ⟨q, hq, hqnz⟩ := correction_test_nonzero' s0 (ofString "qhat")
          (.var .local (ofString "vsec")) _ inner hin hinner
        have heffect : CounterStep (ofString "qhat") (-1) knuthDecr :=
          CounterStep.suffix _ _ _ (CounterStep.sub_one _) (by decide)
        have hpost : (evaluateHOLFiniteState s0 knuthDecr).2.locals.lookup (ofString "qhat") =
            some (.val (.word (q - 1))) := by
          simpa only [BitVec.sub_eq_add_neg] using heffect s0 q hq hflowDec
        have hqle : q.toNat ≤ 4294967295 := by simpa [locN, hq] using hqcap0
        have hqpos : 0 < q.toNat := by
          by_contra hc
          exact hqnz (BitVec.eq_of_toNat_eq (by simpa using Nat.eq_zero_of_not_pos hc))
        have hsub : (q - 1).toNat = q.toNat - 1 := by
          rw [BitVec.toNat_sub]
          change (18446744073709551615 + q.toNat) % 18446744073709551616 = q.toNat - 1
          have := q.isLt; omega
        simp [locN, hpost, hsub]; omega
      · intro _; simpa [evaluateHOLFiniteState_skip] using hqcap0
    · intro _; simpa [evaluateHOLFiniteState_skip] using hqcap0
  · unfold knuthBody at hflow ⊢
    rw [evaluateHOLFiniteState_seq_line780, hreset] at hflow ⊢
    dsimp only at hflow ⊢
    refine ite_flow_prop s0 knuthOuter (.ite knuthInner knuthDecr .skip) .skip
      (fun t => knuthRank t < knuthRank s) ?_ ?_ hflow
    · intro _ _ _ hflowInner
      refine ite_flow_prop s0 knuthInner knuthDecr .skip
        (fun t => knuthRank t < knuthRank s) ?_ ?_ hflowInner
      · intro inner hin hinner hflowDec
        obtain ⟨q, hq, hqnz⟩ := correction_test_nonzero' s0 (ofString "qhat")
          (.var .local (ofString "vsec")) _ inner hin hinner
        have hqs : s.locals.lookup (ofString "qhat") = some (.val (.word q)) := by
          have hne : (ofString "again" == ofString "qhat") = false := by decide
          simpa [s0, decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne] using hq
        have heffect : CounterStep (ofString "qhat") (-1) knuthDecr :=
          CounterStep.suffix _ _ _ (CounterStep.sub_one _) (by decide)
        have hpost : (evaluateHOLFiniteState s0 knuthDecr).2.locals.lookup (ofString "qhat") =
            some (.val (.word (q - 1))) := by
          simpa only [BitVec.sub_eq_add_neg] using heffect s0 q hq hflowDec
        have hpostrank : knuthRank (evaluateHOLFiniteState s0 knuthDecr).2 ≤ (q - 1).toNat + 1 := by
          unfold knuthRank; split <;> simp [hpost]
        have hbefore : knuthRank s = q.toNat + 1 := by
          unfold knuthRank; rw [if_pos hla, hqs]
        have hqpos : 0 < q.toNat := by
          by_contra hc
          exact hqnz (BitVec.eq_of_toNat_eq (by simpa using Nat.eq_zero_of_not_pos hc))
        have hdrop : (q - 1).toNat < q.toNat := by
          rw [BitVec.toNat_sub]
          change (18446744073709551615 + q.toNat) % 18446744073709551616 < q.toNat
          have := q.isLt; omega
        rw [hbefore]; omega
      · intro _; simpa only [evaluateHOLFiniteState_skip, hzero] using hpositive
    · intro _; simpa only [evaluateHOLFiniteState_skip, hzero] using hpositive

/-! ### 5. `div64by32` return-value bound (`q ≤ 2^32 - 1`) -/

private def noReturnOrRaise : ProgHOL 64 → Bool
  | .seq a b => noReturnOrRaise a && noReturnOrRaise b
  | .ite _ a b => noReturnOrRaise a && noReturnOrRaise b
  | .while _ a => noReturnOrRaise a
  | .assign .local _ _ | .store _ _ | .storeByte _ _ | .skip => true
  | _ => false

private theorem evaluate_noReturn {F : Type} (p : ProgHOL 64) (hp : noReturnOrRaise p = true)
    (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64) :
    (evaluateHOLFiniteState s p).1 ≠ some (.returned v) := by
  cases shape : p with
  | skip => rw [evaluateHOLFiniteState_skip]; simp
  | assign k _ _ =>
    cases k with
    | global => simp [shape, noReturnOrRaise] at hp
    | «local» =>
      rw [evaluateHOLFiniteState_assign]
      split
      · simp
      · split <;> simp
  | store _ _ =>
    rw [evaluateHOLFiniteState_store]
    split
    · split
      · split <;> simp
      · simp
    · simp
  | storeByte _ _ =>
    rw [evaluateHOLFiniteState_storeByte]
    split
    · split
      · split <;> simp
      · simp
    · simp
  | seq a b =>
    have hab : noReturnOrRaise a = true ∧ noReturnOrRaise b = true := by
      simpa [shape, noReturnOrRaise, Bool.and_eq_true] using hp
    have rem := evaluateHOLFiniteState_clock_le s a
    rw [evaluateHOLFiniteState_seq_line780]
    have ha := evaluate_noReturn a hab.1 s v
    rcases hr : evaluateHOLFiniteState s a with ⟨r, m⟩
    rw [hr] at ha rem
    have mclk : m.clock ≤ s.clock := rem
    cases r with
    | none => exact evaluate_noReturn b hab.2 m v
    | some _ => exact ha
  | ite _ a b =>
    have hab : noReturnOrRaise a = true ∧ noReturnOrRaise b = true := by
      simpa [shape, noReturnOrRaise, Bool.and_eq_true] using hp
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_noReturn b hab.2 s v
      · exact evaluate_noReturn a hab.1 s v
    · simp
  | «while» cond body =>
    have hb : noReturnOrRaise body = true := by simpa [shape, noReturnOrRaise] using hp
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · simp
        · have dec_lt : (decClockHOLFinite s).clock < s.clock := by
            simp only [decClockHOLFinite]; omega
          dsimp only
          rw [fixClockHOLFinite_evaluateState]
          have ih1 := evaluate_noReturn body hb (decClockHOLFinite s) v
          have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨r1, mid⟩
          rw [hbr] at ih1 rem
          have smaller : mid.clock < s.clock := by
            change mid.clock ≤ s.clock - 1 at rem; omega
          cases r1 with
          | none => exact evaluate_noReturn (.while cond body) (by simpa [noReturnOrRaise] using hb) mid v
          | some r1 =>
            cases r1 with
            | «continue» => exact evaluate_noReturn (.while cond body) (by simpa [noReturnOrRaise] using hb) mid v
            | returned _ => exact ih1
            | _ => simp
      · simp
    · simp
  | _ => simp [shape, noReturnOrRaise] at hp
termination_by (s.clock, sizeOf p)
decreasing_by
  all_goals
    subst shape
    simp_wf
    first
      | exact Prod.Lex.left _ _ dec_lt
      | exact Prod.Lex.left _ _ smaller
      | exact Prod.Lex.right _ (by omega)
      | (rcases Nat.lt_or_eq_of_le mclk with h | h
         · exact Prod.Lex.left _ _ h
         · rw [h]; exact Prod.Lex.right _ (by omega))

private def div64Body : ProgHOL 64 :=
  InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
    (extractFn Guest.Software.guestFn_div64by32).body

private def div64Inner : ProgHOL 64 :=
  match div64Body with
  | .dec _ _ _ (.dec _ _ _ (.dec _ _ _ inner)) => inner
  | _ => .skip

private def div64Loop : ProgHOL 64 :=
  match div64Inner with
  | .seq w _ => w
  | _ => .skip

private def div64Step : ProgHOL 64 :=
  match div64Loop with
  | .while _ b => b
  | _ => .skip

private theorem lookup_div64by32_spec :
    originalRuntimeCode.lookup (ofString "div64by32") =
      some ([(ofString "hi", .one), (ofString "lo", .one), (ofString "d", .one)],
            div64Body, .comb [.one, .one]) :=
  lookup_of_guestAst_getElem 63 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_div64by32) rfl

private theorem lsl1_lt_2_32 (idx : BitVec 64) (hidx : idx.toNat < 32) :
    ((1#64 : BitVec 64) <<< idx.toNat).toNat ≤ 4294967295 := by
  have hlt : 1 * 2 ^ idx.toNat < 2 ^ 32 := Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_right (by omega) hidx) (by omega)
  rw [BitVec.toNat_shiftLeft]
  change (1 <<< idx.toNat) % 18446744073709551616 ≤ 4294967295
  rw [Nat.shiftLeft_eq]
  omega

private theorem or_lt_2_32 (a b : BitVec 64) (ha : a.toNat ≤ 4294967295) (hb : b.toNat ≤ 4294967295) :
    (a ||| b).toNat ≤ 4294967295 := by
  have hor : (a.toNat ||| b.toNat) < 2 ^ 32 :=
    Nat.or_lt_two_pow (by omega) (by omega)
  rw [BitVec.toNat_or]
  change (a.toNat ||| b.toNat) ≤ 4294967295
  omega

private theorem div64Step_preserves {F : Type} (s : PanSemStateFiniteExact 64 F)
    (wi wq : BitVec 64)
    (hi : s.locals.lookup (ofString "i") = some (.val (.word wi)))
    (hq : s.locals.lookup (ofString "q") = some (.val (.word wq)))
    (hi_pos : 0 < wi.toNat) (hi_le : wi.toNat ≤ 32)
    (hq_le : wq.toNat ≤ 4294967295)
    (hnone : (evaluateHOLFiniteState s div64Step).1 = none) :
    let post := (evaluateHOLFiniteState s div64Step).2
    post.locals.lookup (ofString "i") = some (.val (.word (wi - 1#64))) ∧
    ∃ wq' : BitVec 64, post.locals.lookup (ofString "q") = some (.val (.word wq')) ∧ wq'.toNat ≤ 4294967295 := by
  dsimp only
  have hstep_eq : div64Step =
      .seq (.assign .local (ofString "i") (.op .sub [.var .local (ofString "i"), .const 1#64]))
        (.seq (.assign .local (ofString "r")
          (.op .or [.shift .lsl (.var .local (ofString "r")) (.const 1#64),
            .op .and [.shift .lsr (.var .local (ofString "lo")) (.var .local (ofString "i")), .const 1#64]]))
          (.ite (.cmp .notLower (.var .local (ofString "r")) (.var .local (ofString "d")))
            (.seq (.assign .local (ofString "r") (.op .sub [.var .local (ofString "r"), .var .local (ofString "d")]))
              (.assign .local (ofString "q") (.op .or [.var .local (ofString "q"), .shift .lsl (.const 1#64) (.var .local (ofString "i"))])))
            .skip)) := rfl
  rw [hstep_eq] at hnone ⊢
  let s1 := setVarHOLFinite (ofString "i") (.val (.word (wi - 1#64))) s
  have hass1 : evaluateHOLFiniteState s
      (.assign .local (ofString "i") (.op .sub [.var .local (ofString "i"), .const 1#64])) = (none, s1) := by
    simp [s1, evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hi,
      wordOpHOL, wordOp, valueIsWord, valueWord, lookupKvarHOLExact, isValidValueHOLExact,
      setKvarHOLFinite, shapeOfHOLExact, shapeEqHOL]
  rw [evaluate_seq_split, hass1] at hnone ⊢
  dsimp only at hnone ⊢
  rw [evaluateHOLFiniteState_seq_line780] at hnone ⊢
  cases hr2 : evaluateHOLFiniteState s1
      (.assign .local (ofString "r")
        (.op .or [.shift .lsl (.var .local (ofString "r")) (.const 1#64),
          .op .and [.shift .lsr (.var .local (ofString "lo")) (.var .local (ofString "i")), .const 1#64]])) with
  | mk res2 s2 =>
    rw [hr2] at hnone
    dsimp only at hnone ⊢
    cases res2 with
    | some _ => cases hnone
    | none =>
      dsimp only at hnone ⊢
      have hs2_i : s2.locals.lookup (ofString "i") = some (.val (.word (wi - 1#64))) := by
        have hk := evaluate_avoidsLocal_flowing (ofString "i")
          (.assign .local (ofString "r")
            (.op .or [.shift .lsl (.var .local (ofString "r")) (.const 1#64),
              .op .and [.shift .lsr (.var .local (ofString "lo")) (.var .local (ofString "i")), .const 1#64]]))
          (by decide) s1 (by rw [hr2]; exact Or.inl rfl)
        rw [hr2] at hk
        exact hk.trans (by simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
      have hs2_q : s2.locals.lookup (ofString "q") = some (.val (.word wq)) := by
        have hk := evaluate_avoidsLocal_flowing (ofString "q")
          (.assign .local (ofString "r")
            (.op .or [.shift .lsl (.var .local (ofString "r")) (.const 1#64),
              .op .and [.shift .lsr (.var .local (ofString "lo")) (.var .local (ofString "i")), .const 1#64]]))
          (by decide) s1 (by rw [hr2]; exact Or.inl rfl)
        rw [hr2] at hk
        exact hk.trans (by simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "i" ≠ ofString "q" by decide, hq])
      rw [evaluateHOLFiniteState_ite] at hnone ⊢
      cases hev_c : @evalHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a))
          (.cmp .notLower (.var .local (ofString "r")) (.var .local (ofString "d"))) with
      | none => simp [hev_c] at hnone
      | some vc =>
        cases vc with
        | rStruct _ => simp [hev_c] at hnone
        | nStruct _ => simp [hev_c] at hnone
        | val wcv =>
          cases wcv with
          | word wc =>
            simp only [hev_c] at hnone ⊢
            by_cases hcond_eq : wc = 0
            · rw [if_pos hcond_eq, evaluateHOLFiniteState_skip]
              exact ⟨hs2_i, wq, hs2_q, hq_le⟩
            · rw [if_neg hcond_eq] at hnone ⊢
              rw [evaluateHOLFiniteState_seq_line780] at hnone ⊢
              cases hr3 : evaluateHOLFiniteState s2
                  (.assign .local (ofString "r") (.op .sub [.var .local (ofString "r"), .var .local (ofString "d")])) with
              | mk res3 s3 =>
                rw [hr3] at hnone
                dsimp only at hnone ⊢
                cases res3 with
                | some _ => cases hnone
                | none =>
                  dsimp only at hnone ⊢
                  have hs3_i : s3.locals.lookup (ofString "i") = some (.val (.word (wi - 1#64))) := by
                    have hk := evaluate_avoidsLocal_flowing (ofString "i")
                      (.assign .local (ofString "r") (.op .sub [.var .local (ofString "r"), .var .local (ofString "d")]))
                      (by decide) s2 (by rw [hr3]; exact Or.inl rfl)
                    rw [hr3] at hk
                    exact hk.trans hs2_i
                  have hs3_q : s3.locals.lookup (ofString "q") = some (.val (.word wq)) := by
                    have hk := evaluate_avoidsLocal_flowing (ofString "q")
                      (.assign .local (ofString "r") (.op .sub [.var .local (ofString "r"), .var .local (ofString "d")]))
                      (by decide) s2 (by rw [hr3]; exact Or.inl rfl)
                    rw [hr3] at hk
                    exact hk.trans hs2_q
                  let wsub := wi - 1#64
                  have hs3_i' : s3.locals.lookup (ofString "i") = some (.val (.word wsub)) := hs3_i
                  have hwi_sub : wsub.toNat < 32 := by
                    change (wi - 1#64).toNat < 32
                    rw [BitVec.toNat_sub]
                    change (18446744073709551615 + wi.toNat) % 18446744073709551616 < 32
                    have := wi.isLt; omega
                  have hsh_eval : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
                      (.op .or [.var .local (ofString "q"), .shift .lsl (.const 1#64) (.var .local (ofString "i"))]) =
                      some (.val (.word (wq ||| ((1#64 : BitVec 64) <<< wsub.toNat)))) := by
                    have hlt64 : ¬ (64 ≤ wsub.toNat) := by omega
                    simp [evalHOLExact, evalListHOLExact, hs3_q, hs3_i', wordShiftHOL, hlt64,
                      wordOpHOL, wordOp, valueIsWord, valueWord, OrOp.or]
                  rw [evaluateHOLFiniteState_assign] at hnone ⊢
                  rw [hsh_eval] at hnone ⊢
                  dsimp only at hnone ⊢
                  split at hnone
                  · rename_i hv
                    rw [if_pos hv]
                    dsimp only
                    refine ⟨?_, wq ||| ((1#64 : BitVec 64) <<< wsub.toNat), ?_, ?_⟩
                    · simp [wsub, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
                        show ofString "q" ≠ ofString "i" by decide, hs3_i]
                    · simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                    · exact or_lt_2_32 wq _ hq_le (lsl1_lt_2_32 wsub hwi_sub)
                  · simp at hnone

private theorem div64Loop_q_le :
    ∀ (fuel : Nat) {F : Type} (s : PanSemStateFiniteExact 64 F) (wi wq : BitVec 64),
      fuel = wi.toNat →
      wi.toNat ≤ 32 →
      s.locals.lookup (ofString "i") = some (.val (.word wi)) →
      s.locals.lookup (ofString "q") = some (.val (.word wq)) →
      wq.toNat ≤ 4294967295 →
      (evaluateHOLFiniteState s div64Loop).1 = none →
      ∃ wq' : BitVec 64,
        (evaluateHOLFiniteState s div64Loop).2.locals.lookup (ofString "q") = some (.val (.word wq')) ∧
        wq'.toNat ≤ 4294967295 := by
  intro fuel
  induction fuel with
  | zero =>
    intro F s wi wq hfuel _ hi hq hq_le hnone
    have hwi0 : wi = 0#64 := BitVec.eq_of_toNat_eq (by simpa using hfuel.symm)
    subst hwi0
    have hl : div64Loop = .while (.cmp .less (.const 0#64) (.var .local (ofString "i"))) div64Step := rfl
    rw [hl, evaluateHOLFiniteState_while_fixClockRewrite] at hnone ⊢
    simp [evalHOLFinite, evalHOLExact, hi, wordCmpHOL, holAsmSignedLess]
    exact ⟨wq, hq, hq_le⟩
  | succ k ih =>
    intro F s wi wq hfuel hi_le hi hq hq_le hnone
    have hl : div64Loop = .while (.cmp .less (.const 0#64) (.var .local (ofString "i"))) div64Step := rfl
    rw [hl, evaluateHOLFiniteState_while_fixClockRewrite] at hnone ⊢
    have hcmp : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .less (.const 0#64) (.var .local (ofString "i"))) = some (.val (.word 1#64)) := by
      have hslt : holAsmSignedLess 0#64 wi = true := by
        have hw1 : wi.toNat = k + 1 := hfuel.symm
        have hwlt : wi.toNat < 2 ^ 63 := by omega
        have hwpos : 0 < wi.toNat := by omega
        rw [holAsmSignedLess_small 0#64 wi (by decide) hwlt]
        simp [hwpos]
      simp [evalHOLFinite, evalHOLExact, hi, wordCmpHOL, hslt]
    rw [hcmp] at hnone ⊢
    dsimp only at hnone ⊢
    rw [if_pos (show (1#64 : BitVec 64) ≠ 0 by decide)] at hnone ⊢
    by_cases hclk : s.clock = 0
    · rw [if_pos hclk] at hnone; simp at hnone
    · rw [if_neg hclk] at hnone ⊢
      have hnc := evaluate_noTopContinue div64Step rfl (decClockHOLFinite s)
      have hnb := evaluate_noTopBreak div64Step rfl (decClockHOLFinite s)
      let resMid := evaluateHOLFiniteState (decClockHOLFinite s) div64Step
      have hstep : evaluateHOLFiniteState (decClockHOLFinite s) div64Step = resMid := rfl
      cases hm : resMid with
      | mk rStep mid =>
        rw [hstep, hm] at hnone hnc hnb ⊢
        dsimp only at hnone hnc hnb ⊢
        cases rStep with
        | some r =>
          cases r <;> simp_all
        | none =>
          dsimp only at hnone ⊢
          have hstep_none : (evaluateHOLFiniteState (decClockHOLFinite s) div64Step).1 = none := by rw [hstep, hm]
          obtain ⟨hmid_i, wq1, hmid_q, hmid_qle⟩ := div64Step_preserves (decClockHOLFinite s) wi wq
            hi hq (by omega) hi_le hq_le hstep_none
          rw [hstep, hm] at hmid_i hmid_q
          rw [← hl] at hnone ⊢
          have hsub : (wi - 1#64).toNat = k := by
            rw [BitVec.toNat_sub]
            change (18446744073709551615 + wi.toNat) % 18446744073709551616 = k
            have := wi.isLt; omega
          exact ih mid (wi - 1#64) wq1 hsub.symm (by omega) hmid_i hmid_q hmid_qle hnone

theorem div64by32_ret_q_le {F : Type} (s post : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (hrun : evaluateHOLFiniteState s div64Body = (some (.returned v), post)) :
    ∃ (wq : BitVec 64) (vr : ValueHOL 64), v = .rStruct [.val (.word wq), vr] ∧ wq.toNat ≤ 4294967295 := by
  have hb : div64Body =
      .dec (ofString "q") .one (.const 0#64)
        (.dec (ofString "r") .one (.var .local (ofString "hi"))
          (.dec (ofString "i") .one (.const 32#64) div64Inner)) := rfl
  have hrun1 : (evaluateHOLFiniteState s div64Body).1 = some (.returned v) := by rw [hrun]
  rw [hb, evaluateHOLFiniteState_dec_total] at hrun1
  dsimp only [evalHOLExact] at hrun1
  rw [if_pos (show shapeEqHOL ShapeHOL.one (shapeOfHOLExact (.val (.word 0#64))) = true by
    simp [shapeOfHOLExact, shapeEqHOL])] at hrun1
  dsimp only at hrun1
  let s1 := setVarHOLFinite (ofString "q") (.val (.word 0#64)) s
  change (evaluateHOLFiniteState s1 _).1 = some (.returned v) at hrun1
  rw [evaluateHOLFiniteState_dec_total] at hrun1
  dsimp only at hrun1
  split at hrun1
  · simp at hrun1
  · rename_i vhi _
    split at hrun1
    · dsimp only at hrun1
      let s2 := setVarHOLFinite (ofString "r") vhi s1
      change (evaluateHOLFiniteState s2 _).1 = some (.returned v) at hrun1
      rw [evaluateHOLFiniteState_dec_total] at hrun1
      dsimp only [evalHOLExact] at hrun1
      rw [if_pos (show shapeEqHOL ShapeHOL.one (shapeOfHOLExact (.val (.word 32#64))) = true by
        simp [shapeOfHOLExact, shapeEqHOL])] at hrun1
      dsimp only at hrun1
      let s3 := setVarHOLFinite (ofString "i") (.val (.word 32#64)) s2
      change (evaluateHOLFiniteState s3 div64Inner).1 = some (.returned v) at hrun1
      have hinner : div64Inner = .seq div64Loop (.return (.rstruct [.var .local (ofString "q"), .var .local (ofString "r")])) := rfl
      rw [hinner, evaluateHOLFiniteState_seq_line780] at hrun1
      cases hloop : evaluateHOLFiniteState s3 div64Loop with
      | mk rl mid =>
        rw [hloop] at hrun1
        cases rl with
        | some rl =>
          dsimp only at hrun1
          have hnc := evaluate_noReturn div64Loop rfl s3 v
          rw [hloop] at hnc
          exact absurd hrun1 hnc
        | none =>
          dsimp only at hrun1
          have hs3_i : s3.locals.lookup (ofString "i") = some (.val (.word 32#64)) := by
            simp [s3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          have hs3_q : s3.locals.lookup (ofString "q") = some (.val (.word 0#64)) := by
            simp [s3, s2, s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "i" ≠ ofString "q" by decide,
              show ofString "r" ≠ ofString "q" by decide]
          have hloop_none : (evaluateHOLFiniteState s3 div64Loop).1 = none := by rw [hloop]
          obtain ⟨wq', hmid_q, hwq'_le⟩ := div64Loop_q_le 32 s3 32#64 0#64 rfl (by decide)
            hs3_i hs3_q (by decide) hloop_none
          have hmid_q' : mid.locals.lookup (ofString "q") = some (.val (.word wq')) := by
            simpa [hloop] using hmid_q
          rw [evaluateHOLFiniteState_return] at hrun1
          cases hev : @evalHOLExact 64 F _ mid.toExact (fun a => Classical.propDecidable (mid.memaddrs a))
              (.rstruct [.var .local (ofString "q"), .var .local (ofString "r")]) with
          | none =>
            simp [hev] at hrun1
          | some val =>
            simp only [hev] at hrun1
            split at hrun1
            · have hv : v = val := (PanSemResultExact.returned.inj (Option.some.inj hrun1)).symm
              subst hv
              cases hmid_r : mid.locals.lookup (ofString "r") with
              | none => simp [evalHOLExact, evalListHOLExact, hmid_q', hmid_r] at hev
              | some vr =>
                have hval : v = .rStruct [.val (.word wq'), vr] := by
                  simpa [evalHOLExact, evalListHOLExact, hmid_q', hmid_r] using hev.symm
                exact ⟨wq', vr, hval, hwq'_le⟩
            · simp at hrun1
    · simp at hrun1

private theorem three_arg_lookup_div64by32
    {vals : List (ValueHOL 64)} {body' : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {ret' : ShapeHOL}
    (hl : PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup
      (ofString "div64by32") vals = some (body', callee, ret')) :
    body' = div64Body := by
  have hraw := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some _ _ _ _ _ _ hl
  simp only [lookupCodeHOLExact, lookup_div64by32_spec] at hraw
  split at hraw
  · exact (Prod.mk.inj (Option.some.inj hraw)).1.symm
  · cases hraw

/-! ### 6. Proofs of `fb_bn_mul`, `fb_bn_divmnu`, `fb_bn_mod`, and `fb_modexp` -/

private theorem assign_local_word_none' {F : Type} (s : PanSemStateFiniteExact 64 F)
    (name : MlS) (e : ExpHOL 64) (w : BitVec 64)
    (he : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e =
      some (.val (.word w)))
    (hnone : (evaluateHOLFiniteState s (.assign .local name e)).1 = none) :
    (evaluateHOLFiniteState s (.assign .local name e)).2 = setVarHOLFinite name (.val (.word w)) s := by
  rw [evaluateHOLFiniteState_assign] at hnone ⊢
  rw [he] at hnone ⊢
  dsimp only at hnone ⊢
  split at hnone
  · rename_i hv
    rw [if_pos hv]
    rfl
  · simp at hnone

theorem fb_bn_mul : TerminatingFunBoundedOn GuestInv (ofString "bn_mul") K.«bn_mul» := by
  fb_unfold 626 Guest.Software.guestFn_bn_mul
  apply TerminatingProgBoundedOn.weaken'
  · apply dec_guestInv
    apply TerminatingProgBoundedOn.seq_guestInv
    · exact while_scaled8_up_walk_guestInv (ofString "out") (ofString "i") _
        (straightOn _ rfl)
        (DomainTouch.seq _ _ _ (DomainTouch.store _ _ (WordExpression.const _)))
        (by counter_step) (by decide)
    · apply TerminatingProgBoundedOn.seq_guestInv
      · exact straightOn _ rfl
      · apply TerminatingProgBoundedOn.seq_guestInv
        · refine while_scaled8_up_walk_guestInv (ofString "a") (ofString "i") _
            (dec_guestInv _ _ _ (dec_guestInv _ _ _ (dec_guestInv _ _ _ (dec_guestInv _ _ _
              (TerminatingProgBoundedOn.seq_guestInv
                (while_scaled8_up_walk_guestInv (ofString "o") (ofString "j") _
                  (dec_guestInv _ _ _ (straightOn _ rfl))
                  (DomainTouch.dec_op3_mid_load_one _ _ _ _ _ _)
                  (by counter_step) (by decide))
                (straightOn _ rfl))))))
            (DomainTouch.dec_load_one _ _ _)
            (by counter_step) (by decide)
        · exact straightOn _ rfl
  · unfold K.«bn_mul»
    rw [domainBytes_eq]

private def divmnuBody : ProgHOL 64 :=
  InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural
    (extractFn Guest.Software.guestFn_bn_divmnu).body

private def divmnuLoop3Tail : ProgHOL 64 :=
  match divmnuBody with
  | .dec _ _ _ (.dec _ _ _ (.seq _ (.decCall _ _ _ _ (.seq _ (.seq _ (.seq _ (.seq _ (.seq _ (.seq _ (.seq _
      (.dec _ _ _ (.dec _ _ _ (.seq _ (.seq (.while _ (.seq _ tail)) _)))))))))))))) => tail
  | _ => .skip

theorem glo_qhatCapInv : GuestLocalsOnly ["qhat"] QhatCapInv where
  toGuest := fun _ h => h.1
  congr := fun _ _ hg hk ⟨_, hq⟩ => ⟨hg, by simpa [locN, hk "qhat" (by simp)] using hq⟩

private theorem divmnuLoop3Tail_bound :
    TerminatingProgBoundedOn GuestInv divmnuLoop3Tail
      (max 0 (K.«div64by32» + 0 + 1) +
        ((4294967296 + 1) * (0 + 1) +
          (0 + ((domainBytes + 16 + 1) * (0 + 1) +
            max (0 + (0 + (0 + ((domainBytes + 16 + 1) * (0 + 1) + 0)))) 0)))) := by
  dsimp only [divmnuLoop3Tail, divmnuBody, extractFn, Guest.Software.guestFn_bn_divmnu,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural, List.map, Option.map]
  apply dec_guestInv
  apply dec_guestInv
  apply dec_guestInv
  apply dec_guestInv
  apply dec_guestInv
  apply seq_step_on (P := GuestInv) (Q := QhatCapInv)
  · apply TerminatingProgBoundedOn.ite_on
    · exact straightOn _ rfl
    · exact decCall_guestInv' fb_div64by32 (straightOn _ rfl)
  · intro F s hcode hg hnone
    refine ⟨guestInv_evaluate s _ hg, ?_⟩
    rw [evaluateHOLFiniteState_ite] at hnone ⊢
    split at hnone
    · split at hnone
      · rename_i hcond_zero
        simp only [hcond_zero, ↓reduceIte] at hnone ⊢
        cases hdc_full : evaluateHOLFiniteState s _ with
        | mk rdc postDC =>
          rw [hdc_full] at hnone
          dsimp only at hnone ⊢
          subst hnone
          rw [evaluateHOLFiniteState_decCall_total] at hdc_full
          cases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) _ with
          | none => rw [hargs] at hdc_full; simp at hdc_full
          | some vals =>
            rw [hargs] at hdc_full; dsimp only at hdc_full
            cases hl : lookupCodeHOLFinite s.code.lookup (ofString "div64by32") vals with
            | none => rw [hl] at hdc_full; simp at hdc_full
            | some installed =>
              rcases installed with ⟨body', callee, ret'⟩
              rw [hl] at hdc_full; dsimp only at hdc_full
              split at hdc_full
              · simp at hdc_full
              · cases hbodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with
                | mk rb pb =>
                  rw [hbodyRun] at hdc_full
                  have hrem := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite s callee) body'
                  rw [hbodyRun] at hrem
                  simp only [fixClockHOLFinite, Nat.not_lt.mpr hrem, ↓reduceIte] at hdc_full
                  cases rb with
                  | none => simp at hdc_full
                  | some rb =>
                    cases rb with
                    | returned vret =>
                      simp only at hdc_full
                      split at hdc_full
                      · have hb_eq : body' = div64Body := by
                          rw [hcode] at hl
                          exact three_arg_lookup_div64by32 hl
                        subst hb_eq
                        obtain ⟨wq, vr, rfl, hwq_le⟩ := div64by32_ret_q_le _ pb vret hbodyRun
                        let res0 := setVarHOLFinite (ofString "qr") (.rStruct [.val (.word wq), vr]) { pb with locals := s.locals }
                        let contProg : ProgHOL 64 :=
                          .seq (.assign .local (ofString "qhat") (.rfield 0 (.var .local (ofString "qr"))))
                               (.assign .local (ofString "rhat") (.rfield 1 (.var .local (ofString "qr"))))
                        cases hcont : evaluateHOLFiniteState res0 contProg with
                        | mk rc inner =>
                          rw [hcont] at hdc_full
                          have hrc_none : rc = none := (Prod.mk.inj hdc_full).1
                          subst hrc_none
                          have hpost_locals : postDC.locals =
                              HolFiniteMapExact.resVarEq inner.locals (ofString "qr", s.locals.lookup (ofString "qr")) := by
                            have hp := (Prod.mk.inj hdc_full).2
                            rw [← hp]
                          rw [show contProg = .seq (.assign .local (ofString "qhat") (.rfield 0 (.var .local (ofString "qr"))))
                            (.assign .local (ofString "rhat") (.rfield 1 (.var .local (ofString "qr")))) from rfl,
                            evaluateHOLFiniteState_seq_line780] at hcont
                          cases hc1 : evaluateHOLFiniteState res0
                              (.assign .local (ofString "qhat") (.rfield 0 (.var .local (ofString "qr")))) with
                          | mk rc1 mid =>
                            rw [hc1] at hcont
                            dsimp only at hcont
                            cases rc1 with
                            | some _ =>
                              dsimp only at hcont
                              cases hcont
                            | none =>
                              dsimp only at hcont
                              have hc1_none : (evaluateHOLFiniteState res0 (.assign .local (ofString "qhat") (.rfield 0 (.var .local (ofString "qr"))))).1 = none := by rw [hc1]
                              have he_wq : @evalHOLExact 64 F _ res0.toExact (fun a => Classical.propDecidable (res0.memaddrs a))
                                  (.rfield 0 (.var .local (ofString "qr"))) = some (.val (.word wq)) := by
                                simp [evalHOLExact, res0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                              have hmid_eq := assign_local_word_none' res0 (ofString "qhat") _ wq he_wq hc1_none
                              rw [hc1] at hmid_eq
                              dsimp only at hmid_eq
                              have hmid_q : mid.locals.lookup (ofString "qhat") = some (.val (.word wq)) := by
                                rw [hmid_eq]
                                simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                              have hc2_none : (evaluateHOLFiniteState mid (.assign .local (ofString "rhat") (.rfield 1 (.var .local (ofString "qr"))))).1 = none := by
                                rw [hcont]
                              have hk := evaluate_avoidsLocal_flowing (ofString "qhat")
                                (.assign .local (ofString "rhat") (.rfield 1 (.var .local (ofString "qr"))))
                                (by decide) mid (Or.inl hc2_none)
                              rw [hcont] at hk
                              dsimp only at hk
                              have hpost_q : postDC.locals.lookup (ofString "qhat") = some (.val (.word wq)) := by
                                rw [hpost_locals, PanRunBounded.resVarEq_lookup]
                                simp [show ofString "qhat" ≠ ofString "qr" by decide, hk.trans hmid_q]
                              unfold locN
                              rw [hpost_q]
                              exact hwq_le
                      · simp at hdc_full
                    | _ => simp at hdc_full
      · rename_i hcond_nz
        simp only [hcond_nz, ↓reduceIte] at hnone ⊢
        rw [evaluateHOLFiniteState_seq_line780] at hnone ⊢
        cases ha1 : evaluateHOLFiniteState s
            (.assign .local (ofString "qhat") (.const 4294967295#64)) with
        | mk ra1 mid =>
          rw [ha1] at hnone
          dsimp only at hnone ⊢
          cases ra1 with
          | some _ => cases hnone
          | none =>
            dsimp only at hnone ⊢
            have hmid_q : mid.locals.lookup (ofString "qhat") = some (.val (.word 4294967295#64)) := by
              have h1none : (evaluateHOLFiniteState s (.assign .local (ofString "qhat") (.const 4294967295#64))).1 = none := by rw [ha1]
              have h1st := assign_local_word_none' s (ofString "qhat") (.const 4294967295#64) 4294967295#64 rfl h1none
              rw [ha1] at h1st
              dsimp only at h1st
              rw [h1st]
              simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
            have hk := evaluate_avoidsLocal_flowing (ofString "qhat") _ (by decide) mid (Or.inl hnone)
            unfold locN
            rw [hk.trans hmid_q]
            decide
    · simp at hnone
  · apply dec_avoids_on glo_qhatCapInv _ (by decide)
    apply seq_to_guestInv (fun _ h => h.1)
    · exact knuthCorrection_capped_bound
    · apply dec_guestInv
      apply TerminatingProgBoundedOn.seq_guestInv
      · exact straightOn _ rfl
      · apply TerminatingProgBoundedOn.seq_guestInv
        · exact while_scaled8_up_walk_guestInv (ofString "vn") (ofString "i") _
            (dec_guestInv _ _ _ (dec_guestInv _ _ _ (straightOn _ rfl)))
            (DomainTouch.dec_panop_mul_load_one _ _ _ _)
            (by counter_step) (by decide)
        · apply dec_guestInv
          apply TerminatingProgBoundedOn.ite_on
          · apply TerminatingProgBoundedOn.seq_guestInv
            · exact straightOn _ rfl
            · apply TerminatingProgBoundedOn.seq_guestInv
              · exact straightOn _ rfl
              · apply TerminatingProgBoundedOn.seq_guestInv
                · exact straightOn _ rfl
                · apply TerminatingProgBoundedOn.seq_guestInv
                  · exact while_scaled8_up_walk_guestInv (ofString "vn") (ofString "i") _
                      (dec_guestInv _ _ _ (straightOn _ rfl))
                      (DomainTouch.dec_op3_mid_load_one _ _ _ _ _ _)
                      (by counter_step) (by decide)
                  · exact straightOn _ rfl
          · exact straightOn _ rfl

theorem fb_bn_divmnu : TerminatingFunBoundedOn GuestInv (ofString "bn_divmnu") K.«bn_divmnu» := by
  have _ := fb_div64by32
  have _ := fb_nlz32
  fb_unfold 627 Guest.Software.guestFn_bn_divmnu
  apply TerminatingProgBoundedOn.weaken'
  · apply dec_guestInv
    apply dec_guestInv
    apply TerminatingProgBoundedOn.seq_guestInv
    · apply TerminatingProgBoundedOn.ite_on
      · apply dec_guestInv
        apply dec_guestInv
        apply TerminatingProgBoundedOn.seq_guestInv
        · exact straightOn _ rfl
        · apply TerminatingProgBoundedOn.seq_guestInv
          · exact while_scaled8_predec_down_guestInv (ofString "u") (ofString "j") _
              (decCall_guestInv' fb_div64by32 (straightOn _ rfl))
              (DomainTouch.decCall_arg2_load_one _ _ _ _ _ _ _)
              (by decide) (by decide) (by decide)
          · exact straightOn _ rfl
      · exact straightOn _ rfl
    · apply decCall_guestInv' fb_nlz32
      apply TerminatingProgBoundedOn.seq_guestInv
      · exact straightOn _ rfl
      · apply TerminatingProgBoundedOn.seq_guestInv
        · exact while_scaled8_down16_guestInv (ofString "vn") (ofString "i") _
            (straightOn _ rfl)
            (DomainTouch.seq _ _ _ (DomainTouch.store _ _ (WordExpression.op _ _)))
            (by counter_step) (by decide)
        · apply TerminatingProgBoundedOn.seq_guestInv
          · exact straightOn _ rfl
          · apply TerminatingProgBoundedOn.seq_guestInv
            · exact straightOn _ rfl
            · apply TerminatingProgBoundedOn.seq_guestInv
              · exact straightOn _ rfl
              · apply TerminatingProgBoundedOn.seq_guestInv
                · exact while_scaled8_down16_guestInv (ofString "un") (ofString "i") _
                    (straightOn _ rfl)
                    (DomainTouch.seq _ _ _ (DomainTouch.store _ _ (WordExpression.op _ _)))
                    (by counter_step) (by decide)
                · apply TerminatingProgBoundedOn.seq_guestInv
                  · exact straightOn _ rfl
                  · apply dec_guestInv
                    apply dec_guestInv
                    apply TerminatingProgBoundedOn.seq_guestInv
                    · exact straightOn _ rfl
                    · apply TerminatingProgBoundedOn.seq_guestInv
                      · exact while_scaled8_predec_add_cell_guestInv
                          (ofString "un") (ofString "j") (ofString "n") _
                          divmnuLoop3Tail_bound
                          (DomainTouch.dec_load_one _ _ _)
                          (by decide) (by decide) (by decide) (by decide) (by decide)
                      · apply TerminatingProgBoundedOn.seq_guestInv
                        · exact straightOn _ rfl
                        · apply TerminatingProgBoundedOn.seq_guestInv
                          · exact while_scaled8_up_walk_guestInv (ofString "q") (ofString "j") _
                              (straightOn _ rfl)
                              (DomainTouch.seq _ _ _ (DomainTouch.store _ _ (WordExpression.const _)))
                              (by counter_step) (by decide)
                          · apply TerminatingProgBoundedOn.seq_guestInv
                            · exact straightOn _ rfl
                            · apply TerminatingProgBoundedOn.seq_guestInv
                              · exact while_scaled8_up_walk_guestInv (ofString "r") (ofString "i") _
                                  (straightOn _ rfl)
                                  (DomainTouch.seq _ _ _ (DomainTouch.store _ _ (WordExpression.op _ _)))
                                  (by counter_step) (by decide)
                              · exact straightOn _ rfl
  · unfold K.«bn_divmnu» K.«div64by32» K.«nlz32»
    rw [domainBytes_eq]
    simp only [nat_max_eq]
    decide

theorem fb_bn_mod : TerminatingFunBoundedOn GuestInv (ofString "bn_mod") K.«bn_mod» := by
  have _ := fb_digits_len
  have _ := fb_memcpy
  have _ := fb_memzero
  have _ := fb_bn_divmnu
  fb_prove 628 Guest.Software.guestFn_bn_mod K.«bn_mod»

theorem fb_modexp : TerminatingFunBoundedOn GuestInv (ofString "modexp") K.«modexp» :=
  FastGen.fb_modexp_of fb_bn_mod fb_bn_mul

end InitECandidate.Solver.Wave8GuestInv.R16ArithPort
