import InitECandidate.Solver.Wave8GuestInv.ContractParts.C04
import InitECandidate.Solver.Wave8GuestInv.ContractParts.C07
import InitECandidate.Solver.Wave8GuestInv.R13Shards.Common
import InitECandidate.Solver.Wave8GuestInv.R13Shards.WkKeccak256

/-! Standalone proof of `ww_mpt_nibble_key` plus reusable `key_to_nibbles` / `alloc`
write-frame helpers for `R16e-M4b-M1r2-HtabUnion`. -/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2000
set_option linter.style.nameCheck false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards

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
open InitECandidate.Solver.Wave8GuestInv.R13Shards.Keccak256

theorem lookup_resVarEq_ne (m : HolFiniteMapExact MlS (ValueHOL 64))
    (x k : MlS) (ox : Option (ValueHOL 64)) (hne : k ≠ x) :
    (m.resVarEq (x, ox)).lookup k = m.lookup k := by
  simp only [HolFiniteMapExact.resVarEq]
  cases ox <;> simp [FDOMSUB_HOL, FUPDATE_HOL, hne, Ne.symm hne]

private def KeyNibInv {F : Type} (s0 : PanSemStateFiniteExact 64 F)
    (key0 n0 out0 : BitVec 64) (s : PanSemStateFiniteExact 64 F) : Prop :=
  s.code = originalRuntimeCode ∧ GuestInv s ∧
  ByteEff s0 s [(out0.toNat, 2 * n0.toNat)] ∧
  s.locals.lookup (ofString "key") = some (.val (.word key0)) ∧
  s.locals.lookup (ofString "n") = some (.val (.word n0)) ∧
  s.locals.lookup (ofString "out") = some (.val (.word out0)) ∧
  ∃ iw : BitVec 64,
    s.locals.lookup (ofString "i") = some (.val (.word iw)) ∧
    iw.toNat ≤ n0.toNat ∧
    (0 < iw.toNat → sourceBase ≤ out0.toNat ∧ out0.toNat + 2 * iw.toNat ≤ heapEnd)

private theorem noRetOrRaise_seq {F : Type} {a b : ProgHOL 64} {s : PanSemStateFiniteExact 64 F}
    (ha : ¬ Resumes (evaluateHOLFiniteState s a).1)
    (hb : ∀ m, (evaluateHOLFiniteState s a) = (none, m) → ¬ Resumes (evaluateHOLFiniteState m b).1) :
    ¬ Resumes (evaluateHOLFiniteState s (.seq a b)).1 := by
  rw [evaluateHOLFiniteState_seq_line780]
  rcases hr : evaluateHOLFiniteState s a with ⟨r1, m⟩
  rw [hr] at ha
  cases r1 with
  | none => exact hb m hr
  | some _ => exact ha

private theorem noRetOrRaise_storeByte {F : Type} (s : PanSemStateFiniteExact 64 F) (d e : ExpHOL 64) :
    ¬ Resumes (evaluateHOLFiniteState s (.storeByte d e)).1 := by
  rw [evaluateHOLFiniteState_storeByte]
  repeat' split
  all_goals (rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)

private theorem noRetOrRaise_assign {F : Type} (s : PanSemStateFiniteExact 64 F) (k : VarKind) (nm : MlS) (e : ExpHOL 64) :
    ¬ Resumes (evaluateHOLFiniteState s (.assign k nm e)).1 := by
  rw [evaluateHOLFiniteState_assign]
  repeat' split
  all_goals (rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)

private theorem noRetOrRaise_dec {F : Type} (s : PanSemStateFiniteExact 64 F) (nm : MlS) (sh : ShapeHOL) (e : ExpHOL 64)
    {b : ProgHOL 64} (hb : ∀ v, ¬ Resumes (evaluateHOLFiniteState (setVarHOLFinite nm v s) b).1) :
    ¬ Resumes (evaluateHOLFiniteState s (.dec nm sh e b)).1 := by
  rw [evaluateHOLFiniteState_dec_total]; dsimp only
  split
  · exact not_resumes_error
  · rename_i v _; split
    · exact hb v
    · exact not_resumes_error

private theorem noRetOrRaise_while {F : Type} (cond : ExpHOL 64) (body : ProgHOL 64)
    (hb : ∀ t : PanSemStateFiniteExact 64 F, ¬ Resumes (evaluateHOLFiniteState t body).1)
    (k : Nat) (s : PanSemStateFiniteExact 64 F) (hk : s.clock ≤ k) :
    ¬ Resumes (evaluateHOLFiniteState s (.while cond body)).1 := by
  induction k generalizing s with
  | zero =>
    rw [evaluateHOLFiniteState_while_total]
    repeat' split
    all_goals (try omega)
    all_goals (rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h)
  | succ k ih =>
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
        · dsimp only; rw [fixClockHOLFinite_evaluateState]
          have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
          have hnb := hb (decClockHOLFinite s)
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨r1, mid⟩
          rw [hbr] at rem hnb
          have hlt : mid.clock ≤ k := by change mid.clock ≤ s.clock - 1 at rem; omega
          cases r1 with
          | none => exact ih mid hlt
          | some res =>
            cases res with
            | «continue» => exact ih mid hlt
            | «break» => rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
            | _ => exact hnb
      · rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> simp at h
    · exact not_resumes_error

private theorem while_keyNibInv {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {key0 n0 out0 : BitVec 64}
    (cond : ExpHOL 64) (body : ProgHOL 64)
    (hnobc : ∀ t : PanSemStateFiniteExact 64 F,
      (evaluateHOLFiniteState t body).1 ≠ some .break ∧
      (evaluateHOLFiniteState t body).1 ≠ some .continue)
    (hstep : ∀ (s : PanSemStateFiniteExact 64 F) (cw : BitVec 64),
      KeyNibInv s0 key0 n0 out0 s →
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) cond =
        some (.val (.word cw)) → cw ≠ 0 →
      (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = none →
      KeyNibInv s0 key0 n0 out0 (evaluateHOLFiniteState (decClockHOLFinite s) body).2)
    (k : Nat) (s post : PanSemStateFiniteExact 64 F) (hk : s.clock ≤ k)
    (hinv : KeyNibInv s0 key0 n0 out0 s)
    (hrun : evaluateHOLFiniteState s (.while cond body) = (none, post)) :
    KeyNibInv s0 key0 n0 out0 post ∧
    @evalHOLExact 64 F _ post.toExact (fun a => Classical.propDecidable (post.memaddrs a)) cond =
      some (.val (.word 0)) := by
  induction k generalizing s with
  | zero =>
    rw [evaluateHOLFiniteState_while_total] at hrun
    split at hrun
    · rename_i cw hcond
      split at hrun
      · split at hrun <;> [simp at hrun; omega]
      · rename_i hnotnz
        have hcw0 : cw = 0 := Classical.not_not.1 hnotnz
        subst hcw0; simp at hrun; subst hrun; exact ⟨hinv, hcond⟩
    · simp at hrun
  | succ k ih =>
    rw [evaluateHOLFiniteState_while_total] at hrun
    split at hrun
    · rename_i cw hcond
      split at hrun
      · rename_i hnz
        split at hrun
        · simp at hrun
        · dsimp only at hrun
          rw [fixClockHOLFinite_evaluateState] at hrun
          have rem := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) body
          have hbc := hnobc (decClockHOLFinite s)
          rcases hbr : evaluateHOLFiniteState (decClockHOLFinite s) body with ⟨r1, mid⟩
          rw [hbr] at hrun rem hbc
          cases r1 with
          | none =>
            have hmid : KeyNibInv s0 key0 n0 out0 mid := by
              have hb := hstep s cw hinv hcond hnz (by rw [hbr])
              rw [hbr] at hb; exact hb
            exact ih mid (by change mid.clock ≤ s.clock - 1 at rem; omega) hmid hrun
          | some r1 =>
            cases r1 with
            | «continue» => exact absurd rfl hbc.2
            | «break» => exact absurd rfl hbc.1
            | _ => simp at hrun
      · rename_i hnotnz
        have hcw0 : cw = 0 := Classical.not_not.1 hnotnz
        subst hcw0; simp at hrun; subst hrun; exact ⟨hinv, hcond⟩
    · simp at hrun

private theorem dec_none_inv {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {nm : MlS} {e : ExpHOL 64} {b : ProgHOL 64}
    (h : evaluateHOLFiniteState s (.dec nm .one e b) = (none, post)) :
    ∃ w : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e =
        some (.val (.word w)) ∧
      (evaluateHOLFiniteState (setVarHOLFinite nm (.val (.word w)) s) b).1 = none ∧
      post = { (evaluateHOLFiniteState (setVarHOLFinite nm (.val (.word w)) s) b).2 with
        locals := HolFiniteMapExact.resVarEq
          (evaluateHOLFiniteState (setVarHOLFinite nm (.val (.word w)) s) b).2.locals
          (nm, s.locals.lookup nm) } := by
  rw [evaluateHOLFiniteState_dec_total] at h; dsimp only at h
  split at h
  · simp at h
  · rename_i v hv
    split at h
    · rename_i hsh
      rcases v with ⟨⟨w⟩⟩ | _ | _ <;> simp [shapeEqHOL, shapeOfHOLExact] at hsh
      refine ⟨w, hv, ?_, ?_⟩
      · injection h
      · injection h with _ hp; exact hp.symm
    · simp at h

private theorem seq_storeByte_none_inv {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} {d e : ExpHOL 64} {b : ProgHOL 64}
    (hG : GuestInv s) (addr : BitVec 64)
    (hd : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) d =
      some (.val (.word addr)))
    (hin : sourceBase ≤ addr.toNat → addr.toNat + 1 ≤ heapEnd → ∃ iv ∈ Rl, InIvl addr.toNat iv)
    (h : evaluateHOLFiniteState s (.seq (.storeByte d e) b) = (none, post)) :
    ∃ mid : PanSemStateFiniteExact 64 F,
      sourceBase ≤ addr.toNat ∧ addr.toNat + 1 ≤ heapEnd ∧
      ByteEff s mid Rl ∧ mid.locals = s.locals ∧ mid.code = s.code ∧ GuestInv mid ∧
      evaluateHOLFiniteState mid b = (none, post) := by
  rw [evaluateHOLFiniteState_seq_line780] at h
  have hbs := byteEff_storeByte (Rl := Rl) hG d e (fun x hx hdom => by
    rw [hd] at hx; cases hx
    have hord : (panByteAlignHOL addr).toNat % 8 = 0 ∧
        sourceBase ≤ (panByteAlignHOL addr).toNat ∧ (panByteAlignHOL addr).toNat < heapEnd := by
      rwa [hG.memaddrs, ordinaryDomain_iff] at hdom
    have hhe8 : heapEnd % 8 = 0 := by decide
    have hsb8 : sourceBase % 8 = 0 := by decide
    have hal := panByteAlign_toNat64 addr
    exact hin (by omega) (by omega))
  rcases h1 : evaluateHOLFiniteState s (.storeByte d e) with ⟨r1, mid⟩
  rw [h1] at h hbs
  cases r1 with
  | some _ => simp at h
  | none =>
    obtain ⟨x, hx, hlo, hhi⟩ := hbs.2 rfl
    rw [hd] at hx; cases hx
    have hloc : mid.locals = s.locals := by
      rw [evaluateHOLFiniteState_storeByte] at h1
      revert h1; repeat' split
      all_goals intro h1 <;> injection h1 with _ hm <;> subst hm <;> rfl
    exact ⟨mid, hlo, hhi, hbs.1, hloc, hbs.1.code,
      guestInv_congr hbs.1.code hbs.1.memaddrs hbs.1.shMemaddrs hbs.1.baseAddr hG, h⟩

private theorem one_byte_nibbles_step {F : Type} {s0 s post : PanSemStateFiniteExact 64 F}
    {key0 n0 out0 iw : BitVec 64} (bnm : MlS) (kOff : ExpHOL 64)
    (outOff0 outOff1 : ExpHOL 64) (d0 : Nat) {rest : ProgHOL 64}
    (hb_ne_out : bnm ≠ ofString "out") (hb_ne_i : bnm ≠ ofString "i")
    (hb_ne_key : bnm ≠ ofString "key") (hb_ne_n : bnm ≠ ofString "n")
    (hc : s.code = originalRuntimeCode) (hG : GuestInv s)
    (heff : ByteEff s0 s [(out0.toNat, 2 * n0.toNat)])
    (hk : s.locals.lookup (ofString "key") = some (.val (.word key0)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n0)))
    (ho : s.locals.lookup (ofString "out") = some (.val (.word out0)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iw)))
    (ho0 : ∀ bw : BitVec 64,
      let sb := setVarHOLFinite bnm (.val (.word bw)) s
      @evalHOLExact 64 F _ sb.toExact (fun a => Classical.propDecidable (sb.memaddrs a)) outOff0 =
        some (.val (.word (out0 + 2#64 * iw + BitVec.ofNat 64 d0))))
    (ho1 : ∀ (bw : BitVec 64) (m : PanSemStateFiniteExact 64 F),
      m.locals = (setVarHOLFinite bnm (.val (.word bw)) s).locals →
      @evalHOLExact 64 F _ m.toExact (fun a => Classical.propDecidable (m.memaddrs a)) outOff1 =
        some (.val (.word (out0 + 2#64 * iw + BitVec.ofNat 64 (d0 + 1)))))
    (hin0 : sourceBase ≤ (out0 + 2#64 * iw + BitVec.ofNat 64 d0).toNat →
      (out0 + 2#64 * iw + BitVec.ofNat 64 d0).toNat + 1 ≤ heapEnd →
      InIvl (out0 + 2#64 * iw + BitVec.ofNat 64 d0).toNat (out0.toNat, 2 * n0.toNat))
    (hin1 : sourceBase ≤ (out0 + 2#64 * iw + BitVec.ofNat 64 d0).toNat →
      (out0 + 2#64 * iw + BitVec.ofNat 64 d0).toNat + 1 ≤ heapEnd →
      sourceBase ≤ (out0 + 2#64 * iw + BitVec.ofNat 64 (d0 + 1)).toNat →
      (out0 + 2#64 * iw + BitVec.ofNat 64 (d0 + 1)).toNat + 1 ≤ heapEnd →
      InIvl (out0 + 2#64 * iw + BitVec.ofNat 64 (d0 + 1)).toNat (out0.toNat, 2 * n0.toNat))
    (hrun : evaluateHOLFiniteState s
      (.dec bnm .one (.loadByte kOff)
        (.seq (.storeByte outOff0 (.shift .lsr (.var .local bnm) (.const 4)))
          (.seq (.storeByte outOff1 (.op .and [.var .local bnm, .const 15]))
            rest))) = (none, post)) :
    ∃ m2 : PanSemStateFiniteExact 64 F,
      sourceBase ≤ (out0 + 2#64 * iw + BitVec.ofNat 64 d0).toNat ∧
      (out0 + 2#64 * iw + BitVec.ofNat 64 d0).toNat + 1 ≤ heapEnd ∧
      sourceBase ≤ (out0 + 2#64 * iw + BitVec.ofNat 64 (d0 + 1)).toNat ∧
      (out0 + 2#64 * iw + BitVec.ofNat 64 (d0 + 1)).toNat + 1 ≤ heapEnd ∧
      m2.code = originalRuntimeCode ∧ GuestInv m2 ∧
      ByteEff s0 m2 [(out0.toNat, 2 * n0.toNat)] ∧
      m2.locals.lookup (ofString "key") = some (.val (.word key0)) ∧
      m2.locals.lookup (ofString "n") = some (.val (.word n0)) ∧
      m2.locals.lookup (ofString "out") = some (.val (.word out0)) ∧
      m2.locals.lookup (ofString "i") = some (.val (.word iw)) ∧
      (evaluateHOLFiniteState m2 rest).1 = none ∧
      post = { (evaluateHOLFiniteState m2 rest).2 with
        locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState m2 rest).2.locals
          (bnm, s.locals.lookup bnm) } := by
  obtain ⟨bw, _, hrest1, hpost_eq⟩ := dec_none_inv hrun
  set sb := setVarHOLFinite bnm (.val (.word bw)) s
  have hG_sb : GuestInv sb := guestInv_setVar _ _ s hG
  have heff_sb : ByteEff s0 sb [(out0.toNat, 2 * n0.toNat)] := heff.locals_clock _ s.clock
  rcases h_eq : evaluateHOLFiniteState sb
      (.seq (.storeByte outOff0 (.shift .lsr (.var .local bnm) (.const 4)))
        (.seq (.storeByte outOff1 (.op .and [.var .local bnm, .const 15])) rest)) with ⟨r_end, p_end⟩
  have hr_none : r_end = none := by rw [h_eq] at hrest1; exact hrest1
  subst hr_none
  obtain ⟨m1, hlo0, hhi0, heff1, hloc1, hc1, hG1, hseq2⟩ :=
    seq_storeByte_none_inv (Rl := [(out0.toNat, 2 * n0.toNat)]) hG_sb
      (out0 + 2#64 * iw + BitVec.ofNat 64 d0) (ho0 bw)
      (fun h1 h2 => ⟨_, List.mem_singleton.mpr rfl, hin0 h1 h2⟩) h_eq
  obtain ⟨m2, hlo1, hhi1, heff2, hloc2, hc2, hG2, hrest2⟩ :=
    seq_storeByte_none_inv (Rl := [(out0.toNat, 2 * n0.toNat)]) hG1
      (out0 + 2#64 * iw + BitVec.ofNat 64 (d0 + 1)) (ho1 bw m1 hloc1)
      (fun h1 h2 => ⟨_, List.mem_singleton.mpr rfl, hin1 hlo0 hhi0 h1 h2⟩) hseq2
  have hloc_m2 : m2.locals = sb.locals := hloc2.trans hloc1
  refine ⟨m2, hlo0, hhi0, hlo1, hhi1, hc2.trans (hc1.trans hc), hG2,
    (heff_sb.trans heff1).trans heff2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hloc_m2]; simp [sb, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hk, hb_ne_key]
  · rw [hloc_m2]; simp [sb, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn, hb_ne_n]
  · rw [hloc_m2]; simp [sb, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ho, hb_ne_out]
  · rw [hloc_m2]; simp [sb, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hi, hb_ne_i]
  · rw [hrest2]
  · rw [hpost_eq, h_eq, hrest2]

private theorem nib_addr_nowrap (out0 iw n0 : BitVec 64) (step : Nat)
    (hprev : 0 < iw.toNat → sourceBase ≤ out0.toNat ∧ out0.toNat + 2 * iw.toNat ≤ heapEnd)
    (hstep_cond : iw.toNat + step ≤ n0.toNat ∨ ¬ (n0 < iw + BitVec.ofNat 64 step))
    (hstep_le : step ≤ 4) (hstep_pos : 0 < step)
    (h0_lo : sourceBase ≤ (out0 + 2#64 * iw + 0#64).toNat)
    (h0_hi : (out0 + 2#64 * iw + 0#64).toNat + 1 ≤ heapEnd) :
    (2#64 * iw).toNat = 2 * iw.toNat ∧
    (out0 + 2#64 * iw).toNat = out0.toNat + 2 * iw.toNat ∧
    (iw + BitVec.ofNat 64 step).toNat = iw.toNat + step ∧
    iw.toNat + step ≤ n0.toNat ∧
    sourceBase ≤ out0.toNat ∧
    ∀ d : Nat, d < 2 * step →
      (out0 + 2#64 * iw + BitVec.ofNat 64 d).toNat = out0.toNat + 2 * iw.toNat + d ∧
      InIvl (out0 + 2#64 * iw + BitVec.ofNat 64 d).toNat (out0.toNat, 2 * n0.toNat) := by
  have hsb : sourceBase = 2701131776 := rfl
  have hhe : heapEnd = 33806089704 := by decide
  rw [BitVec.add_zero] at h0_lo h0_hi
  have holt := out0.isLt; have hilt := iw.isLt; have hnlt := n0.isLt
  by_cases hiz : iw.toNat = 0
  · have hi0 : iw = 0 := BitVec.eq_of_toNat_eq hiz
    subst hi0
    have hz : 2#64 * (0 : BitVec 64) = (0 : BitVec 64) := rfl
    have hao : out0 + (0 : BitVec 64) = out0 := BitVec.add_zero out0
    rw [hz, hao] at h0_lo h0_hi ⊢
    have h0_nat : (0 : BitVec 64).toNat = 0 := rfl
    have hstep_bv : ((0 : BitVec 64) + BitVec.ofNat 64 step).toNat = step := by
      rw [zero_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hle_n : step ≤ n0.toNat := by
      rcases hstep_cond with h | h
      · omega
      · rw [BitVec.lt_def, hstep_bv] at h; omega
    refine ⟨rfl, by simp [h0_nat], by omega, by omega, h0_lo, fun d hd => ?_⟩
    have hd_nat : (BitVec.ofNat 64 d).toNat = d := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hadd_d : (out0 + BitVec.ofNat 64 d).toNat = out0.toNat + d := by
      rw [BitVec.toNat_add, hd_nat, Nat.mod_eq_of_lt (by omega)]
    rw [hadd_d, h0_nat]
    exact ⟨by omega, ⟨by omega, by omega⟩⟩
  · obtain ⟨hdlo, hdhi⟩ := hprev (by omega)
    have h2i : (2#64 * iw).toNat = 2 * iw.toNat := by
      rw [BitVec.toNat_mul]
      have h2_nat : (2#64).toNat = 2 := rfl
      rw [h2_nat, Nat.mod_eq_of_lt (by omega)]
    have ho2i : (out0 + 2#64 * iw).toNat = out0.toNat + 2 * iw.toNat := by
      rw [BitVec.toNat_add, h2i, Nat.mod_eq_of_lt (by omega)]
    have his : (iw + BitVec.ofNat 64 step).toNat = iw.toNat + step := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    have hle_n : iw.toNat + step ≤ n0.toNat := by
      rcases hstep_cond with h | h
      · exact h
      · rw [BitVec.lt_def, his] at h; omega
    refine ⟨h2i, ho2i, his, hle_n, hdlo, fun d hd => ?_⟩
    have hadd_d : (out0 + 2#64 * iw + BitVec.ofNat 64 d).toNat = out0.toNat + 2 * iw.toNat + d := by
      rw [BitVec.toNat_add, ho2i, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hadd_d]
    exact ⟨rfl, ⟨by omega, by omega⟩⟩

private theorem eval_out_2i {F : Type} (s : PanSemStateFiniteExact 64 F) (out0 iw : BitVec 64)
    (ho : s.locals.lookup (ofString "out") = some (.val (.word out0)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iw))) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .local (ofString "out"), .panop .mul [.const 2, .var .local (ofString "i")]]) =
      some (.val (.word (out0 + 2#64 * iw + 0#64))) := by
  simp [evalHOLExact, evalListHOLExact, ho, hi, valueIsWord, valueWord, panOpHOL, wordOpHOL, wordOp]

private theorem eval_out_2i_c {F : Type} (s : PanSemStateFiniteExact 64 F) (out0 iw : BitVec 64) (d : Nat)
    (ho : s.locals.lookup (ofString "out") = some (.val (.word out0)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iw))) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .local (ofString "out"), .panop .mul [.const 2, .var .local (ofString "i")], .const (BitVec.ofNat 64 d)]) =
      some (.val (.word (out0 + 2#64 * iw + BitVec.ofNat 64 d))) := by
  simp [evalHOLExact, evalListHOLExact, ho, hi, valueIsWord, valueWord, panOpHOL, wordOpHOL, wordOp, BitVec.add_assoc]

private theorem key_to_nibbles_body_eff {F : Type}
    (s0 : PanSemStateFiniteExact 64 F) (key0 n0 out0 : BitVec 64)
    (hc : s0.code = originalRuntimeCode) (hG : GuestInv s0)
    (hk0 : s0.locals.lookup (ofString "key") = some (.val (.word key0)))
    (hn0 : s0.locals.lookup (ofString "n") = some (.val (.word n0)))
    (ho0 : s0.locals.lookup (ofString "out") = some (.val (.word out0)))
    (hres : Resumes (evaluateHOLFiniteState s0 (sourceFnBody Guest.Software.guestFn_key_to_nibbles)).1) :
    ByteEff s0 (evaluateHOLFiniteState s0 (sourceFnBody Guest.Software.guestFn_key_to_nibbles)).2
      [(out0.toNat, 2 * n0.toNat)] ∧
    (0 < n0.toNat → sourceBase ≤ out0.toNat ∧ out0.toNat + 2 * n0.toNat ≤ heapEnd) := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_key_to_nibbles,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map] at hres ⊢
  rw [evaluateHOLFiniteState_dec_total] at hres ⊢; dsimp only at hres ⊢
  have hev0 : @evalHOLExact 64 F _ s0.toExact (fun a => Classical.propDecidable (s0.memaddrs a))
      (.const (BitVec.ofNat 64 0)) = some (.val (.word (BitVec.ofNat 64 0))) := rfl
  rw [hev0] at hres ⊢; dsimp only at hres ⊢
  have hsh0 : shapeEqHOL .one (shapeOfHOLExact (.val (.word (BitVec.ofNat 64 0)))) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  rw [if_pos hsh0] at hres ⊢; dsimp only at hres ⊢
  set s1 := setVarHOLFinite (ofString "i") (.val (.word (BitVec.ofNat 64 0))) s0
  have hinv1 : KeyNibInv s0 key0 n0 out0 s1 := by
    refine ⟨hc, guestInv_setVar _ _ s0 hG, (ByteEff.refl s0 _).locals_clock _ s0.clock, ?_, ?_, ?_, BitVec.ofNat 64 0, ?_, Nat.zero_le _, fun h => by simp at h⟩
    · simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hk0, show ofString "i" ≠ ofString "key" by decide]
    · simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn0, show ofString "i" ≠ ofString "n" by decide]
    · simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ho0, show ofString "i" ≠ ofString "out" by decide]
    · simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  rw [evaluateHOLFiniteState_seq_line780] at hres ⊢
  set w4 : ProgHOL 64 := .while (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 4)])) _
  have hw4_nrr : ¬ Resumes (evaluateHOLFiniteState s1 w4).1 := by
    refine noRetOrRaise_while _ _ (fun t => ?_) s1.clock s1 le_rfl
    exact noRetOrRaise_dec _ _ _ _ fun _ =>
      noRetOrRaise_seq (noRetOrRaise_storeByte _ _ _) fun _ _ =>
      noRetOrRaise_seq (noRetOrRaise_storeByte _ _ _) fun _ _ =>
      noRetOrRaise_dec _ _ _ _ fun _ =>
      noRetOrRaise_seq (noRetOrRaise_storeByte _ _ _) fun _ _ =>
      noRetOrRaise_seq (noRetOrRaise_storeByte _ _ _) fun _ _ =>
      noRetOrRaise_dec _ _ _ _ fun _ =>
      noRetOrRaise_seq (noRetOrRaise_storeByte _ _ _) fun _ _ =>
      noRetOrRaise_seq (noRetOrRaise_storeByte _ _ _) fun _ _ =>
      noRetOrRaise_dec _ _ _ _ fun _ =>
      noRetOrRaise_seq (noRetOrRaise_storeByte _ _ _) fun _ _ =>
      noRetOrRaise_seq (noRetOrRaise_storeByte _ _ _) fun _ _ =>
      noRetOrRaise_assign _ _ _ _
  rcases hr4 : evaluateHOLFiniteState s1 w4 with ⟨r4, s2⟩
  cases r4 with
  | some _ => rw [hr4] at hres hw4_nrr; exact absurd hres hw4_nrr
  | none =>
    dsimp only at hres ⊢
    have hnbc_dec : ∀ {p : ProgHOL 64},
        (∀ t : PanSemStateFiniteExact 64 F, (evaluateHOLFiniteState t p).1 ≠ some .break ∧ (evaluateHOLFiniteState t p).1 ≠ some .continue) →
        ∀ nm e (t : PanSemStateFiniteExact 64 F),
          (evaluateHOLFiniteState t (.dec nm .one e p)).1 ≠ some .break ∧
          (evaluateHOLFiniteState t (.dec nm .one e p)).1 ≠ some .continue := by
      intro p hp nm e t
      rw [evaluateHOLFiniteState_dec_total]; dsimp only
      split
      · simp
      · rename_i v _; split
        · exact hp (setVarHOLFinite nm v t)
        · simp
    have hnbc_seq_sb : ∀ {p : ProgHOL 64},
        (∀ t : PanSemStateFiniteExact 64 F, (evaluateHOLFiniteState t p).1 ≠ some .break ∧ (evaluateHOLFiniteState t p).1 ≠ some .continue) →
        ∀ d e (t : PanSemStateFiniteExact 64 F),
          (evaluateHOLFiniteState t (.seq (.storeByte d e) p)).1 ≠ some .break ∧
          (evaluateHOLFiniteState t (.seq (.storeByte d e) p)).1 ≠ some .continue := by
      intro p hp d e t
      rw [evaluateHOLFiniteState_seq_line780]
      rcases hs : evaluateHOLFiniteState t (.storeByte d e) with ⟨rs, ms⟩
      cases rs with
      | none => exact hp ms
      | some _ =>
        rw [evaluateHOLFiniteState_storeByte] at hs
        revert hs; repeat' split
        all_goals (intro hs; cases hs; try simp)
    have hnbc_asgn : ∀ nm e (t : PanSemStateFiniteExact 64 F),
        (evaluateHOLFiniteState t (.assign .local nm e)).1 ≠ some .break ∧
        (evaluateHOLFiniteState t (.assign .local nm e)).1 ≠ some .continue := by
      intro nm e t; rw [evaluateHOLFiniteState_assign]
      repeat' split
      all_goals simp
    have hinv2_pair := while_keyNibInv _ _
      (by
        intro t
        apply hnbc_dec; apply hnbc_seq_sb; apply hnbc_seq_sb
        apply hnbc_dec; apply hnbc_seq_sb; apply hnbc_seq_sb
        apply hnbc_dec; apply hnbc_seq_sb; apply hnbc_seq_sb
        apply hnbc_dec; apply hnbc_seq_sb; apply hnbc_seq_sb
        exact hnbc_asgn _ _)
      (by
        intro st cw hinv hcond hnz hbody_none
        obtain ⟨hst_c, hst_G, hst_eff, hst_k, hst_n, hst_o, iw, hst_i, hiw_le, hprev⟩ := hinv
        have hnotlt : ¬ (n0 < iw + 4#64) := by
          simp only [evalHOLExact, evalListHOLExact, hst_n, hst_i, wordOpHOL, wordOp, valueIsWord, valueWord,
            List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr, add_zero,
            Compiler.Encoders.Asm.wordCmpHOL] at hcond
          intro hlt
          have hnotle : ¬ (iw + 4#64 ≤ n0) := BitVec.not_le.mpr hlt
          simp [hnotle] at hcond
          exact hnz hcond.symm
        let st' := decClockHOLFinite st
        have hst'_c : st'.code = originalRuntimeCode := hst_c
        have hG' : GuestInv st' := guestInv_congr (s := st) rfl rfl rfl rfl hst_G
        have heff' : ByteEff s0 st' [(out0.toNat, 2 * n0.toNat)] := hst_eff.locals_clock _ _
        rcases hpst : evaluateHOLFiniteState st' _ with ⟨pst_r, pst⟩
        rw [hpst] at hbody_none; dsimp only at hbody_none; subst hbody_none
        obtain ⟨u1, h0lo, h0hi, _, _, hu1c, hu1G, hu1eff, hu1k, hu1n, hu1o, hu1i, hu1r, hpst1⟩ :=
          one_byte_nibbles_step (s := st') (ofString "b0") _ _ _ 0
            (by decide) (by decide) (by decide) (by decide)
            hst'_c hG' heff' hst_k hst_n hst_o hst_i
            (fun bw => eval_out_2i _ out0 iw
              (by simp [st', decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hst_o, show ofString "b0" ≠ ofString "out" by decide])
              (by simp [st', decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hst_i, show ofString "b0" ≠ ofString "i" by decide]))
            (fun bw m hm => eval_out_2i_c _ out0 iw 1
              (by rw [hm]; simp [st', decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hst_o, show ofString "b0" ≠ ofString "out" by decide])
              (by rw [hm]; simp [st', decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hst_i, show ofString "b0" ≠ ofString "i" by decide]))
            (fun hlo hhi => (nib_addr_nowrap out0 iw n0 4 hprev (Or.inr hnotlt) (by omega) (by omega) hlo hhi).2.2.2.2.2 0 (by omega) |>.2)
            (fun hlo hhi _ _ => (nib_addr_nowrap out0 iw n0 4 hprev (Or.inr hnotlt) (by omega) (by omega) hlo hhi).2.2.2.2.2 1 (by omega) |>.2)
            hpst
        have hnw := nib_addr_nowrap out0 iw n0 4 hprev (Or.inr hnotlt) (by omega) (by omega) h0lo h0hi
        rcases h_u1 : evaluateHOLFiniteState u1 _ with ⟨r_u1, p_u1⟩
        rw [h_u1] at hu1r; dsimp only at hu1r; subst hu1r
        obtain ⟨u2, _, _, _, _, hu2c, hu2G, hu2eff, hu2k, hu2n, hu2o, hu2i, hu2r, hpst2⟩ :=
          one_byte_nibbles_step (ofString "b1") _ _ _ 2
            (by decide) (by decide) (by decide) (by decide)
            hu1c hu1G hu1eff hu1k hu1n hu1o hu1i
            (fun bw => eval_out_2i_c _ out0 iw 2
              (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu1o, show ofString "b1" ≠ ofString "out" by decide])
              (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu1i, show ofString "b1" ≠ ofString "i" by decide]))
            (fun bw m hm => eval_out_2i_c _ out0 iw 3
              (by rw [hm]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu1o, show ofString "b1" ≠ ofString "out" by decide])
              (by rw [hm]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu1i, show ofString "b1" ≠ ofString "i" by decide]))
            (fun _ _ => (hnw.2.2.2.2.2 2 (by omega)).2)
            (fun _ _ _ _ => (hnw.2.2.2.2.2 3 (by omega)).2)
            h_u1
        rcases h_u2 : evaluateHOLFiniteState u2 _ with ⟨r_u2, p_u2⟩
        rw [h_u2] at hu2r; dsimp only at hu2r; subst hu2r
        obtain ⟨u3, _, _, _, _, hu3c, hu3G, hu3eff, hu3k, hu3n, hu3o, hu3i, hu3r, hpst3⟩ :=
          one_byte_nibbles_step (ofString "b2") _ _ _ 4
            (by decide) (by decide) (by decide) (by decide)
            hu2c hu2G hu2eff hu2k hu2n hu2o hu2i
            (fun bw => eval_out_2i_c _ out0 iw 4
              (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu2o, show ofString "b2" ≠ ofString "out" by decide])
              (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu2i, show ofString "b2" ≠ ofString "i" by decide]))
            (fun bw m hm => eval_out_2i_c _ out0 iw 5
              (by rw [hm]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu2o, show ofString "b2" ≠ ofString "out" by decide])
              (by rw [hm]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu2i, show ofString "b2" ≠ ofString "i" by decide]))
            (fun _ _ => (hnw.2.2.2.2.2 4 (by omega)).2)
            (fun _ _ _ _ => (hnw.2.2.2.2.2 5 (by omega)).2)
            h_u2
        rcases h_u3 : evaluateHOLFiniteState u3 _ with ⟨r_u3, p_u3⟩
        rw [h_u3] at hu3r; dsimp only at hu3r; subst hu3r
        obtain ⟨u4, _, _, _, h7hi, hu4c, hu4G, hu4eff, hu4k, hu4n, hu4o, hu4i, hu4r, hpst4⟩ :=
          one_byte_nibbles_step (ofString "b3") _ _ _ 6
            (by decide) (by decide) (by decide) (by decide)
            hu3c hu3G hu3eff hu3k hu3n hu3o hu3i
            (fun bw => eval_out_2i_c _ out0 iw 6
              (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu3o, show ofString "b3" ≠ ofString "out" by decide])
              (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu3i, show ofString "b3" ≠ ofString "i" by decide]))
            (fun bw m hm => eval_out_2i_c _ out0 iw 7
              (by rw [hm]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu3o, show ofString "b3" ≠ ofString "out" by decide])
              (by rw [hm]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu3i, show ofString "b3" ≠ ofString "i" by decide]))
            (fun _ _ => (hnw.2.2.2.2.2 6 (by omega)).2)
            (fun _ _ _ _ => (hnw.2.2.2.2.2 7 (by omega)).2)
            h_u3
        have hasgn : evaluateHOLFiniteState u4
            (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 4)])) =
            (none, setVarHOLFinite (ofString "i") (.val (.word (iw + 4#64))) u4) := by
          simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hu4i, wordOpHOL, wordOp,
            valueIsWord, valueWord, lookupKvarHOLExact, isValidValueHOLExact, setKvarHOLFinite,
            shapeOfHOLExact, shapeEqHOL]
        have h7_eq := (hnw.2.2.2.2.2 7 (by omega)).1
        rw [h7_eq] at h7hi
        set L_new :=
          HolFiniteMapExact.resVarEq (HolFiniteMapExact.resVarEq (HolFiniteMapExact.resVarEq (HolFiniteMapExact.resVarEq
            (setVarHOLFinite (ofString "i") (.val (.word (iw + 4#64))) u4).locals
            (ofString "b3", u3.locals.lookup (ofString "b3")))
            (ofString "b2", u2.locals.lookup (ofString "b2")))
            (ofString "b1", u1.locals.lookup (ofString "b1")))
            (ofString "b0", st'.locals.lookup (ofString "b0"))
        have hpst_all : pst = { u4 with locals := L_new } := by
          rw [hpst1, h_u1, hpst2, h_u2, hpst3, h_u3, hpst4, hasgn]; rfl
        dsimp only
        rw [hpst_all]
        refine ⟨hu4c, guestInv_congr (s := u4) rfl rfl rfl rfl hu4G, hu4eff.locals_clock _ _, ?_, ?_, ?_,
          iw + 4#64, ?_, by rw [hnw.2.2.1]; exact hnw.2.2.2.1,
          fun _ => ⟨hnw.2.2.2.2.1, by rw [hnw.2.2.1]; omega⟩⟩
        · simp [L_new, lookup_resVarEq_ne, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu4k,
            show ofString "key" ≠ ofString "b0" by decide, show ofString "key" ≠ ofString "b1" by decide,
            show ofString "key" ≠ ofString "b2" by decide, show ofString "key" ≠ ofString "b3" by decide,
            show ofString "i" ≠ ofString "key" by decide]
        · simp [L_new, lookup_resVarEq_ne, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu4n,
            show ofString "n" ≠ ofString "b0" by decide, show ofString "n" ≠ ofString "b1" by decide,
            show ofString "n" ≠ ofString "b2" by decide, show ofString "n" ≠ ofString "b3" by decide,
            show ofString "i" ≠ ofString "n" by decide]
        · simp [L_new, lookup_resVarEq_ne, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu4o,
            show ofString "out" ≠ ofString "b0" by decide, show ofString "out" ≠ ofString "b1" by decide,
            show ofString "out" ≠ ofString "b2" by decide, show ofString "out" ≠ ofString "b3" by decide,
            show ofString "i" ≠ ofString "out" by decide]
        · simp [L_new, lookup_resVarEq_ne, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "i" ≠ ofString "b0" by decide, show ofString "i" ≠ ofString "b1" by decide,
            show ofString "i" ≠ ofString "b2" by decide, show ofString "i" ≠ ofString "b3" by decide])
      s1.clock s1 s2 le_rfl hinv1 hr4
    rw [hr4] at hres; dsimp only at hres
    rw [evaluateHOLFiniteState_seq_line780] at hres ⊢
    set w1 : ProgHOL 64 := .while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) _
    have hw1_nrr : ¬ Resumes (evaluateHOLFiniteState s2 w1).1 := by
      refine noRetOrRaise_while _ _ (fun t => ?_) s2.clock s2 le_rfl
      exact noRetOrRaise_dec _ _ _ _ fun _ =>
        noRetOrRaise_seq (noRetOrRaise_storeByte _ _ _) fun _ _ =>
        noRetOrRaise_seq (noRetOrRaise_storeByte _ _ _) fun _ _ =>
        noRetOrRaise_assign _ _ _ _
    rcases hr1 : evaluateHOLFiniteState s2 w1 with ⟨r1, s3⟩
    cases r1 with
    | some _ => rw [hr1] at hres hw1_nrr; exact absurd hres hw1_nrr
    | none =>
      dsimp only at ⊢
      obtain ⟨hinv3, hcond3⟩ := while_keyNibInv _ _
        (by
          intro t
          apply hnbc_dec; apply hnbc_seq_sb; apply hnbc_seq_sb
          exact hnbc_asgn _ _)
        (by
          intro st cw hinv hcond hnz hbody_none
          obtain ⟨hst_c, hst_G, hst_eff, hst_k, hst_n, hst_o, iw, hst_i, hiw_le, hprev⟩ := hinv
          have hlt : iw.toNat < n0.toNat := by
            simp [evalHOLExact, hst_n, hst_i, Compiler.Encoders.Asm.wordCmpHOL] at hcond
            by_contra hge; have hge' : ¬ (iw < n0) := by rw [BitVec.lt_def]; omega
            simp [hge'] at hcond; exact hnz hcond.symm
          let st' := decClockHOLFinite st
          have hst'_c : st'.code = originalRuntimeCode := hst_c
          have hG' : GuestInv st' := guestInv_congr (s := st) rfl rfl rfl rfl hst_G
          have heff' : ByteEff s0 st' [(out0.toNat, 2 * n0.toNat)] := hst_eff.locals_clock _ _
          rcases hpst : evaluateHOLFiniteState st' _ with ⟨pst_r, pst⟩
          rw [hpst] at hbody_none; dsimp only at hbody_none; subst hbody_none
          obtain ⟨u1, h0lo, h0hi, _, h1hi, hu1c, hu1G, hu1eff, hu1k, hu1n, hu1o, hu1i, hu1r, hpst1⟩ :=
            one_byte_nibbles_step (s := st') (ofString "b") _ _ _ 0
              (by decide) (by decide) (by decide) (by decide)
              hst'_c hG' heff' hst_k hst_n hst_o hst_i
              (fun bw => eval_out_2i _ out0 iw
                (by simp [st', decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hst_o, show ofString "b" ≠ ofString "out" by decide])
                (by simp [st', decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hst_i, show ofString "b" ≠ ofString "i" by decide]))
              (fun bw m hm => eval_out_2i_c _ out0 iw 1
                (by rw [hm]; simp [st', decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hst_o, show ofString "b" ≠ ofString "out" by decide])
                (by rw [hm]; simp [st', decClockHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hst_i, show ofString "b" ≠ ofString "i" by decide]))
              (fun hlo hhi => (nib_addr_nowrap out0 iw n0 1 hprev (Or.inl (by omega)) (by omega) (by omega) hlo hhi).2.2.2.2.2 0 (by omega) |>.2)
              (fun hlo hhi _ _ => (nib_addr_nowrap out0 iw n0 1 hprev (Or.inl (by omega)) (by omega) (by omega) hlo hhi).2.2.2.2.2 1 (by omega) |>.2)
              hpst
          have hnw := nib_addr_nowrap out0 iw n0 1 hprev (Or.inl (by omega)) (by omega) (by omega) h0lo h0hi
          have hasgn : evaluateHOLFiniteState u1
              (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 1)])) =
              (none, setVarHOLFinite (ofString "i") (.val (.word (iw + 1#64))) u1) := by
            simp [evaluateHOLFiniteState_assign, evalHOLExact, evalListHOLExact, hu1i, wordOpHOL, wordOp,
              valueIsWord, valueWord, lookupKvarHOLExact, isValidValueHOLExact, setKvarHOLFinite,
              shapeOfHOLExact, shapeEqHOL]
          have h1_eq := (hnw.2.2.2.2.2 1 (by omega)).1
          rw [h1_eq] at h1hi
          dsimp only
          rw [hpst1, hasgn]
          refine ⟨hu1c, guestInv_congr (s := u1) rfl rfl rfl rfl hu1G, hu1eff.locals_clock _ _, ?_, ?_, ?_,
            iw + 1#64, ?_, by rw [hnw.2.2.1]; exact hnw.2.2.2.1,
            fun _ => ⟨hnw.2.2.2.2.1, by rw [hnw.2.2.1]; omega⟩⟩
          · simp [lookup_resVarEq_ne, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu1k,
              show ofString "key" ≠ ofString "b" by decide, show ofString "i" ≠ ofString "key" by decide]
          · simp [lookup_resVarEq_ne, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu1n,
              show ofString "n" ≠ ofString "b" by decide, show ofString "i" ≠ ofString "n" by decide]
          · simp [lookup_resVarEq_ne, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hu1o,
              show ofString "out" ≠ ofString "b" by decide, show ofString "i" ≠ ofString "out" by decide]
          · simp [lookup_resVarEq_ne, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "i" ≠ ofString "b" by decide])
        s2.clock s2 s3 le_rfl hinv2_pair.1 hr1
      obtain ⟨_, _, heff3, _, hst3_n, _, iw3, hst3_i, hiw3_le, hdom3⟩ := hinv3
      have hge3 : ¬ (iw3 < n0) := by
        intro hlt
        simp [evalHOLExact, hst3_n, hst3_i, Compiler.Encoders.Asm.wordCmpHOL, hlt] at hcond3
      rw [BitVec.lt_def] at hge3
      have hiw3_eq : iw3.toNat = n0.toNat := by omega
      have hret_run : (evaluateHOLFiniteState s3 (.return (.const (BitVec.ofNat 64 0)))).2 = emptyLocalsHOLFinite s3 := by
        rw [evaluateHOLFiniteState_return]
        simp [evalHOLExact, isValidValueHOLExact, shapeEqHOL, shapeOfHOLExact]
      rw [hret_run]
      refine ⟨heff3.locals_clock _ s3.clock, fun hpos => ?_⟩
      rw [← hiw3_eq] at hpos ⊢
      exact hdom3 hpos

theorem lookup_key_to_nibbles_r16 :
    originalRuntimeCode.lookup (ofString "key_to_nibbles") =
      some ([(ofString "key", .one), (ofString "n", .one), (ofString "out", .one)],
        sourceFnBody Guest.Software.guestFn_key_to_nibbles, .one) :=
  lookup_of_guestAst_getElem 248 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_key_to_nibbles) rfl

theorem call0_key_to_nibbles_eff {F : Type}
    (s : PanSemStateFiniteExact 64 F) (kExp nExp oExp : ExpHOL 64)
    (hc : s.code = originalRuntimeCode) (hG : GuestInv s)
    (hnt : (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "key_to_nibbles") [kExp, nExp, oExp])).1 ≠ some .timeOut)
    (hor : (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "key_to_nibbles") [kExp, nExp, oExp])).1 = none ∨
      Resumes (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "key_to_nibbles") [kExp, nExp, oExp])).1) :
    ∃ kw nw ow : BitVec 64,
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) kExp = some (.val (.word kw)) ∧
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nExp = some (.val (.word nw)) ∧
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) oExp = some (.val (.word ow)) ∧
      ByteEff s (evaluateHOLFiniteState s (.call (some (none, none)) (ofString "key_to_nibbles") [kExp, nExp, oExp])).2
        [(ow.toNat, 2 * nw.toNat)] ∧
      True ∧
      (0 < nw.toNat → sourceBase ≤ ow.toNat ∧ ow.toNat + 2 * nw.toNat ≤ heapEnd) := by
  have not_or_err : ¬ (some (.error : PanSemResultExact 64) = none ∨ Resumes (some .error)) := by
    rintro (h | h)
    · cases h
    · exact not_resumes_error h
  rw [evaluateHOLFiniteState_call] at hnt hor ⊢
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [kExp, nExp, oExp] with _ | vals
  · simp only [hargs] at hor; exact absurd hor not_or_err
  · simp only [hargs] at hnt hor ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "key_to_nibbles") vals with _ | ⟨body', callee, ret'⟩
    · simp only [hl] at hor; exact absurd hor not_or_err
    · simp only [hl] at hnt hor ⊢
      have hsame := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "key_to_nibbles") _ _ body'
        _ ret' vals callee (by rw [hc]; exact lookup_key_to_nibbles_r16) hl
      subst hsame
      have hret := lookupCodeHOLFinite_installed_return s (ofString "key_to_nibbles") _ _ _
        _ ret' vals callee (by rw [hc]; exact lookup_key_to_nibbles_r16) hl
      subst hret
      have hl' : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "key_to_nibbles") vals =
          some (sourceFnBody Guest.Software.guestFn_key_to_nibbles, callee, .one) := by
        simpa [hc] using hl
      obtain ⟨kw, nw, ow, rfl, hkw, hnw, how⟩ :=
        lookupCode_three_words (by decide) (by decide) (by decide) lookup_key_to_nibbles_r16 hl'
      have hvals_ev :
          @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) kExp = some (.val (.word kw)) ∧
          @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nExp = some (.val (.word nw)) ∧
          @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) oExp = some (.val (.word ow)) := by
        rw [evalListHOLFinite_eq_toExact] at hargs
        simp only [evalListHOLExact] at hargs
        rcases he1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) kExp with _ | v1
        · simp [he1] at hargs
        · rcases he2 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) nExp with _ | v2
          · simp [he1, he2] at hargs
          · rcases he3 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) oExp with _ | v3
            · simp [he1, he2, he3] at hargs
            · simp [he1, he2, he3] at hargs
              obtain ⟨rfl, rfl, rfl⟩ := hargs
              exact ⟨rfl, rfl, rfl⟩
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt hor ⊢
        let entry := callEntryStateHOLFinite s callee
        have hGe : GuestInv entry := guestInv_callEntry s callee hG
        rcases hrun : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_key_to_nibbles) with ⟨res, post⟩
        dsimp only [entry] at hrun
        simp only [hrun] at hnt hor ⊢
        have hres_b : Resumes res := by
          cases res with
          | none => exfalso; rcases hor with h | ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
          | some r =>
            cases r with
            | returned v => exact Or.inl ⟨v, rfl⟩
            | exception eid ev => exact hor.resolve_left (by simp)
            | _ => exfalso; rcases hor with h | ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
        obtain ⟨heff_b, hdom_b⟩ := key_to_nibbles_body_eff entry kw nw ow hc hGe hkw hnw how
          (by dsimp only [entry]; rw [hrun]; exact hres_b)
        dsimp only [entry] at heff_b
        rw [hrun] at heff_b
        have heff_s : ByteEff s post [(ow.toNat, 2 * nw.toNat)] :=
          ((ByteEff.refl s _).locals_clock _ _).trans heff_b
        cases res with
        | none => exfalso; rcases hres_b with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h
        | some r =>
          cases r with
          | returned v =>
            dsimp only at hor ⊢
            split
            · exact ⟨kw, nw, ow, hvals_ev.1, hvals_ev.2.1, hvals_ev.2.2, heff_s.locals_clock _ _, trivial, hdom_b⟩
            · rename_i hbad; rw [if_neg hbad] at hor; exact absurd hor not_or_err
          | exception eid ev =>
            exact ⟨kw, nw, ow, hvals_ev.1, hvals_ev.2.1, hvals_ev.2.2, heff_s.locals_clock _ _, trivial, hdom_b⟩
          | _ => exfalso; rcases hres_b with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp at h

theorem decCall_alloc_resumes_inv {F : Type}
    (s : PanSemStateFiniteExact 64 F) (x : MlS) (szExp : ExpHOL 64) (cont : ProgHOL 64)
    (hc : s.code = originalRuntimeCode) (hAR : ArenaReady s)
    (hnt : (evaluateHOLFiniteState s (.decCall x .one (ofString "alloc") [szExp] cont)).1 ≠ some .timeOut)
    (hres : Resumes (evaluateHOLFiniteState s (.decCall x .one (ofString "alloc") [szExp] cont)).1) :
    ∃ hp sz q : BitVec 64, ∃ mid : PanSemStateFiniteExact 64 F,
      s.globals.lookup (ofString "heap_ptr") = some (.val (.word hp)) ∧
      hp.toNat = globN s "heap_ptr" ∧
      @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) szExp = some (.val (.word sz)) ∧
      q = (hp + (sz + 7)) &&& ((0 : BitVec 64) - 8) ∧
      q.toNat = hp.toNat + (sz.toNat + 7) / 8 * 8 ∧
      hp.toNat ≤ q.toNat ∧ q.toNat ≤ heapLimit ∧ q.toNat % 8 = 0 ∧
      mid.code = originalRuntimeCode ∧ ArenaReady mid ∧
      mid.memory = s.memory ∧ mid.be = s.be ∧
      mid.globals = s.globals.update (ofString "heap_ptr", .val (.word q)) ∧
      mid.locals = s.locals.update (x, .val (.word hp)) ∧
      (evaluateHOLFiniteState mid cont).1 ≠ some .timeOut ∧
      Resumes (evaluateHOLFiniteState mid cont).1 ∧
      (evaluateHOLFiniteState s (.decCall x .one (ofString "alloc") [szExp] cont)).2 =
        { (evaluateHOLFiniteState mid cont).2 with
          locals := HolFiniteMapExact.resVarEq (evaluateHOLFiniteState mid cont).2.locals (x, s.locals.lookup x) } := by
  obtain ⟨hG, hA⟩ := hAR
  obtain ⟨hp, _, _, hhp, hhp_eq, _, _, _, _⟩ := R13.arenaOK_globals s hA
  have hlook : originalRuntimeCode.lookup (ofString "alloc") =
      some ([(ofString "n", .one)], sourceFnBody Guest.Software.guestFn_alloc, .one) :=
    lookup_of_guestAst_getElem 7 (by rw [guestAst_len]; decide) (extractFn Guest.Software.guestFn_alloc) rfl
  rw [evaluateHOLFiniteState_decCall_total] at hnt hres ⊢
  rcases hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [szExp] with _ | vals
  · simp only [hargs] at hres; exact absurd hres not_resumes_error
  · simp only [hargs] at hnt hres ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "alloc") vals with _ | ⟨body', callee, ret'⟩
    · simp only [hl] at hres; exact absurd hres not_resumes_error
    · simp only [hl] at hnt hres ⊢
      have hsame := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "alloc") _ _ body'
        _ ret' vals callee (by rw [hc]; exact hlook) hl
      subst hsame
      have hret := lookupCodeHOLFinite_installed_return s (ofString "alloc") _ _ _
        _ ret' vals callee (by rw [hc]; exact hlook) hl
      subst hret
      have hl' : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "alloc") vals =
          some (sourceFnBody Guest.Software.guestFn_alloc, callee, .one) := by simpa [hc] using hl
      obtain ⟨sz, rfl, hsz_c⟩ := lookupCode_one_word hlook hl'
      have hsz_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) szExp =
          some (.val (.word sz)) := by
        rw [evalListHOLFinite_eq_toExact] at hargs
        simp only [evalListHOLExact] at hargs
        rcases he : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) szExp with _ | v1
        · simp [he] at hargs
        · simp [he] at hargs; subst hargs; rfl
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt hres ⊢
        let entry := callEntryStateHOLFinite s callee
        have hal_res : Resumes (evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_alloc)).1 := by
          rcases hr : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_alloc) with ⟨ra, pa⟩
          dsimp only [entry] at hr hnt hres ⊢
          rw [hr] at hnt hres
          dsimp only at hnt hres ⊢
          cases ra with
          | none => exact absurd hres not_resumes_error
          | some r =>
            cases r with
            | returned v => exact Or.inl ⟨v, rfl⟩
            | exception eid ev =>
              dsimp only [fixClockHOLFinite] at hres
              rcases hres with ⟨_, h⟩ | ⟨e', v', h, hne⟩
              · simp at h
              · cases h
                exact Or.inr ⟨eid, ev, Eq.refl _, hne⟩
            | _ => exfalso; rcases hres with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> simp [fixClockHOLFinite] at h
        obtain ⟨sz', hsz'_c, hal_ret, hnot_sub, hnot_cMax, hal_post⟩ :=
          R13.alloc_body_resumes entry hp hc hhp hal_res
        have hsz_eq : sz = sz' := by
          change callee.lookup (ofString "n") = some (.val (.word sz')) at hsz'_c
          rw [hsz_c] at hsz'_c
          injection hsz'_c with h1; injection h1 with h2; injection h2
        subst hsz_eq
        rcases hr : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_alloc) with ⟨ra, pa⟩
        dsimp only [entry] at hr hal_ret hal_post
        rw [hr] at hal_ret hal_post
        dsimp only at hal_ret hal_post
        subst hal_ret
        simp only [hr, fixClockHOLFinite] at hnt hres ⊢
        have hsh_hp : (shapeEqHOL (shapeOfHOLExact (.val (.word hp))) .one &&
            shapeEqHOL (shapeOfHOLExact (.val (.word hp))) .one) = true := by
          simp [shapeEqHOL, shapeOfHOLExact]
        rw [if_pos hsh_hp] at hnt hres ⊢
        dsimp only at hnt hres ⊢
        let q : BitVec 64 := (hp + (sz + 7)) &&& ((0 : BitVec 64) - 8)
        have hhp_hi : hp.toNat ≤ heapLimit := by rw [hhp_eq]; exact hA.2.1
        have hhp_al : hp.toNat % 8 = 0 := by rw [hhp_eq]; exact hA.2.2.2.2.2.1
        obtain ⟨hq_eq, hq_hi, hq_al, hp_le_q, _⟩ :=
          R13.alloc_arith hp sz hhp_hi hhp_al hnot_sub hnot_cMax
        change q.toNat = _ at hq_eq
        let mid := setVarHOLFinite x (.val (.word hp))
          { pa with locals := s.locals,
                    clock := if (callEntryStateHOLFinite s callee).clock < pa.clock
                             then (callEntryStateHOLFinite s callee).clock else pa.clock }
        have hmid_eq : mid =
            { s with locals := s.locals.update (x, .val (.word hp)),
                     globals := s.globals.update (ofString "heap_ptr", .val (.word q)),
                     clock := mid.clock } := by
          dsimp only [mid, setVarHOLFinite]; rw [hal_post]; rfl
        have hmid_AR : ArenaReady mid := by
          rw [hmid_eq]
          refine ⟨⟨hG.code, hG.memaddrs, hG.shMemaddrs, hG.baseAddr⟩, ?_⟩
          unfold ArenaOK
          have h1 : globN { s with locals := s.locals.update (x, .val (.word hp)), globals := s.globals.update (ofString "heap_ptr", .val (.word q)), clock := mid.clock } "heap_ptr" = q.toNat := by
            simp [globN, HolFiniteMapExact.lookup_update, FUPDATE]
          have h2 : globN { s with locals := s.locals.update (x, .val (.word hp)), globals := s.globals.update (ofString "heap_ptr", .val (.word q)), clock := mid.clock } "frame_mem_ptr" = globN s "frame_mem_ptr" := by
            simp [globN, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "heap_ptr" ≠ ofString "frame_mem_ptr" by decide]
          have h3 : globN { s with locals := s.locals.update (x, .val (.word hp)), globals := s.globals.update (ofString "heap_ptr", .val (.word q)), clock := mid.clock } "scratch_ptr" = globN s "scratch_ptr" := by
            simp [globN, HolFiniteMapExact.lookup_update, FUPDATE, show ofString "heap_ptr" ≠ ofString "scratch_ptr" by decide]
          rw [h1, h2, h3]
          have hsb : sourceBase ≤ hp.toNat := by rw [hhp_eq]; exact hA.1
          exact ⟨by omega, hq_hi, hA.2.2.1, hA.2.2.2.1, hA.2.2.2.2.1, hq_al,
            hA.2.2.2.2.2.2.1, hA.2.2.2.2.2.2.2.1,
            globalsWord_update (ofString "heap_ptr") q rfl hA.2.2.2.2.2.2.2.2⟩
        refine ⟨hp, sz, q, mid, hhp, hhp_eq, hsz_ev, rfl, hq_eq, hp_le_q, hq_hi, hq_al,
          by rw [hmid_eq]; exact hc, hmid_AR,
          by rw [hmid_eq], by rw [hmid_eq], by rw [hmid_eq], by rw [hmid_eq],
          hnt, hres, rfl⟩

theorem ww_mpt_nibble_key :
    WritesWithin (fun s => [(globN s "keccak_pad", 136), (globN s "keccak_st", 200), (globN s "mpt_hash_scratch", 40)])
    ["heap_ptr"] (ofString "mpt_nibble_key") := by
  have hlook : originalRuntimeCode.lookup (ofString "mpt_nibble_key") =
      some ([(ofString "m", .one), (ofString "key", .one), (ofString "klen", .one)],
        sourceFnBody Guest.Software.guestFn_mpt_nibble_key, .comb [.one, .one]) :=
    lookup_of_guestAst_getElem 270 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_mpt_nibble_key) rfl
  refine ⟨_, _, _, hlook, ?_⟩
  intro F s hc hAR _ hnt hres
  let R0 : List Ivl := [(globN s "keccak_pad", 136), (globN s "keccak_st", 200), (globN s "mpt_hash_scratch", 40)]
  have finish_ww : ∀ (post : PanSemStateFiniteExact 64 F),
      ArenaReady post →
      globN s "heap_ptr" ≤ globN post "heap_ptr" →
      (∀ k : MlS, k ≠ ofString "heap_ptr" → post.globals.lookup k = s.globals.lookup k) →
      ByteEff s post (R0 ++ [(globN s "heap_ptr", heapLimit - globN s "heap_ptr")]) →
      ArenaReady post ∧ globN s "heap_ptr" ≤ globN post "heap_ptr" ∧
        globN post "scratch_ptr" ≤ globN s "scratch_ptr" ∧
        FrameOutside s post
          (R0 ++ [(globN s "frame_mem_ptr", globN s "scratch_ptr" - globN s "frame_mem_ptr")])
          (globN s "heap_ptr", heapLimit - globN s "heap_ptr") ∧
        ∀ k : MlS, k ∉ (["heap_ptr"] : List String).map ofString → s.globals.lookup k = post.globals.lookup k := by
    intro post hAR_p hhp_le hg_eq heff
    refine ⟨hAR_p, hhp_le, ?_, ?_, ?_⟩
    · have hsp : post.globals.lookup (ofString "scratch_ptr") = s.globals.lookup (ofString "scratch_ptr") :=
        hg_eq _ (by decide)
      unfold globN; rw [hsp]
    · intro a hkeep hfresh
      by_contra hne
      obtain ⟨iv, hiv, _, hc1, hc2⟩ := heff.cell_frame a hne
      simp only [List.mem_append, List.mem_singleton] at hiv
      rcases hiv with hR0 | rfl
      · exact hkeep iv (List.mem_append_left _ hR0) ⟨hc1, hc2⟩
      · exact hfresh ⟨hc1, hc2⟩
    · intro k hk
      have hne : k ≠ ofString "heap_ptr" := by simpa using hk
      exact (hg_eq k hne).symm
  let ret1 : ExpHOL 64 := InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural
    (Exp.rStruct [Exp.var VarKind.local "nb", Exp.const (BitVec.ofNat 64 64)])
  let ret2 : ExpHOL 64 := InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural
    (Exp.rStruct [Exp.var VarKind.local "nb2", Exp.panOp PanOp.mul [Exp.const (BitVec.ofNat 64 2), Exp.var VarKind.local "klen"]])
  set c_kec : ProgHOL 64 := .call (some (none, none)) (ofString "keccak256")
    [.var .local (ofString "key"), .var .local (ofString "klen"), .var .global (ofString "mpt_hash_scratch")]
  set dc_nb : ProgHOL 64 := .decCall (ofString "nb") .one (ofString "alloc") [.const 64#64]
    (.seq
      (.call (some (none, none)) (ofString "key_to_nibbles")
        [.var .global (ofString "mpt_hash_scratch"), .const 32#64, .var .local (ofString "nb")])
      (.return ret1))
  have hbody : sourceFnBody Guest.Software.guestFn_mpt_nibble_key =
      .seq
        (.ite (.cmp .notEqual (.load .one (.op .add [.var .local (ofString "m"), .const 8#64])) (.const 0#64))
          (.seq c_kec dc_nb)
          .skip)
        (.decCall (ofString "nb2") .one (ofString "alloc")
          [.panop .mul [.const 2#64, .var .local (ofString "klen")]]
          (.seq
            (.call (some (none, none)) (ofString "key_to_nibbles")
              [.var .local (ofString "key"), .var .local (ofString "klen"), .var .local (ofString "nb2")])
            (.return ret2))) := rfl
  rw [hbody, evaluateHOLFiniteState_seq_line780] at hnt hres ⊢
  rw [evaluateHOLFiniteState_ite] at hnt hres ⊢
  rcases hcond : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .notEqual (.load .one (.op .add [.var .local (ofString "m"), .const 8#64])) (.const 0#64)) with _ | cv
  · simp [hcond] at hres; exact absurd hres not_resumes_error
  · rcases cv with ⟨⟨cw⟩⟩ | _ | _
    · simp only [hcond] at hnt hres ⊢
      by_cases hcw0 : cw = 0
      · simp only [hcw0, ↓reduceIte, evaluateHOLFiniteState_skip] at hnt hres ⊢
        obtain ⟨hp, sz, q, mid, _, hhp_eq, hsz_ev, _, hq_eq, hp_le_q, hq_hi, _,
            hmid_c, hmid_AR, hmid_mem, hmid_be, hmid_glob, hmid_loc, hcont_nt, hcont_res, hpost_eq⟩ :=
          decCall_alloc_resumes_inv s (ofString "nb2") _ _ hc hAR hnt hres
        rw [hpost_eq]
        have hklen_word : ∃ klen_w : BitVec 64,
            s.locals.lookup (ofString "klen") = some (.val (.word klen_w)) ∧ sz = 2#64 * klen_w := by
          simp only [evalHOLExact, evalListHOLExact] at hsz_ev
          rcases hkl : s.locals.lookup (ofString "klen") with _ | kv
          · simp [hkl] at hsz_ev
          · rcases kv with ⟨⟨kw⟩⟩ | _ | _
            · simp [hkl, valueIsWord, valueWord, panOpHOL] at hsz_ev
              exact ⟨kw, rfl, hsz_ev.symm⟩
            · simp [hkl, List.all, valueIsWord] at hsz_ev
            · simp [hkl, List.all, valueIsWord] at hsz_ev
        obtain ⟨klen_w, hklen_s, rfl⟩ := hklen_word
        rw [evaluateHOLFiniteState_seq_line780] at hcont_nt hcont_res ⊢
        set c_ktn : ProgHOL 64 := .call (some (none, none)) (ofString "key_to_nibbles")
          [.var .local (ofString "key"), .var .local (ofString "klen"), .var .local (ofString "nb2")]
        have hc_nt : (evaluateHOLFiniteState mid c_ktn).1 ≠ some .timeOut := by
          rcases hr : evaluateHOLFiniteState mid c_ktn with ⟨r1, _⟩
          rw [hr] at hcont_nt; intro h; subst h; simp at hcont_nt
        have hc_or : (evaluateHOLFiniteState mid c_ktn).1 = none ∨
            Resumes (evaluateHOLFiniteState mid c_ktn).1 := by
          rcases hr : evaluateHOLFiniteState mid c_ktn with ⟨r1, _⟩
          rw [hr] at hcont_res
          cases r1 with
          | none => exact Or.inl rfl
          | some _ => exact Or.inr hcont_res
        obtain ⟨_, nw, ow, _, hnw_ev, how_ev, heff_ktn, _, hdom_ktn⟩ :=
          call0_key_to_nibbles_eff mid _ _ _ hmid_c hmid_AR.1 hc_nt hc_or
        have hnw_eq : klen_w = nw := by
          simp [evalHOLExact, hmid_loc, HolFiniteMapExact.lookup_update, FUPDATE, hklen_s,
            show ofString "nb2" ≠ ofString "klen" by decide] at hnw_ev
          exact hnw_ev
        have how_eq : hp = ow := by
          simp [evalHOLExact, hmid_loc, HolFiniteMapExact.lookup_update, FUPDATE] at how_ev
          exact how_ev
        subst hnw_eq how_eq
        rcases hr_ktn : evaluateHOLFiniteState mid c_ktn with ⟨r_ktn, m_after⟩
        change ByteEff mid (evaluateHOLFiniteState mid c_ktn).2 _ at heff_ktn
        rw [hr_ktn] at heff_ktn
        dsimp only at heff_ktn hcont_res ⊢
        have heff_ktn_free : ByteEff mid m_after (R0 ++ [(globN s "heap_ptr", heapLimit - globN s "heap_ptr")]) := by
          refine heff_ktn.mono (fun iv hiv hipos => ?_)
          simp only [List.mem_singleton] at hiv; subst hiv
          have hpos_kl : 0 < klen_w.toNat := by omega
          obtain ⟨_, hhi_he⟩ := hdom_ktn hpos_kl
          have hhe_lt : heapEnd < 2 ^ 64 := by decide
          have h2kl : (2#64 * klen_w).toNat = 2 * klen_w.toNat := by
            rw [BitVec.toNat_mul]
            have h2_nat : (2#64).toNat = 2 := rfl
            rw [h2_nat, Nat.mod_eq_of_lt (by omega)]
          rw [h2kl] at hq_eq
          refine ⟨(globN s "heap_ptr", heapLimit - globN s "heap_ptr"),
            List.mem_append_right _ (List.mem_singleton.mpr rfl), ?_, ?_⟩ <;> omega
        cases r_ktn with
        | some _ =>
          dsimp only
          have hm_AR : ArenaReady { m_after with locals := m_after.locals.resVarEq (ofString "nb2", s.locals.lookup (ofString "nb2")) } :=
            localsFree_arenaReady m_after (m_after.locals.resVarEq (ofString "nb2", s.locals.lookup (ofString "nb2"))) m_after.clock
              ⟨guestInv_congr heff_ktn.code heff_ktn.memaddrs heff_ktn.shMemaddrs heff_ktn.baseAddr hmid_AR.1,
               arenaOK_congr heff_ktn.globals hmid_AR.2⟩
          refine ⟨hm_AR, ?_, ?_, ?_, ?_⟩
          · rw [← hhp_eq]; simp [globN, heff_ktn.globals, hmid_glob, HolFiniteMapExact.lookup_update, FUPDATE, FUPDATE_HOL]; exact hp_le_q
          · simp [globN, heff_ktn.globals, hmid_glob, HolFiniteMapExact.lookup_update, FUPDATE, FUPDATE_HOL,
              show ofString "heap_ptr" ≠ ofString "scratch_ptr" by decide]
          · intro a hkeep hfresh; by_contra hne
            rw [← hmid_mem] at hne
            obtain ⟨iv, hiv, _, hc1, hc2⟩ := heff_ktn_free.cell_frame a hne
            simp only [List.mem_append, List.mem_singleton] at hiv
            rcases hiv with hR0 | rfl
            · exact hkeep iv (List.mem_append_left _ hR0) ⟨hc1, hc2⟩
            · exact hfresh ⟨hc1, hc2⟩
          · intro k hk
            have hne : k ≠ ofString "heap_ptr" := by simpa using hk
            simp [heff_ktn.globals, hmid_glob, HolFiniteMapExact.lookup_update, FUPDATE, FUPDATE_HOL, hne, Ne.symm hne]
        | none =>
          have hret_eff := byteEff_return m_after ret2 (R0 ++ [(globN s "heap_ptr", heapLimit - globN s "heap_ptr")])
          have heff_tot := heff_ktn_free.trans hret_eff
          set fin := (evaluateHOLFiniteState m_after (.return ret2)).2
          have hm_AR : ArenaReady { fin with locals := fin.locals.resVarEq (ofString "nb2", s.locals.lookup (ofString "nb2")) } :=
            localsFree_arenaReady fin (fin.locals.resVarEq (ofString "nb2", s.locals.lookup (ofString "nb2"))) fin.clock
              ⟨guestInv_congr heff_tot.code heff_tot.memaddrs heff_tot.shMemaddrs heff_tot.baseAddr hmid_AR.1,
               arenaOK_congr heff_tot.globals hmid_AR.2⟩
          refine ⟨hm_AR, ?_, ?_, ?_, ?_⟩
          · rw [← hhp_eq]; simp [globN, heff_tot.globals, hmid_glob, HolFiniteMapExact.lookup_update, FUPDATE, FUPDATE_HOL]; exact hp_le_q
          · simp [globN, heff_tot.globals, hmid_glob, HolFiniteMapExact.lookup_update, FUPDATE, FUPDATE_HOL,
              show ofString "heap_ptr" ≠ ofString "scratch_ptr" by decide]
          · intro a hkeep hfresh; by_contra hne
            rw [← hmid_mem] at hne
            obtain ⟨iv, hiv, _, hc1, hc2⟩ := heff_tot.cell_frame a hne
            simp only [List.mem_append, List.mem_singleton] at hiv
            rcases hiv with hR0 | rfl
            · exact hkeep iv (List.mem_append_left _ hR0) ⟨hc1, hc2⟩
            · exact hfresh ⟨hc1, hc2⟩
          · intro k hk
            have hne : k ≠ ofString "heap_ptr" := by simpa using hk
            simp [heff_tot.globals, hmid_glob, HolFiniteMapExact.lookup_update, FUPDATE, FUPDATE_HOL, hne, Ne.symm hne]
      · simp only [hcw0, ↓reduceIte] at hnt hres ⊢
        have hdc_no_none : ∀ t : PanSemStateFiniteExact 64 F, (evaluateHOLFiniteState t dc_nb).1 ≠ none := by
          intro t; dsimp only [dc_nb]; rw [evaluateHOLFiniteState_decCall_total]
          rcases hargs : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) [.const 64#64] with _ | vals
          · simp
          · simp only
            rcases hl : lookupCodeHOLFinite t.code.lookup (ofString "alloc") vals with _ | ⟨body', callee', ret'⟩
            · simp
            · simp only
              split
              · simp
              · rcases hr : evaluateHOLFiniteState (callEntryStateHOLFinite t callee') body' with ⟨ra, pa⟩
                simp only [hr]
                cases ra with
                | none => simp
                | some r =>
                  cases r with
                  | returned v =>
                    dsimp only [fixClockHOLFinite]
                    split
                    · dsimp only
                      rw [evaluateHOLFiniteState_seq_line780]
                      rcases evaluateHOLFiniteState _ _ with ⟨r_k, t_k⟩
                      cases r_k with
                      | some _ => simp
                      | none => dsimp only; exact return_ne_none t_k _
                    · simp
                  | _ => simp [fixClockHOLFinite]
        have hyes_no_none : (evaluateHOLFiniteState s (.seq c_kec dc_nb)).1 ≠ none := by
          rw [evaluateHOLFiniteState_seq_line780]
          rcases evaluateHOLFiniteState s c_kec with ⟨r1, m1⟩
          cases r1 with
          | some _ => simp
          | none => exact hdc_no_none m1
        rcases hyes : evaluateHOLFiniteState s (.seq c_kec dc_nb) with ⟨r_yes, p_yes⟩
        cases r_yes with
        | none => exact absurd (by rw [hyes]) hyes_no_none
        | some ry =>
          rw [hyes] at hnt hres
          dsimp only at hnt hres ⊢
          rw [evaluateHOLFiniteState_seq_line780] at hyes
          have hkec_sub : ∀ vals,
              evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
                [.var .local (ofString "key"), .var .local (ofString "klen"), .var .global (ofString "mpt_hash_scratch")] = some vals →
              ∀ i ∈ [globBufIvl s.globals "keccak_st" 200, globBufIvl s.globals "keccak_pad" 136,
                     (valWordNat (vals[2]?.getD (.rStruct [])), 32)],
                0 < i.2 → ∃ j ∈ R0, j.1 ≤ i.1 ∧ i.1 + i.2 ≤ j.1 + j.2 := by
            intro vals hvals i hi hipos
            rw [evalListHOLFinite_eq_toExact] at hvals
            simp only [evalListHOLExact, evalHOLExact] at hvals
            rcases he1 : s.locals.lookup (ofString "key") with _ | v1 <;>
              rcases he2 : s.locals.lookup (ofString "klen") with _ | v2 <;>
              rcases he3 : s.globals.lookup (ofString "mpt_hash_scratch") with _ | v3
            all_goals (try simp [he1, he2, he3] at hvals)
            subst hvals
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
            rcases hi with rfl | rfl | rfl
            · rw [globBufIvl_eq_bufferRegion] at hipos ⊢
              by_cases hz : globN s "keccak_st" = 0
              · simp [bufferRegion, hz] at hipos
              · simp only [bufferRegion, hz, ↓reduceIte]
                exact ⟨(globN s "keccak_st", 200), by simp [R0], le_rfl, le_rfl⟩
            · rw [globBufIvl_eq_bufferRegion] at hipos ⊢
              by_cases hz : globN s "keccak_pad" = 0
              · simp [bufferRegion, hz] at hipos
              · simp only [bufferRegion, hz, ↓reduceIte]
                exact ⟨(globN s "keccak_pad", 136), by simp [R0], le_rfl, le_rfl⟩
            · have hv3 : valWordNat v3 = globN s "mpt_hash_scratch" := by
                unfold globN; rw [he3]; rcases v3 with ⟨⟨w⟩⟩ | _ | _ <;> rfl
              simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, hv3]
              exact ⟨(globN s "mpt_hash_scratch", 40), by simp [R0], le_rfl, by omega⟩
          rcases hkec : evaluateHOLFiniteState s c_kec with ⟨r_kec, m1⟩
          have hkec_nt : r_kec ≠ some .timeOut := by
            rw [hkec] at hyes; intro h; subst h; cases hyes; exact hnt rfl
          cases r_kec with
          | some rk =>
            rw [hkec] at hyes; dsimp only at hyes; cases hyes
            have heff1 := call0_byteEff funByteEff_keccak256 s _ R0 hc hAR.1 hkec_sub
              (by rw [hkec]; exact hkec_nt) (by rw [hkec]; exact Or.inr hres)
            change ByteEff s (evaluateHOLFiniteState s c_kec).2 R0 at heff1
            rw [hkec] at heff1; dsimp only at heff1
            have hm1_AR : ArenaReady p_yes :=
              ⟨guestInv_congr heff1.code heff1.memaddrs heff1.shMemaddrs heff1.baseAddr hAR.1,
               arenaOK_congr heff1.globals hAR.2⟩
            exact finish_ww p_yes hm1_AR
              (by simp [globN, heff1.globals])
              (fun k _ => by rw [heff1.globals])
              (heff1.mono fun iv hiv _ => ⟨iv, List.mem_append_left _ hiv, le_rfl, le_rfl⟩)
          | none =>
            have heff1 := call0_byteEff funByteEff_keccak256 s _ R0 hc hAR.1 hkec_sub
              (by rw [hkec]; simp) (by rw [hkec]; exact Or.inl rfl)
            change ByteEff s (evaluateHOLFiniteState s c_kec).2 R0 at heff1
            rw [hkec] at heff1 hyes; dsimp only at heff1 hyes
            have hm1_c : m1.code = originalRuntimeCode := heff1.code.trans hc
            have hm1_AR : ArenaReady m1 :=
              ⟨guestInv_congr heff1.code heff1.memaddrs heff1.shMemaddrs heff1.baseAddr hAR.1,
               arenaOK_congr heff1.globals hAR.2⟩
            have hdc_nt : (evaluateHOLFiniteState m1 dc_nb).1 ≠ some .timeOut := by
              rw [hyes]; exact hnt
            have hdc_res : Resumes (evaluateHOLFiniteState m1 dc_nb).1 := by
              rw [hyes]; exact hres
            obtain ⟨hp, sz, q, mid, _, hhp_eq, hsz_ev, _, hq_eq, hp_le_q, hq_hi, _,
                hmid_c, hmid_AR, hmid_mem, hmid_be, hmid_glob, hmid_loc, hcont_nt, hcont_res, hpost_eq⟩ :=
              decCall_alloc_resumes_inv m1 (ofString "nb") _ _ hm1_c hm1_AR hdc_nt hdc_res
            have hsz64 : sz = 64#64 := by simp [evalHOLExact] at hsz_ev; exact hsz_ev.symm
            subst hsz64
            have hhp_s : globN m1 "heap_ptr" = globN s "heap_ptr" := by simp [globN, heff1.globals]
            change (evaluateHOLFiniteState m1 dc_nb).2 = _ at hpost_eq
            rw [hyes] at hpost_eq; dsimp only at hpost_eq
            rw [hpost_eq]
            rw [evaluateHOLFiniteState_seq_line780] at hcont_nt hcont_res ⊢
            set c_ktn : ProgHOL 64 := .call (some (none, none)) (ofString "key_to_nibbles")
              [.var .global (ofString "mpt_hash_scratch"), .const 32#64, .var .local (ofString "nb")]
            have hc_nt : (evaluateHOLFiniteState mid c_ktn).1 ≠ some .timeOut := by
              rcases hr : evaluateHOLFiniteState mid c_ktn with ⟨r1, _⟩
              rw [hr] at hcont_nt; intro h; subst h; simp at hcont_nt
            have hc_or : (evaluateHOLFiniteState mid c_ktn).1 = none ∨
                Resumes (evaluateHOLFiniteState mid c_ktn).1 := by
              rcases hr : evaluateHOLFiniteState mid c_ktn with ⟨r1, _⟩
              rw [hr] at hcont_res
              cases r1 with
              | none => exact Or.inl rfl
              | some _ => exact Or.inr hcont_res
            obtain ⟨_, nw, ow, _, hnw_ev, how_ev, heff_ktn, _, _⟩ :=
              call0_key_to_nibbles_eff mid _ _ _ hmid_c hmid_AR.1 hc_nt hc_or
            have hnw32 : nw = 32#64 := by simp [evalHOLExact] at hnw_ev; exact hnw_ev.symm
            have how_hp : ow = hp := by
              simp [evalHOLExact, hmid_loc, HolFiniteMapExact.lookup_update, FUPDATE] at how_ev
              exact how_ev.symm
            subst hnw32 how_hp
            rcases hr_ktn : evaluateHOLFiniteState mid c_ktn with ⟨r_ktn, m_after⟩
            change ByteEff mid (evaluateHOLFiniteState mid c_ktn).2 _ at heff_ktn
            rw [hr_ktn] at heff_ktn
            dsimp only at heff_ktn hcont_res ⊢
            have heff1_w : ByteEff s m1 (R0 ++ [(globN s "heap_ptr", heapLimit - globN s "heap_ptr")]) :=
              heff1.mono fun iv hiv _ => ⟨iv, List.mem_append_left _ hiv, le_rfl, le_rfl⟩
            have heff_ktn_w : ByteEff mid m_after (R0 ++ [(globN s "heap_ptr", heapLimit - globN s "heap_ptr")]) := by
              refine heff_ktn.mono (fun iv hiv _ => ?_)
              simp only [List.mem_singleton] at hiv; subst hiv
              have h64_nat : (64#64).toNat = 64 := rfl
              have h32_nat : (32#64).toNat = 32 := rfl
              rw [h64_nat] at hq_eq
              rw [h32_nat]
              refine ⟨(globN s "heap_ptr", heapLimit - globN s "heap_ptr"),
                List.mem_append_right _ (List.mem_singleton.mpr rfl), ?_, ?_⟩ <;> omega
            cases r_ktn with
            | some _ =>
              dsimp only
              have hm_AR : ArenaReady { m_after with locals := m_after.locals.resVarEq (ofString "nb", m1.locals.lookup (ofString "nb")) } :=
                localsFree_arenaReady m_after (m_after.locals.resVarEq (ofString "nb", m1.locals.lookup (ofString "nb"))) m_after.clock
                  ⟨guestInv_congr heff_ktn.code heff_ktn.memaddrs heff_ktn.shMemaddrs heff_ktn.baseAddr hmid_AR.1,
                   arenaOK_congr heff_ktn.globals hmid_AR.2⟩
              refine ⟨hm_AR, ?_, ?_, ?_, ?_⟩
              · rw [← hhp_s, ← hhp_eq]; simp [globN, heff_ktn.globals, hmid_glob, HolFiniteMapExact.lookup_update, FUPDATE, FUPDATE_HOL]; exact hp_le_q
              · simp [globN, heff_ktn.globals, hmid_glob, heff1.globals, HolFiniteMapExact.lookup_update, FUPDATE, FUPDATE_HOL,
                  show ofString "heap_ptr" ≠ ofString "scratch_ptr" by decide]
              · intro a hkeep hfresh; by_contra hne
                by_cases hma : m_after.memory a = m1.memory a
                · rw [hma] at hne
                  obtain ⟨iv, hiv, _, hc1, hc2⟩ := heff1_w.cell_frame a hne
                  simp only [List.mem_append, List.mem_singleton] at hiv
                  rcases hiv with hR0 | rfl
                  · exact hkeep iv (List.mem_append_left _ hR0) ⟨hc1, hc2⟩
                  · exact hfresh ⟨hc1, hc2⟩
                · rw [← hmid_mem] at hma
                  obtain ⟨iv, hiv, _, hc1, hc2⟩ := heff_ktn_w.cell_frame a hma
                  simp only [List.mem_append, List.mem_singleton] at hiv
                  rcases hiv with hR0 | rfl
                  · exact hkeep iv (List.mem_append_left _ hR0) ⟨hc1, hc2⟩
                  · exact hfresh ⟨hc1, hc2⟩
              · intro k hk
                have hne : k ≠ ofString "heap_ptr" := by simpa using hk
                simp [heff_ktn.globals, hmid_glob, heff1.globals, HolFiniteMapExact.lookup_update, FUPDATE, FUPDATE_HOL, hne, Ne.symm hne]
            | none =>
              have hret_eff := byteEff_return m_after ret1 (R0 ++ [(globN s "heap_ptr", heapLimit - globN s "heap_ptr")])
              have heff_tot := heff_ktn_w.trans hret_eff
              set fin := (evaluateHOLFiniteState m_after (.return ret1)).2
              have hm_AR : ArenaReady { fin with locals := fin.locals.resVarEq (ofString "nb", m1.locals.lookup (ofString "nb")) } :=
                localsFree_arenaReady fin (fin.locals.resVarEq (ofString "nb", m1.locals.lookup (ofString "nb"))) fin.clock
                  ⟨guestInv_congr heff_tot.code heff_tot.memaddrs heff_tot.shMemaddrs heff_tot.baseAddr hmid_AR.1,
                   arenaOK_congr heff_tot.globals hmid_AR.2⟩
              refine ⟨hm_AR, ?_, ?_, ?_, ?_⟩
              · rw [← hhp_s, ← hhp_eq]; simp [globN, heff_tot.globals, hmid_glob, HolFiniteMapExact.lookup_update, FUPDATE, FUPDATE_HOL]; exact hp_le_q
              · simp [globN, heff_tot.globals, hmid_glob, heff1.globals, HolFiniteMapExact.lookup_update, FUPDATE, FUPDATE_HOL,
                  show ofString "heap_ptr" ≠ ofString "scratch_ptr" by decide]
              · intro a hkeep hfresh; by_contra hne
                by_cases hma : fin.memory a = m1.memory a
                · rw [hma] at hne
                  obtain ⟨iv, hiv, _, hc1, hc2⟩ := heff1_w.cell_frame a hne
                  simp only [List.mem_append, List.mem_singleton] at hiv
                  rcases hiv with hR0 | rfl
                  · exact hkeep iv (List.mem_append_left _ hR0) ⟨hc1, hc2⟩
                  · exact hfresh ⟨hc1, hc2⟩
                · rw [← hmid_mem] at hma
                  obtain ⟨iv, hiv, _, hc1, hc2⟩ := heff_tot.cell_frame a hma
                  simp only [List.mem_append, List.mem_singleton] at hiv
                  rcases hiv with hR0 | rfl
                  · exact hkeep iv (List.mem_append_left _ hR0) ⟨hc1, hc2⟩
                  · exact hfresh ⟨hc1, hc2⟩
              · intro k hk
                have hne : k ≠ ofString "heap_ptr" := by simpa using hk
                simp [heff_tot.globals, hmid_glob, heff1.globals, HolFiniteMapExact.lookup_update, FUPDATE, FUPDATE_HOL, hne, Ne.symm hne]
    · simp [hcond] at hres; exact absurd hres not_resumes_error
    · simp [hcond] at hres; exact absurd hres not_resumes_error

end InitECandidate.Solver.Wave8GuestInv.R16Shards
