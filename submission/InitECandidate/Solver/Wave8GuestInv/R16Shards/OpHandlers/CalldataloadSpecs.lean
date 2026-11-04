import InitECandidate.Solver.Wave8GuestInv.Deliveries.M11.RlpMemcpyLemmas
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M13.StoreAllocHelpers
import InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.Common
import InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.ReadOnly
import InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.StackPush

/-! # `memzero`, `buffer_read`, and `op_calldataload_spec` -/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers

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
open InitECandidate.Solver.Wave8Contracts.M23

/-! ## 1. Function lookups and `M11.ByteRegionEffect` -> `M23.ByteRegionEffect` bridge -/

theorem lookup_heap_mark :
    originalRuntimeCode.lookup (ofString "heap_mark") =
      some ([], sourceFnBody Guest.Software.guestFn_heap_mark, .one) :=
  lookup_of_guestAst_getElem 8 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_heap_mark) rfl

theorem lookup_heap_release :
    originalRuntimeCode.lookup (ofString "heap_release") =
      some ([(ofString "m", .one)], sourceFnBody Guest.Software.guestFn_heap_release, .one) :=
  lookup_of_guestAst_getElem 9 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_heap_release) rfl

theorem lookup_alloc :
    originalRuntimeCode.lookup (ofString "alloc") =
      some ([(ofString "n", .one)], sourceFnBody Guest.Software.guestFn_alloc, .one) :=
  lookup_of_guestAst_getElem 7 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_alloc) rfl

theorem lookup_memzero :
    originalRuntimeCode.lookup (ofString "memzero") =
      some ([(ofString "dst", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_memzero, .one) :=
  lookup_of_guestAst_getElem 17 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_memzero) rfl

theorem lookup_buffer_read :
    originalRuntimeCode.lookup (ofString "buffer_read") =
      some ([(ofString "buf", .one), (ofString "buf_len", .one),
             (ofString "start", .one), (ofString "size", .one), (ofString "out", .one)],
        sourceFnBody Guest.Software.guestFn_buffer_read, .one) :=
  lookup_of_guestAst_getElem 462 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_buffer_read) rfl

theorem lookup_u256_from_be :
    originalRuntimeCode.lookup (ofString "u256_from_be") =
      some ([(ofString "p", .one), (ofString "n", .one)],
        sourceFnBody Guest.Software.guestFn_u256_from_be, .comb [.one, .one, .one, .one]) :=
  lookup_of_guestAst_getElem 86 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_u256_from_be) rfl

theorem bre_of_m11 {F : Type} {s post : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (h : M11.ByteRegionEffect s post Rl) : ByteRegionEffect s post Rl :=
  ⟨h.code, h.memaddrs, h.shMemaddrs, h.baseAddr, h.be, h.globals, h.out_dom, h.cell_frame, h.byte_frame⟩

/-- Five-word-parameter lookup helper (for `buffer_read`). -/
theorem pan_five_word_lookup {width : Nat} [NeZero width]
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (name p1 p2 p3 p4 p5 : MlS) (body : ProgHOL width) (w1 w2 w3 w4 w5 : BitVec width)
    (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h14 : p1 ≠ p4) (h15 : p1 ≠ p5)
    (h23 : p2 ≠ p3) (h24 : p2 ≠ p4) (h25 : p2 ≠ p5)
    (h34 : p3 ≠ p4) (h35 : p3 ≠ p5) (h45 : p4 ≠ p5)
    (lookup : code name = some ([(p1, .one), (p2, .one), (p3, .one), (p4, .one), (p5, .one)], body, .one)) :
    PanSemStateFiniteExact.lookupCodeHOLFinite code name
        [.val (.word w1), .val (.word w2), .val (.word w3), .val (.word w4), .val (.word w5)] =
      some (body,
        ((((HolFiniteMapExact.empty.update (p1, .val (.word w1))).update (p2, .val (.word w2))).update
            (p3, .val (.word w3))).update (p4, .val (.word w4))).update (p5, .val (.word w5)), .one) := by
  have raw : lookupCodeHOLExact code name
      [.val (.word w1), .val (.word w2), .val (.word w3), .val (.word w4), .val (.word w5)] =
      some (body,
        (fun key =>
          if key = p5 then some (.val (.word w5))
          else if key = p4 then some (.val (.word w4))
          else if key = p3 then some (.val (.word w3))
          else if key = p2 then some (.val (.word w2))
          else if key = p1 then some (.val (.word w1))
          else none), .one) := by
    simp [lookupCodeHOLExact, lookup, shapeOfHOLExact, shapeEqHOL,
      h12, h13, h14, h15, h23, h24, h25, h34, h35, h45]
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite
  split
  · rename_i missing
    rw [raw] at missing
    cases missing
  · rename_i foundBody foundLocals foundShape found
    have equal := Option.some.inj (found.symm.trans raw)
    obtain ⟨rfl, rest⟩ := Prod.mk.inj equal
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj rest
    apply congrArg (fun locals => some (foundBody, locals, ShapeHOL.one))
    apply HolFiniteMapExact.ext
    funext key
    by_cases k5 : key = p5
    · subst k5
      simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY]
    · have k5' : p5 ≠ key := Ne.symm k5
      by_cases k4 : key = p4
      · subst k4
        simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY, k5, k5']
      · have k4' : p4 ≠ key := Ne.symm k4
        by_cases k3 : key = p3
        · subst k3
          simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY, k5, k5', k4, k4']
        · have k3' : p3 ≠ key := Ne.symm k3
          by_cases k2 : key = p2
          · subst k2
            simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY,
              k5, k5', k4, k4', k3, k3']
          · have k2' : p2 ≠ key := Ne.symm k2
            by_cases k1 : key = p1
            · subst k1
              simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY,
                k5, k5', k4, k4', k3, k3', k2, k2']
            · have k1' : p1 ≠ key := Ne.symm k1
              simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY,
                k5, k5', k4, k4', k3, k3', k2, k2', k1, k1']

/-! ## 2. `ByteRegionEffect` of `memzero` -/

private theorem bv_add_small (a b : BitVec 64) (h : a.toNat + b.toNat < 2 ^ 64) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt h

private theorem seq_none_or_err_bre {F : Type} {s : PanSemStateFiniteExact 64 F}
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

private theorem memzero_word_store_step {F : Type}
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
      rw [bv_add_small dst (iv + BitVec.ofNat 64 c) (by rw [hsum_ivc]; omega), hsum_ivc]
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

private theorem memzero_byte_store_step {F : Type}
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
      rw [bv_add_small dst (iv + BitVec.ofNat 64 c) (by rw [hsum_ivc]; omega), hsum_ivc]
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

private def MemzeroBreInv {F : Type} (dst n : BitVec 64)
    (t : PanSemStateFiniteExact 64 F) : Prop :=
  t.memaddrs = ordinaryDomain ∧
  t.locals.lookup (ofString "dst") = some (.val (.word dst)) ∧
  t.locals.lookup (ofString "n") = some (.val (.word n)) ∧
  ∃ iv : BitVec 64,
    t.locals.lookup (ofString "i") = some (.val (.word iv)) ∧
    iv.toNat ≤ n.toNat ∧
    iv.toNat ≤ 33806089704 ∧
    (iv.toNat > 0 → dst.toNat + iv.toNat ≤ 33806089704)

private theorem memzero_loop_runner {F : Type}
    (Rl : List Ivl) (dst n : BitVec 64) (cond : ExpHOL 64) (body : ProgHOL 64)
    (hstep : ∀ (s : PanSemStateFiniteExact 64 F),
      MemzeroBreInv dst n s →
      ∃ cv : BitVec 64,
        @evalHOLFinite 64 F _ s (fun a => Classical.propDecidable (s.memaddrs a)) cond =
          some (.val (.word cv)) ∧
        (cv ≠ 0 →
          (∀ sb, evaluateHOLFiniteState (decClockHOLFinite s) body = (none, sb) →
            MemzeroBreInv dst n sb ∧
            ByteRegionEffect (decClockHOLFinite s) sb Rl) ∧
          (∀ r, r ≠ none → (evaluateHOLFiniteState (decClockHOLFinite s) body).1 = r →
            r = some .error)))
    (s0 : PanSemStateFiniteExact 64 F)
    (hinv : MemzeroBreInv dst n s0)
    (hnt : (evaluateHOLFiniteState s0 (.while cond body)).1 ≠ some .timeOut) :
    ((evaluateHOLFiniteState s0 (.while cond body)).1 = none →
      MemzeroBreInv dst n (evaluateHOLFiniteState s0 (.while cond body)).2 ∧
      ByteRegionEffect s0 (evaluateHOLFiniteState s0 (.while cond body)).2 Rl) ∧
    ((evaluateHOLFiniteState s0 (.while cond body)).1 ≠ none →
      (evaluateHOLFiniteState s0 (.while cond body)).1 = some .error) := by
  suffices hmain : ∀ (k : Nat) (s : PanSemStateFiniteExact 64 F), s.clock = k →
      MemzeroBreInv dst n s →
      (evaluateHOLFiniteState s (.while cond body)).1 ≠ some .timeOut →
      ((evaluateHOLFiniteState s (.while cond body)).1 = none →
        MemzeroBreInv dst n (evaluateHOLFiniteState s (.while cond body)).2 ∧
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

private theorem eval_add2_di {F : Type} (s : PanSemStateFiniteExact 64 F)
    (d iv : BitVec 64)
    (hd : s.locals.lookup (ofString "dst") = some (.val (.word d)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word iv))) :
    @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) =
      some (.val (.word (d + (iv + BitVec.ofNat 64 0)))) := by
  simp only [evalHOLExact, evalListHOLExact, hd, hi, wordOpHOL, wordOp, valueIsWord, valueWord,
    List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr]
  rfl

private theorem eval_add3_dic {F : Type} (s : PanSemStateFiniteExact 64 F)
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

private theorem assign_i_memzero_step {F : Type} (st : PanSemStateFiniteExact 64 F)
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
      MemzeroBreInv dst n p ∧ ByteRegionEffect st p Rl) ∧
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

theorem eval_memzero_body_bre {F : Type}
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
  have hinv1 : MemzeroBreInv dst0 n0 s1 :=
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
      Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, Bool.not_eq_true', decide_eq_false_iff_not]
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
  have hL1 : ∀ t0 : PanSemStateFiniteExact 64 F, MemzeroBreInv dst0 n0 t0 →
      (evaluateHOLFiniteState t0 lp1).1 ≠ some .timeOut →
      ((evaluateHOLFiniteState t0 lp1).1 = none →
        MemzeroBreInv dst0 n0 (evaluateHOLFiniteState t0 lp1).2 ∧
        ByteRegionEffect t0 (evaluateHOLFiniteState t0 lp1).2 Rl) ∧
      ((evaluateHOLFiniteState t0 lp1).1 ≠ none → (evaluateHOLFiniteState t0 lp1).1 = some .error) := by
    intro t0 hinv0 hnt1
    refine memzero_loop_runner Rl dst0 n0 _ _ (fun st ⟨st_ma, st_dst, st_n, iv, st_i, hiv_n, hiv_he, hdom_prev⟩ => ?_) t0 hinv0 hnt1
    refine ⟨if iv.toNat + 32 ≤ n0.toNat then 1 else 0, hcond_nl st iv 32 st_n st_i hiv_he (by omega), fun hcv => ?_⟩
    have hle32 : iv.toNat + 32 ≤ n0.toNat := by split_ifs at hcv with h; exact h; exact absurd rfl hcv
    let d0 := decClockHOLFinite st
    have w0 := memzero_word_store_step (st := d0) (Rl := Rl) (c := 0)
      st_ma (fun hb => hsub_w (iv.toNat + 0) (by omega) (by omega))
      (eval_add2_di d0 dst0 iv st_dst st_i)
      ⟨fun h => by have := hdom_prev (by omega); omega, by omega⟩
    apply seq_none_or_err_bre ⟨fun m hm => (w0.1 m hm).1, w0.2⟩
    intro m1 hm1 he1; obtain ⟨_, l1, dom1⟩ := w0.1 m1 hm1
    have ma1 : m1.memaddrs = ordinaryDomain := he1.memaddrs.trans st_ma
    have w8 := memzero_word_store_step (st := m1) (Rl := Rl) (c := 8)
      ma1 (fun hb => hsub_w (iv.toNat + 8) (by omega) (by omega))
      (eval_add3_dic m1 dst0 iv 8 (l1.symm ▸ st_dst) (l1.symm ▸ st_i)) ⟨fun _ => by omega, by omega⟩
    apply seq_none_or_err_bre ⟨fun m hm => (w8.1 m hm).1, w8.2⟩
    intro m2 hm2 he2; obtain ⟨_, l2, dom2⟩ := w8.1 m2 hm2
    have ma2 : m2.memaddrs = ordinaryDomain := he2.memaddrs.trans ma1
    have w16 := memzero_word_store_step (st := m2) (Rl := Rl) (c := 16)
      ma2 (fun hb => hsub_w (iv.toNat + 16) (by omega) (by omega))
      (eval_add3_dic m2 dst0 iv 16 (by rw [l2, l1]; exact st_dst) (by rw [l2, l1]; exact st_i)) ⟨fun _ => by omega, by omega⟩
    apply seq_none_or_err_bre ⟨fun m hm => (w16.1 m hm).1, w16.2⟩
    intro m3 hm3 he3; obtain ⟨_, l3, dom3⟩ := w16.1 m3 hm3
    have ma3 : m3.memaddrs = ordinaryDomain := he3.memaddrs.trans ma2
    have w24 := memzero_word_store_step (st := m3) (Rl := Rl) (c := 24)
      ma3 (fun hb => hsub_w (iv.toNat + 24) (by omega) (by omega))
      (eval_add3_dic m3 dst0 iv 24 (by rw [l3, l2, l1]; exact st_dst) (by rw [l3, l2, l1]; exact st_i)) ⟨fun _ => by omega, by omega⟩
    apply seq_none_or_err_bre ⟨fun m hm => (w24.1 m hm).1, w24.2⟩
    intro m4 hm4 he4; obtain ⟨_, l4, dom4⟩ := w24.1 m4 hm4
    exact assign_i_memzero_step m4 dst0 iv n0 32 Rl (he4.memaddrs.trans ma3)
      (by rw [l4, l3, l2, l1]; exact st_dst)
      (by rw [l4, l3, l2, l1]; exact st_n)
      (by rw [l4, l3, l2, l1]; exact st_i) (by omega) hle32 (by omega)
  let lp2 : ProgHOL 64 := .while (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 8)]))
    (.seq (.store (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) (.const (BitVec.ofNat 64 0)))
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 8)])))
  have hL2 : ∀ t0 : PanSemStateFiniteExact 64 F, MemzeroBreInv dst0 n0 t0 →
      (evaluateHOLFiniteState t0 lp2).1 ≠ some .timeOut →
      ((evaluateHOLFiniteState t0 lp2).1 = none →
        MemzeroBreInv dst0 n0 (evaluateHOLFiniteState t0 lp2).2 ∧
        ByteRegionEffect t0 (evaluateHOLFiniteState t0 lp2).2 Rl) ∧
      ((evaluateHOLFiniteState t0 lp2).1 ≠ none → (evaluateHOLFiniteState t0 lp2).1 = some .error) := by
    intro t0 hinv0 hnt2
    refine memzero_loop_runner Rl dst0 n0 _ _ (fun st ⟨st_ma, st_dst, st_n, iv, st_i, hiv_n, hiv_he, hdom_prev⟩ => ?_) t0 hinv0 hnt2
    refine ⟨if iv.toNat + 8 ≤ n0.toNat then 1 else 0, hcond_nl st iv 8 st_n st_i hiv_he (by omega), fun hcv => ?_⟩
    have hle8 : iv.toNat + 8 ≤ n0.toNat := by split_ifs at hcv with h; exact h; exact absurd rfl hcv
    let d0 := decClockHOLFinite st
    have w0 := memzero_word_store_step (st := d0) (Rl := Rl) (c := 0)
      st_ma (fun hb => hsub_w (iv.toNat + 0) (by omega) (by omega))
      (eval_add2_di d0 dst0 iv st_dst st_i)
      ⟨fun h => by have := hdom_prev (by omega); omega, by omega⟩
    apply seq_none_or_err_bre ⟨fun m hm => (w0.1 m hm).1, w0.2⟩
    intro m1 hm1 he1; obtain ⟨_, l1, dom1⟩ := w0.1 m1 hm1
    exact assign_i_memzero_step m1 dst0 iv n0 8 Rl (he1.memaddrs.trans st_ma)
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
  have hL3 : ∀ t0 : PanSemStateFiniteExact 64 F, MemzeroBreInv dst0 n0 t0 →
      (evaluateHOLFiniteState t0 lp3).1 ≠ some .timeOut →
      ((evaluateHOLFiniteState t0 lp3).1 = none →
        MemzeroBreInv dst0 n0 (evaluateHOLFiniteState t0 lp3).2 ∧
        ByteRegionEffect t0 (evaluateHOLFiniteState t0 lp3).2 Rl) ∧
      ((evaluateHOLFiniteState t0 lp3).1 ≠ none → (evaluateHOLFiniteState t0 lp3).1 = some .error) := by
    intro t0 hinv0 hnt3
    refine memzero_loop_runner Rl dst0 n0 _ _ (fun st ⟨st_ma, st_dst, st_n, iv, st_i, hiv_n, hiv_he, hdom_prev⟩ => ?_) t0 hinv0 hnt3
    refine ⟨if iv.toNat + 8 ≤ n0.toNat then 1 else 0, hcond_nl st iv 8 st_n st_i hiv_he (by omega), fun hcv => ?_⟩
    have hle8 : iv.toNat + 8 ≤ n0.toNat := by split_ifs at hcv with h; exact h; exact absurd rfl hcv
    let d0 := decClockHOLFinite st
    have b0 := memzero_byte_store_step (st := d0) (Rl := Rl) (c := 0)
      st_ma (fun hb => hsub_b (iv.toNat + 0) (by omega) (by omega))
      (eval_add2_di d0 dst0 iv st_dst st_i) ⟨fun h => by have := hdom_prev (by omega); omega, by omega⟩
    apply seq_none_or_err_bre ⟨fun m hm => (b0.1 m hm).1, b0.2⟩
    intro m1 hm1 he1; obtain ⟨_, l1, dom1⟩ := b0.1 m1 hm1
    have ma1 : m1.memaddrs = ordinaryDomain := he1.memaddrs.trans st_ma
    have b1 := memzero_byte_store_step (st := m1) (Rl := Rl) (c := 1)
      ma1 (fun hb => hsub_b (iv.toNat + 1) (by omega) (by omega))
      (eval_add3_dic m1 dst0 iv 1 (l1.symm ▸ st_dst) (l1.symm ▸ st_i)) ⟨fun _ => by omega, by omega⟩
    apply seq_none_or_err_bre ⟨fun m hm => (b1.1 m hm).1, b1.2⟩
    intro m2 hm2 he2; obtain ⟨_, l2, dom2⟩ := b1.1 m2 hm2
    have ma2 : m2.memaddrs = ordinaryDomain := he2.memaddrs.trans ma1
    have b2 := memzero_byte_store_step (st := m2) (Rl := Rl) (c := 2)
      ma2 (fun hb => hsub_b (iv.toNat + 2) (by omega) (by omega))
      (eval_add3_dic m2 dst0 iv 2 (by rw [l2, l1]; exact st_dst) (by rw [l2, l1]; exact st_i)) ⟨fun _ => by omega, by omega⟩
    apply seq_none_or_err_bre ⟨fun m hm => (b2.1 m hm).1, b2.2⟩
    intro m3 hm3 he3; obtain ⟨_, l3, dom3⟩ := b2.1 m3 hm3
    have ma3 : m3.memaddrs = ordinaryDomain := he3.memaddrs.trans ma2
    have b3 := memzero_byte_store_step (st := m3) (Rl := Rl) (c := 3)
      ma3 (fun hb => hsub_b (iv.toNat + 3) (by omega) (by omega))
      (eval_add3_dic m3 dst0 iv 3 (by rw [l3, l2, l1]; exact st_dst) (by rw [l3, l2, l1]; exact st_i)) ⟨fun _ => by omega, by omega⟩
    apply seq_none_or_err_bre ⟨fun m hm => (b3.1 m hm).1, b3.2⟩
    intro m4 hm4 he4; obtain ⟨_, l4, dom4⟩ := b3.1 m4 hm4
    have ma4 : m4.memaddrs = ordinaryDomain := he4.memaddrs.trans ma3
    have b4 := memzero_byte_store_step (st := m4) (Rl := Rl) (c := 4)
      ma4 (fun hb => hsub_b (iv.toNat + 4) (by omega) (by omega))
      (eval_add3_dic m4 dst0 iv 4 (by rw [l4, l3, l2, l1]; exact st_dst) (by rw [l4, l3, l2, l1]; exact st_i)) ⟨fun _ => by omega, by omega⟩
    apply seq_none_or_err_bre ⟨fun m hm => (b4.1 m hm).1, b4.2⟩
    intro m5 hm5 he5; obtain ⟨_, l5, dom5⟩ := b4.1 m5 hm5
    have ma5 : m5.memaddrs = ordinaryDomain := he5.memaddrs.trans ma4
    have b5 := memzero_byte_store_step (st := m5) (Rl := Rl) (c := 5)
      ma5 (fun hb => hsub_b (iv.toNat + 5) (by omega) (by omega))
      (eval_add3_dic m5 dst0 iv 5 (by rw [l5, l4, l3, l2, l1]; exact st_dst) (by rw [l5, l4, l3, l2, l1]; exact st_i)) ⟨fun _ => by omega, by omega⟩
    apply seq_none_or_err_bre ⟨fun m hm => (b5.1 m hm).1, b5.2⟩
    intro m6 hm6 he6; obtain ⟨_, l6, dom6⟩ := b5.1 m6 hm6
    have ma6 : m6.memaddrs = ordinaryDomain := he6.memaddrs.trans ma5
    have b6 := memzero_byte_store_step (st := m6) (Rl := Rl) (c := 6)
      ma6 (fun hb => hsub_b (iv.toNat + 6) (by omega) (by omega))
      (eval_add3_dic m6 dst0 iv 6 (by rw [l6, l5, l4, l3, l2, l1]; exact st_dst) (by rw [l6, l5, l4, l3, l2, l1]; exact st_i)) ⟨fun _ => by omega, by omega⟩
    apply seq_none_or_err_bre ⟨fun m hm => (b6.1 m hm).1, b6.2⟩
    intro m7 hm7 he7; obtain ⟨_, l7, dom7⟩ := b6.1 m7 hm7
    have ma7 : m7.memaddrs = ordinaryDomain := he7.memaddrs.trans ma6
    have b7 := memzero_byte_store_step (st := m7) (Rl := Rl) (c := 7)
      ma7 (fun hb => hsub_b (iv.toNat + 7) (by omega) (by omega))
      (eval_add3_dic m7 dst0 iv 7 (by rw [l7, l6, l5, l4, l3, l2, l1]; exact st_dst) (by rw [l7, l6, l5, l4, l3, l2, l1]; exact st_i)) ⟨fun _ => by omega, by omega⟩
    apply seq_none_or_err_bre ⟨fun m hm => (b7.1 m hm).1, b7.2⟩
    intro m8 hm8 he8; obtain ⟨_, l8, dom8⟩ := b7.1 m8 hm8
    exact assign_i_memzero_step m8 dst0 iv n0 8 Rl (he8.memaddrs.trans ma7)
      (by rw [l8, l7, l6, l5, l4, l3, l2, l1]; exact st_dst)
      (by rw [l8, l7, l6, l5, l4, l3, l2, l1]; exact st_n)
      (by rw [l8, l7, l6, l5, l4, l3, l2, l1]; exact st_i)
      (by omega) hle8 (by omega)
  let lp4 : ProgHOL 64 := .while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n")))
    (.seq (.storeByte (.op .add [.var .local (ofString "dst"), .var .local (ofString "i")]) (.const (BitVec.ofNat 64 0)))
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const (BitVec.ofNat 64 1)])))
  have hL4 : ∀ t0 : PanSemStateFiniteExact 64 F, MemzeroBreInv dst0 n0 t0 →
      (evaluateHOLFiniteState t0 lp4).1 ≠ some .timeOut →
      ((evaluateHOLFiniteState t0 lp4).1 = none →
        MemzeroBreInv dst0 n0 (evaluateHOLFiniteState t0 lp4).2 ∧
        ByteRegionEffect t0 (evaluateHOLFiniteState t0 lp4).2 Rl) ∧
      ((evaluateHOLFiniteState t0 lp4).1 ≠ none → (evaluateHOLFiniteState t0 lp4).1 = some .error) := by
    intro t0 hinv0 hnt4
    refine memzero_loop_runner Rl dst0 n0 _ _ (fun st ⟨st_ma, st_dst, st_n, iv, st_i, hiv_n, hiv_he, hdom_prev⟩ => ?_) t0 hinv0 hnt4
    have hc4 : @evalHOLFinite 64 F _ st (fun a => Classical.propDecidable (st.memaddrs a))
        (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) =
        some (.val (.word (if iv.toNat < n0.toNat then 1 else 0))) := by
      rw [evalHOLFinite_eq_toExact]
      simp [evalHOLExact, st_i, st_n, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def]
    refine ⟨if iv.toNat < n0.toNat then 1 else 0, hc4, fun hcv => ?_⟩
    have hlt1 : iv.toNat < n0.toNat := by split_ifs at hcv with h; exact h; exact absurd rfl hcv
    let d0 := decClockHOLFinite st
    have b0 := memzero_byte_store_step (st := d0) (Rl := Rl) (c := 0)
      st_ma (fun hb => hsub_b (iv.toNat + 0) (by omega) (by omega))
      (eval_add2_di d0 dst0 iv st_dst st_i) ⟨fun h => by have := hdom_prev (by omega); omega, by omega⟩
    apply seq_none_or_err_bre ⟨fun m hm => (b0.1 m hm).1, b0.2⟩
    intro m1 hm1 he1; obtain ⟨_, l1, dom1⟩ := b0.1 m1 hm1
    exact assign_i_memzero_step m1 dst0 iv n0 1 Rl (he1.memaddrs.trans st_ma)
      (l1.symm ▸ st_dst) (l1.symm ▸ st_n) (l1.symm ▸ st_i)
      (by omega) (by omega) (by omega)
  let iteP : ProgHOL 64 := .ite
    (.cmp .equal (.op .and [.var .local (ofString "dst"), .const (BitVec.ofNat 64 7)]) (.const (BitVec.ofNat 64 0)))
    (.seq lp1 lp2)
    .skip
  have hite_spec : ∀ t0 : PanSemStateFiniteExact 64 F,
      MemzeroBreInv dst0 n0 t0 →
      (evaluateHOLFiniteState t0 iteP).1 ≠ some .timeOut →
      ((evaluateHOLFiniteState t0 iteP).1 = none →
        MemzeroBreInv dst0 n0 (evaluateHOLFiniteState t0 iteP).2 ∧
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
          Compiler.Encoders.Asm.wordCmpHOL] at hcond_ev
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

theorem eval_call_memzero_bre {F : Type}
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
    (by rw [hcode]; exact lookup_memzero)
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
    obtain ⟨_, hret, hexn⟩ := eval_memzero_body_bre entry dst0 n0 Rl hma
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

/-! ## 3. `ByteRegionEffect` of `buffer_read` -/

theorem eval_buffer_read_body_bre {F : Type}
    (s : PanSemStateFiniteExact 64 F) (buf0 buflen0 start0 size0 out0 : BitVec 64) (Rl : List Ivl)
    (hcode : s.code = originalRuntimeCode)
    (hma : s.memaddrs = ordinaryDomain)
    (hbuf : s.locals.lookup (ofString "buf") = some (.val (.word buf0)))
    (hbuflen : s.locals.lookup (ofString "buf_len") = some (.val (.word buflen0)))
    (hstart : s.locals.lookup (ofString "start") = some (.val (.word start0)))
    (hsize : s.locals.lookup (ofString "size") = some (.val (.word size0)))
    (hout : s.locals.lookup (ofString "out") = some (.val (.word out0)))
    (hbnd : out0.toNat + size0.toNat < 2 ^ 64)
    (hsub : 0 < size0.toNat → ∃ ivl ∈ Rl, ivl.1 ≤ out0.toNat ∧ out0.toNat + size0.toNat ≤ ivl.1 + ivl.2)
    (hnt : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_buffer_read)).1 ≠ some .timeOut) :
    let res := evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_buffer_read)
    (∀ rv, res.1 = some (.returned rv) → rv = .val (.word 0) ∧ ByteRegionEffect s res.2 Rl) ∧
    ¬ IsEvmErr res.1 := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_buffer_read,
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
  set s1 := setVarHOLFinite (ofString "avail") (.val (.word 0)) s
  have hs1_buf : s1.locals.lookup (ofString "buf") = some (.val (.word buf0)) := by
    have hne : ofString "avail" ≠ ofString "buf" := by decide
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne, hbuf]
  have hs1_buflen : s1.locals.lookup (ofString "buf_len") = some (.val (.word buflen0)) := by
    have hne : ofString "avail" ≠ ofString "buf_len" := by decide
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne, hbuflen]
  have hs1_start : s1.locals.lookup (ofString "start") = some (.val (.word start0)) := by
    have hne : ofString "avail" ≠ ofString "start" := by decide
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne, hstart]
  have hs1_size : s1.locals.lookup (ofString "size") = some (.val (.word size0)) := by
    have hne : ofString "avail" ≠ ofString "size" := by decide
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne, hsize]
  have hs1_out : s1.locals.lookup (ofString "out") = some (.val (.word out0)) := by
    have hne : ofString "avail" ≠ ofString "out" := by decide
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne, hout]
  have hs1_avail : s1.locals.lookup (ofString "avail") = some (.val (.word 0)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have heff_s_s1 : ByteRegionEffect s s1 Rl :=
    ByteRegionEffect.refl s Rl |>.with_locals_clock s1.locals s1.clock
  let ite1 : ProgHOL 64 := .ite (.cmp .lower (.var .local (ofString "start")) (.var .local (ofString "buf_len")))
    (.seq (.assign .local (ofString "avail") (.op .sub [.var .local (ofString "buf_len"), .var .local (ofString "start")]))
      (.seq (.ite (.cmp .lower (.var .local (ofString "size")) (.var .local (ofString "avail")))
              (.assign .local (ofString "avail") (.var .local (ofString "size"))) .skip)
        (.call (some (none, none)) (ofString "memcpy")
          [.var .local (ofString "out"),
           .op .add [.var .local (ofString "buf"), .var .local (ofString "start")],
           .var .local (ofString "avail")])))
    .skip
  let mzCall : ProgHOL 64 := .call (some (none, none)) (ofString "memzero")
    [.op .add [.var .local (ofString "out"), .var .local (ofString "avail")],
     .op .sub [.var .local (ofString "size"), .var .local (ofString "avail")]]
  change (let res := (let r0 := evaluateHOLFiniteState s1 (.seq ite1 (.seq mzCall (.return (.const 0))))
      (r0.1, { r0.2 with locals := HolFiniteMapExact.resVarEq r0.2.locals (ofString "avail", s.locals.lookup (ofString "avail")) }))
    (∀ rv, res.1 = some (.returned rv) → rv = .val (.word 0) ∧ ByteRegionEffect s res.2 Rl) ∧
    ¬ IsEvmErr res.1)
  have hnt' : (evaluateHOLFiniteState s1 (.seq ite1 (.seq mzCall (.return (.const 0))))).1 ≠ some .timeOut := hnt
  clear hnt
  have hite1_spec :
      ((evaluateHOLFiniteState s1 ite1).1 = none →
        let m := (evaluateHOLFiniteState s1 ite1).2
        ByteRegionEffect s1 m Rl ∧
        m.locals.lookup (ofString "size") = some (.val (.word size0)) ∧
        m.locals.lookup (ofString "out") = some (.val (.word out0)) ∧
        ∃ av : BitVec 64, m.locals.lookup (ofString "avail") = some (.val (.word av)) ∧ av.toNat ≤ size0.toNat) ∧
      ((evaluateHOLFiniteState s1 ite1).1 ≠ none → ¬ Resumes (evaluateHOLFiniteState s1 ite1).1) := by
    have hnt_ite1 : (evaluateHOLFiniteState s1 ite1).1 ≠ some .timeOut := by
      rintro hto
      rw [evaluateHOLFiniteState_seq_line780] at hnt'
      rcases hr : evaluateHOLFiniteState s1 ite1 with ⟨o, t⟩
      rw [hr] at hto hnt'; dsimp only at hto hnt'; subst hto; exact hnt' rfl
    dsimp only [ite1] at hnt_ite1 ⊢
    have hc1 : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
        (.cmp .lower (.var .local (ofString "start")) (.var .local (ofString "buf_len"))) =
        some (.val (.word (if start0.toNat < buflen0.toNat then 1 else 0))) := by
      simp [evalHOLExact, hs1_start, hs1_buflen, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def]
    rw [evaluateHOLFiniteState_ite, hc1] at hnt_ite1 ⊢
    by_cases hlt_sb : start0.toNat < buflen0.toNat
    · simp only [hlt_sb, ↓reduceIte, show (1 : BitVec 64) ≠ 0 by decide] at hnt_ite1 ⊢
      rw [evaluateHOLFiniteState_seq_line780] at hnt_ite1 ⊢
      have hsub_ev : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
          (.op .sub [.var .local (ofString "buf_len"), .var .local (ofString "start")]) =
          some (.val (.word (buflen0 - start0))) := by
        simp [evalHOLExact, evalListHOLExact, hs1_buflen, hs1_start, wordOpHOL, wordOp, valueIsWord, valueWord]
      have hvld1 : isValidValueHOLFinite s1 .local (ofString "avail") (.val (.word (buflen0 - start0))) = true := by
        simp [isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLExact, hs1_avail, shapeOfHOLExact, shapeEqHOL]
      have hasg1 : evaluateHOLFiniteState s1
          (.assign .local (ofString "avail") (.op .sub [.var .local (ofString "buf_len"), .var .local (ofString "start")])) =
          (none, setVarHOLFinite (ofString "avail") (.val (.word (buflen0 - start0))) s1) := by
        rw [evaluateHOLFiniteState_assign, hsub_ev]; dsimp only; rw [if_pos hvld1]; rfl
      rw [hasg1] at hnt_ite1 ⊢; dsimp only at hnt_ite1 ⊢
      set s2 := setVarHOLFinite (ofString "avail") (.val (.word (buflen0 - start0))) s1
      have hs2_avail : s2.locals.lookup (ofString "avail") = some (.val (.word (buflen0 - start0))) := by
        simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      have hs2_size : s2.locals.lookup (ofString "size") = some (.val (.word size0)) := by
        have hne : ofString "avail" ≠ ofString "size" := by decide
        simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne, hs1_size]
      have hs2_out : s2.locals.lookup (ofString "out") = some (.val (.word out0)) := by
        have hne : ofString "avail" ≠ ofString "out" := by decide
        simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne, hs1_out]
      have hs2_buf : s2.locals.lookup (ofString "buf") = some (.val (.word buf0)) := by
        have hne : ofString "avail" ≠ ofString "buf" := by decide
        simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne, hs1_buf]
      have hs2_start : s2.locals.lookup (ofString "start") = some (.val (.word start0)) := by
        have hne : ofString "avail" ≠ ofString "start" := by decide
        simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne, hs1_start]
      rw [evaluateHOLFiniteState_seq_line780] at hnt_ite1 ⊢
      have hc2 : @evalHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a))
          (.cmp .lower (.var .local (ofString "size")) (.var .local (ofString "avail"))) =
          some (.val (.word (if size0.toNat < (buflen0 - start0).toNat then 1 else 0))) := by
        simp [evalHOLExact, hs2_size, hs2_avail, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def]
      rw [evaluateHOLFiniteState_ite, hc2] at hnt_ite1 ⊢
      have hclamp : ∃ s3 : PanSemStateFiniteExact 64 F, ∃ av : BitVec 64,
          (if (if size0.toNat < (buflen0 - start0).toNat then (1 : BitVec 64) else 0) = 0 then
            evaluateHOLFiniteState s2 .skip
          else
            evaluateHOLFiniteState s2 (.assign .local (ofString "avail") (.var .local (ofString "size")))) = (none, s3) ∧
          ByteRegionEffect s1 s3 Rl ∧
          s3.code = originalRuntimeCode ∧ s3.memaddrs = ordinaryDomain ∧
          s3.locals.lookup (ofString "buf") = some (.val (.word buf0)) ∧
          s3.locals.lookup (ofString "start") = some (.val (.word start0)) ∧
          s3.locals.lookup (ofString "size") = some (.val (.word size0)) ∧
          s3.locals.lookup (ofString "out") = some (.val (.word out0)) ∧
          s3.locals.lookup (ofString "avail") = some (.val (.word av)) ∧
          av.toNat ≤ size0.toNat := by
        by_cases hlt_sa : size0.toNat < (buflen0 - start0).toNat
        · simp only [hlt_sa, ↓reduceIte, show (1 : BitVec 64) ≠ 0 by decide]
          have hvld2 : isValidValueHOLFinite s2 .local (ofString "avail") (.val (.word size0)) = true := by
            simp [isValidValueHOLFinite, isValidValueHOLExact, lookupKvarHOLExact, hs2_avail, shapeOfHOLExact, shapeEqHOL]
          have hasg2 : evaluateHOLFiniteState s2 (.assign .local (ofString "avail") (.var .local (ofString "size"))) =
              (none, setVarHOLFinite (ofString "avail") (.val (.word size0)) s2) := by
            rw [evaluateHOLFiniteState_assign]; simp only [evalHOLExact, hs2_size]; rw [if_pos hvld2]; rfl
          refine ⟨setVarHOLFinite (ofString "avail") (.val (.word size0)) s2, size0, hasg2,
            ByteRegionEffect.refl s1 Rl |>.with_locals_clock _ s1.clock, hcode, hma, ?_, ?_, ?_, ?_, ?_, le_refl _⟩
          · have hne : ofString "avail" ≠ ofString "buf" := by decide
            simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne, hs2_buf]
          · have hne : ofString "avail" ≠ ofString "start" := by decide
            simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne, hs2_start]
          · have hne : ofString "avail" ≠ ofString "size" := by decide
            simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne, hs2_size]
          · have hne : ofString "avail" ≠ ofString "out" := by decide
            simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne, hs2_out]
          · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        · simp only [hlt_sa, ↓reduceIte, evaluateHOLFiniteState_skip]
          refine ⟨s2, buflen0 - start0, rfl, ByteRegionEffect.refl s1 Rl |>.with_locals_clock _ s1.clock,
            hcode, hma, hs2_buf, hs2_start, hs2_size, hs2_out, hs2_avail, by omega⟩
      obtain ⟨s3, av, hcl_eq, heff_s1_s3, hs3_code, hs3_ma, hs3_buf, hs3_start, hs3_size, hs3_out, hs3_av, hav_le⟩ := hclamp
      dsimp only at hnt_ite1 ⊢
      rw [hcl_eq] at hnt_ite1 ⊢; dsimp only at hnt_ite1 ⊢
      have hsrc_ev : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
          (.op .add [.var .local (ofString "buf"), .var .local (ofString "start")]) =
          some (.val (.word (buf0 + (start0 + 0)))) := by
        simp only [evalHOLExact, evalListHOLExact, hs3_buf, hs3_start, wordOpHOL, wordOp, valueIsWord, valueWord,
          List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr]
      have hmc := M11.eval_call_memcpy_bre s3
        (.var .local (ofString "out"))
        (.op .add [.var .local (ofString "buf"), .var .local (ofString "start")])
        (.var .local (ofString "avail"))
        out0 (buf0 + (start0 + 0)) av Rl hs3_code hs3_ma hs3_out hsrc_ev hs3_av
        (fun hpos => by
          obtain ⟨ivl, hivl, h1, h2⟩ := hsub (by omega)
          exact ⟨ivl, hivl, h1, by omega⟩)
        hnt_ite1
      exact ⟨fun hn => by
        obtain ⟨hm11, hloc⟩ := hmc.1 hn
        exact ⟨heff_s1_s3.trans (bre_of_m11 hm11), hloc.symm ▸ hs3_size, hloc.symm ▸ hs3_out, av, hloc.symm ▸ hs3_av, hav_le⟩,
        hmc.2⟩
    · simp only [hlt_sb, ↓reduceIte, evaluateHOLFiniteState_skip]
      exact ⟨fun _ => ⟨ByteRegionEffect.refl s1 Rl, hs1_size, hs1_out, 0, hs1_avail, Nat.zero_le _⟩,
        fun h => False.elim (h rfl)⟩
  rw [evaluateHOLFiniteState_seq_line780] at hnt' ⊢
  rcases hr_ite1 : evaluateHOLFiniteState s1 ite1 with ⟨r1, m1⟩
  rw [hr_ite1] at hite1_spec hnt'
  dsimp only at hite1_spec hnt' ⊢
  cases r1 with
  | some r0 =>
    have hnr := hite1_spec.2 (by simp)
    exact ⟨fun rv hrv => False.elim (hnr (Or.inl ⟨rv, hrv⟩)),
      fun ⟨ev, hex⟩ => hnr (Or.inr ⟨ofString "EvmErr", ev, hex, by decide⟩)⟩
  | none =>
    dsimp only at hnt' ⊢
    obtain ⟨heff_m1, hm1_size, hm1_out, av, hm1_av, hav_le⟩ := hite1_spec.1 rfl
    rw [evaluateHOLFiniteState_seq_line780] at hnt' ⊢
    have hnt_mz : (evaluateHOLFiniteState m1 mzCall).1 ≠ some .timeOut := by
      rintro hto
      rcases hr : evaluateHOLFiniteState m1 mzCall with ⟨o, t⟩
      rw [hr] at hto hnt'; dsimp only at hto hnt'; subst hto; exact hnt' rfl
    have hm1_code : m1.code = originalRuntimeCode := heff_m1.code.trans hcode
    have hm1_ma : m1.memaddrs = ordinaryDomain := heff_m1.memaddrs.trans hma
    have hdst_mz : @evalHOLExact 64 F _ m1.toExact (fun a => Classical.propDecidable (m1.memaddrs a))
        (.op .add [.var .local (ofString "out"), .var .local (ofString "avail")]) =
        some (.val (.word (out0 + (av + 0)))) := by
      simp only [evalHOLExact, evalListHOLExact, hm1_out, hm1_av, wordOpHOL, wordOp, valueIsWord, valueWord,
        List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr]
    have hn_mz : @evalHOLExact 64 F _ m1.toExact (fun a => Classical.propDecidable (m1.memaddrs a))
        (.op .sub [.var .local (ofString "size"), .var .local (ofString "avail")]) =
        some (.val (.word (size0 - av))) := by
      simp [evalHOLExact, evalListHOLExact, hm1_size, hm1_av, wordOpHOL, wordOp, valueIsWord, valueWord]
    have hdst_mz_nat : (out0 + (av + 0)).toNat = out0.toNat + av.toNat := by
      have hav0 : av + 0 = av := BitVec.add_zero av
      rw [hav0]
      exact bv_add_small out0 av (by omega)
    have hn_mz_nat : (size0 - av).toNat = size0.toNat - av.toNat :=
      BitVec.toNat_sub_of_le (BitVec.le_def.2 hav_le)
    have hmz := eval_call_memzero_bre m1
      (.op .add [.var .local (ofString "out"), .var .local (ofString "avail")])
      (.op .sub [.var .local (ofString "size"), .var .local (ofString "avail")])
      (out0 + (av + 0)) (size0 - av) Rl hm1_code hm1_ma hdst_mz hn_mz
      (fun hpos => by
        rw [hn_mz_nat] at hpos
        obtain ⟨ivl, hivl, h1, h2⟩ := hsub (by omega)
        exact ⟨ivl, hivl, by rw [hdst_mz_nat]; omega, by rw [hdst_mz_nat, hn_mz_nat]; omega⟩)
      hnt_mz
    rcases hr_mz : evaluateHOLFiniteState m1 mzCall with ⟨r2, m2⟩
    rw [hr_mz] at hmz hnt'
    dsimp only at hmz hnt' ⊢
    cases r2 with
    | some r0 =>
      have hnr := hmz.2 (by simp)
      exact ⟨fun rv hrv => False.elim (hnr (Or.inl ⟨rv, hrv⟩)),
        fun ⟨ev, hex⟩ => hnr (Or.inr ⟨ofString "EvmErr", ev, hex, by decide⟩)⟩
    | none =>
      dsimp only at hnt' ⊢
      obtain ⟨heff_m2, _⟩ := hmz.1 rfl
      rw [evaluateHOLFiniteState_return]
      have hev_r0 : @evalHOLExact 64 F _ m2.toExact
          (fun a => Classical.propDecidable (m2.memaddrs a)) (.const 0) =
          some (.val (.word 0)) := rfl
      have hsz : sizeOfShapeWithContextHOL m2.structs (shapeOfHOLExact (.val (.word 0) : ValueHOL 64)) ≤ 32 := by
        simp [shapeOfHOLExact]
      rw [hev_r0]; dsimp only; rw [if_pos hsz]; dsimp only
      have heff_all : ByteRegionEffect s (emptyLocalsHOLFinite m2) Rl :=
        ((heff_s_s1.trans heff_m1).trans heff_m2).with_locals_clock _ _
      refine ⟨fun rv hrv => ?_, by rintro ⟨_, h⟩; cases h⟩
      injection hrv with hrv'; injection hrv' with hrv''
      exact ⟨hrv''.symm, heff_all.with_locals_clock _ _⟩

theorem eval_call_buffer_read_bre {F : Type}
    (s : PanSemStateFiniteExact 64 F) (bufExp buflenExp startExp sizeExp outExp : ExpHOL 64)
    (buf0 buflen0 start0 size0 out0 : BitVec 64) (Rl : List Ivl)
    (hcode : s.code = originalRuntimeCode)
    (hma : s.memaddrs = ordinaryDomain)
    (hbuf : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) bufExp =
      some (.val (.word buf0)))
    (hbuflen : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) buflenExp =
      some (.val (.word buflen0)))
    (hstart : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) startExp =
      some (.val (.word start0)))
    (hsize : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) sizeExp =
      some (.val (.word size0)))
    (hout : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) outExp =
      some (.val (.word out0)))
    (hbnd : out0.toNat + size0.toNat < 2 ^ 64)
    (hsub : 0 < size0.toNat → ∃ ivl ∈ Rl, ivl.1 ≤ out0.toNat ∧ out0.toNat + size0.toNat ≤ ivl.1 + ivl.2)
    (hnt : (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "buffer_read") [bufExp, buflenExp, startExp, sizeExp, outExp])).1 ≠
      some .timeOut) :
    let out := evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "buffer_read") [bufExp, buflenExp, startExp, sizeExp, outExp])
    (out.1 = none → ByteRegionEffect s out.2 Rl ∧ out.2.locals = s.locals) ∧
    (out.1 ≠ none → (∀ rv, out.1 ≠ some (.returned rv)) ∧ ¬ IsEvmErr out.1) := by
  dsimp only
  rw [evaluateHOLFiniteState_call] at hnt ⊢
  have hargs : evalListHOLFinite s
      (h := fun a => Classical.propDecidable (s.memaddrs a)) [bufExp, buflenExp, startExp, sizeExp, outExp] =
      some [.val (.word buf0), .val (.word buflen0), .val (.word start0), .val (.word size0), .val (.word out0)] := by
    simp [evalListHOLFinite, evalListHOLExact, hbuf, hbuflen, hstart, hsize, hout]
  have hlook := pan_five_word_lookup s.code.lookup (ofString "buffer_read")
    (ofString "buf") (ofString "buf_len") (ofString "start") (ofString "size") (ofString "out")
    (sourceFnBody Guest.Software.guestFn_buffer_read) buf0 buflen0 start0 size0 out0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [hcode]; exact lookup_buffer_read)
  rw [hargs] at hnt ⊢; dsimp only at hnt ⊢
  rw [hlook] at hnt ⊢; dsimp only at hnt ⊢
  by_cases hclk0 : s.clock = 0
  · rw [if_pos hclk0] at hnt; exact absurd rfl hnt
  · rw [if_neg hclk0] at hnt ⊢
    let cmap : HolFiniteMapExact MlS (ValueHOL 64) :=
      ((((HolFiniteMapExact.empty.update (ofString "buf", ValueHOL.val (.word buf0))).update
          (ofString "buf_len", ValueHOL.val (.word buflen0))).update
          (ofString "start", ValueHOL.val (.word start0))).update
          (ofString "size", ValueHOL.val (.word size0))).update
          (ofString "out", ValueHOL.val (.word out0))
    let entry := callEntryStateHOLFinite s cmap
    have hent_buf : entry.locals.lookup (ofString "buf") = some (.val (.word buf0)) := by
      have h1 : ofString "out" ≠ ofString "buf" := by decide
      have h2 : ofString "size" ≠ ofString "buf" := by decide
      have h3 : ofString "start" ≠ ofString "buf" := by decide
      have h4 : ofString "buf_len" ≠ ofString "buf" := by decide
      simp [entry, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        h1, h2, h3, h4, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4]
    have hent_buflen : entry.locals.lookup (ofString "buf_len") = some (.val (.word buflen0)) := by
      have h1 : ofString "out" ≠ ofString "buf_len" := by decide
      have h2 : ofString "size" ≠ ofString "buf_len" := by decide
      have h3 : ofString "start" ≠ ofString "buf_len" := by decide
      simp [entry, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        h1, h2, h3, Ne.symm h1, Ne.symm h2, Ne.symm h3]
    have hent_start : entry.locals.lookup (ofString "start") = some (.val (.word start0)) := by
      have h1 : ofString "out" ≠ ofString "start" := by decide
      have h2 : ofString "size" ≠ ofString "start" := by decide
      simp [entry, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        h1, h2, Ne.symm h1, Ne.symm h2]
    have hent_size : entry.locals.lookup (ofString "size") = some (.val (.word size0)) := by
      have h1 : ofString "out" ≠ ofString "size" := by decide
      simp [entry, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, h1, Ne.symm h1]
    have hent_out : entry.locals.lookup (ofString "out") = some (.val (.word out0)) := by
      simp [entry, cmap, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    rcases hb : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_buffer_read) with ⟨br, bs⟩
    have hnt_b : br ≠ some .timeOut := by
      rintro rfl
      have hb' : evaluateHOLFiniteState (callEntryStateHOLFinite s cmap)
        (sourceFnBody Guest.Software.guestFn_buffer_read) = (some .timeOut, bs) := hb
      rw [hb'] at hnt; exact hnt rfl
    obtain ⟨hret, hnevm⟩ := eval_buffer_read_body_bre entry buf0 buflen0 start0 size0 out0 Rl
      hcode hma hent_buf hent_buflen hent_start hent_size hent_out hbnd hsub (by rw [hb]; exact hnt_b)
    rw [hb] at hret hnevm
    dsimp only at hret hnevm
    cases br with
    | none =>
      exact ⟨fun h => by simp at h, fun _ => ⟨fun _ h => by simp at h, by rintro ⟨_, h⟩; cases h⟩⟩
    | some r =>
      cases r with
      | timeOut => exact absurd rfl hnt_b
      | exception eid ev =>
        exact ⟨fun h => by simp at h, fun _ => ⟨fun _ h => by simp at h, hnevm⟩⟩
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
        exact ⟨fun h => by simp at h, fun _ => ⟨fun _ h => by simp at h, by rintro ⟨_, h⟩; cases h⟩⟩

/-! ## 4. `alloc_body_no_evmErr`, `heapGap_disj`, and `op_calldataload_spec` -/

theorem lookup_bswap64 :
    originalRuntimeCode.lookup (ofString "bswap64") =
      some ([(ofString "x", .one)],
        sourceFnBody Guest.Software.guestFn_bswap64, .one) :=
  lookup_of_guestAst_getElem 23 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_bswap64) rfl

def noRaiseProg (good : MlS → Bool) : ProgHOL 64 → Bool
  | .dec _ _ _ body => noRaiseProg good body
  | .seq first second => noRaiseProg good first && noRaiseProg good second
  | .ite _ yes no => noRaiseProg good yes && noRaiseProg good no
  | .while _ body => noRaiseProg good body
  | .decCall _ _ fname _ cont => good fname && noRaiseProg good cont
  | .call none fname _ => good fname
  | .call (some (none, none)) fname _ => good fname
  | .call (some (some (.local, _), none)) fname _ => good fname
  | .assign .local _ _ => true
  | .primitive _ _ _ => true
  | .skip | .break | .continue | .annot _ _ | .return _ => true
  | _ => false

theorem evaluate_noRaiseProg {F : Type} (good : MlS → Bool)
    (hgood : ∀ function, good function = true → ∀ values body callee rs,
      PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup function values =
        some (body, callee, rs) →
      noRaiseProg good body = true)
    (program : ProgHOL 64) (supported : noRaiseProg good program = true)
    (state : PanSemStateFiniteExact 64 F) (code : state.code = originalRuntimeCode) :
    ¬ IsEvmErr (evaluateHOLFiniteState state program).1 := by
  cases shape : program with
  | skip => rw [evaluateHOLFiniteState_skip]; rintro ⟨_, h⟩; cases h
  | «break» => rw [evaluateHOLFiniteState_break]; rintro ⟨_, h⟩; cases h
  | «continue» => rw [evaluateHOLFiniteState_continue]; rintro ⟨_, h⟩; cases h
  | annot _ _ => rw [evaluateHOLFiniteState_annot]; rintro ⟨_, h⟩; cases h
  | «return» _ =>
    rw [evaluateHOLFiniteState_return]
    split
    · rintro ⟨_, h⟩; cases h
    · split <;> (rintro ⟨_, h⟩; cases h)
  | assign kind name value =>
    cases kind with
    | global => simp [shape, noRaiseProg] at supported
    | «local» =>
      rw [evaluateHOLFiniteState_assign]
      split
      · rintro ⟨_, h⟩; cases h
      · split <;> (rintro ⟨_, h⟩; cases h)
  | primitive name op args =>
    rw [evaluateHOLFiniteState_primitive]
    split
    · rintro ⟨_, h⟩; cases h
    · split
      · rintro ⟨_, h⟩; cases h
      · split <;> (rintro ⟨_, h⟩; cases h)
  | dec name kind initializer body =>
    have child : noRaiseProg good body = true := by simpa only [shape, noRaiseProg] using supported
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · rintro ⟨_, h⟩; cases h
    · rename_i val _
      split
      · have ih := evaluate_noRaiseProg good hgood body child (setVarHOLFinite name val state) code
        rcases hrun : evaluateHOLFiniteState (setVarHOLFinite name val state) body with ⟨res, st⟩
        rw [hrun] at ih; exact ih
      · rintro ⟨_, h⟩; cases h
  | seq first second =>
    have children : noRaiseProg good first = true ∧ noRaiseProg good second = true := by
      simpa only [shape, noRaiseProg, Bool.and_eq_true] using supported
    have ih1 := evaluate_noRaiseProg good hgood first children.1 state code
    have remaining := evaluateHOLFiniteState_clock_le state first
    have meta' := PanRunBounded.evaluateHOLFiniteState_metadata state first
    rw [evaluateHOLFiniteState_seq_line780]
    rcases firstRun : evaluateHOLFiniteState state first with ⟨result, middle⟩
    rw [firstRun] at ih1 remaining meta'
    dsimp only at ih1 remaining meta' ⊢
    cases result with
    | none =>
      have mclock : middle.clock ≤ state.clock := remaining
      exact evaluate_noRaiseProg good hgood second children.2 middle (meta'.1.trans code)
    | some _ => exact ih1
  | ite condition yes no =>
    have children : noRaiseProg good yes = true ∧ noRaiseProg good no = true := by
      simpa only [shape, noRaiseProg, Bool.and_eq_true] using supported
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_noRaiseProg good hgood no children.2 state code
      · exact evaluate_noRaiseProg good hgood yes children.1 state code
    · rintro ⟨_, h⟩; cases h
  | «while» condition body =>
    have child : noRaiseProg good body = true := by simpa only [shape, noRaiseProg] using supported
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · rintro ⟨_, h⟩; cases h
        · rename_i nonzero
          dsimp only
          rw [fixClockHOLFinite_evaluateState]
          have ih1 := evaluate_noRaiseProg good hgood body child (decClockHOLFinite state) code
          have remaining := evaluateHOLFiniteState_clock_le (decClockHOLFinite state) body
          have meta' := PanRunBounded.evaluateHOLFiniteState_metadata (decClockHOLFinite state) body
          rcases bodyRun : evaluateHOLFiniteState (decClockHOLFinite state) body with ⟨result, middle⟩
          rw [bodyRun] at ih1 remaining meta'
          dsimp only at ih1 remaining meta' ⊢
          have smaller : middle.clock < state.clock := by
            change middle.clock ≤ state.clock - 1 at remaining
            omega
          have mCode : middle.code = originalRuntimeCode := meta'.1.trans code
          cases result with
          | none =>
            exact evaluate_noRaiseProg good hgood (.while condition body)
              (by simpa [noRaiseProg] using child) middle mCode
          | some r =>
            cases r with
            | «continue» =>
              exact evaluate_noRaiseProg good hgood (.while condition body)
                (by simpa [noRaiseProg] using child) middle mCode
            | «break» | returned _ | finalFfi _ | error | timeOut =>
              rintro ⟨_, h⟩; cases h
            | exception _ _ => exact ih1
      · rintro ⟨_, h⟩; cases h
    · rintro ⟨_, h⟩; cases h
  | call ret fname arguments =>
    rcases ret with _ | ⟨dest, hdl⟩
    · have hfn : good fname = true := by simpa only [shape, noRaiseProg] using supported
      rw [evaluateHOLFiniteState_call]
      rcases evalListHOLFinite state
          (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments with _ | values
      · rintro ⟨_, h⟩; cases h
      · dsimp only
        rcases found : lookupCodeHOLFinite state.code.lookup fname values with _ | ⟨body, callee, rs⟩
        · rintro ⟨_, h⟩; cases h
        · dsimp only
          have found' : lookupCodeHOLFinite originalRuntimeCode.lookup fname values =
              some (body, callee, rs) := by rwa [← code]
          have bodyOk := hgood fname hfn values body callee rs found'
          split
          · rintro ⟨_, h⟩; cases h
          · have ih := evaluate_noRaiseProg good hgood body bodyOk
              (callEntryStateHOLFinite state callee) code
            have cl := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite state callee) body
            rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with ⟨res, st⟩
            rw [hrun] at ih cl; dsimp only at ih cl ⊢
            change st.clock ≤ state.clock - 1 at cl
            have small : st.clock < state.clock := by omega
            cases res with
            | none => rintro ⟨_, h⟩; cases h
            | some r =>
              cases r with
              | returned _ => dsimp only; split <;> (rintro ⟨_, h⟩; cases h)
              | exception _ _ => exact ih
              | _ => rintro ⟨_, h⟩; cases h
    · rcases hdl with _ | _
      · rcases dest with _ | ⟨vk, vnm⟩
        · have hfn : good fname = true := by simpa only [shape, noRaiseProg] using supported
          rw [evaluateHOLFiniteState_call]
          rcases evalListHOLFinite state
              (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments with _ | values
          · rintro ⟨_, h⟩; cases h
          · dsimp only
            rcases found : lookupCodeHOLFinite state.code.lookup fname values with _ | ⟨body, callee, rs⟩
            · rintro ⟨_, h⟩; cases h
            · dsimp only
              have found' : lookupCodeHOLFinite originalRuntimeCode.lookup fname values =
                  some (body, callee, rs) := by rwa [← code]
              have bodyOk := hgood fname hfn values body callee rs found'
              split
              · rintro ⟨_, h⟩; cases h
              · have ih := evaluate_noRaiseProg good hgood body bodyOk
                  (callEntryStateHOLFinite state callee) code
                have cl := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite state callee) body
                rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with ⟨res, st⟩
                rw [hrun] at ih cl; dsimp only at ih cl ⊢
                change st.clock ≤ state.clock - 1 at cl
                have small : st.clock < state.clock := by omega
                cases res with
                | none => rintro ⟨_, h⟩; cases h
                | some r =>
                  cases r with
                  | returned _ => dsimp only; split <;> (rintro ⟨_, h⟩; cases h)
                  | exception _ _ => exact ih
                  | _ => rintro ⟨_, h⟩; cases h
        · cases vk with
          | global => simp [shape, noRaiseProg] at supported
          | «local» =>
            have hfn : good fname = true := by simpa only [shape, noRaiseProg] using supported
            rw [evaluateHOLFiniteState_call]
            rcases evalListHOLFinite state
                (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments with _ | values
            · rintro ⟨_, h⟩; cases h
            · dsimp only
              rcases found : lookupCodeHOLFinite state.code.lookup fname values with _ | ⟨body, callee, rs⟩
              · rintro ⟨_, h⟩; cases h
              · dsimp only
                have found' : lookupCodeHOLFinite originalRuntimeCode.lookup fname values =
                    some (body, callee, rs) := by rwa [← code]
                have bodyOk := hgood fname hfn values body callee rs found'
                split
                · rintro ⟨_, h⟩; cases h
                · have ih := evaluate_noRaiseProg good hgood body bodyOk
                    (callEntryStateHOLFinite state callee) code
                  have cl := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite state callee) body
                  rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with ⟨res, st⟩
                  rw [hrun] at ih cl; dsimp only at ih cl ⊢
                  change st.clock ≤ state.clock - 1 at cl
                  have small : st.clock < state.clock := by omega
                  cases res with
                  | none => rintro ⟨_, h⟩; cases h
                  | some r =>
                    cases r with
                    | returned _ =>
                      dsimp only; split
                      · split <;> (rintro ⟨_, h⟩; cases h)
                      · rintro ⟨_, h⟩; cases h
                    | exception _ _ => exact ih
                    | _ => rintro ⟨_, h⟩; cases h
      · simp [shape, noRaiseProg] at supported
  | decCall name kind function arguments continuation =>
    have children : good function = true ∧ noRaiseProg good continuation = true := by
      simpa only [shape, noRaiseProg, Bool.and_eq_true] using supported
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
    rcases evalListHOLFinite state
        (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments with _ | values
    · rintro ⟨_, h⟩; cases h
    · dsimp only
      rcases found : lookupCodeHOLFinite state.code.lookup function values with _ | ⟨body, callee, rs⟩
      · rintro ⟨_, h⟩; cases h
      · dsimp only
        have found' : lookupCodeHOLFinite originalRuntimeCode.lookup function values =
            some (body, callee, rs) := by rwa [← code]
        have bodyOk := hgood function children.1 values body callee rs found'
        split
        · rintro ⟨_, h⟩; cases h
        · rename_i nonzero
          have ih := evaluate_noRaiseProg good hgood body bodyOk
            (callEntryStateHOLFinite state callee) code
          have meta' := PanRunBounded.evaluateHOLFiniteState_metadata
            (callEntryStateHOLFinite state callee) body
          have cl := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite state callee) body
          rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with ⟨res, st⟩
          rw [hrun] at ih meta' cl; dsimp only at ih meta' cl ⊢
          change st.clock ≤ state.clock - 1 at cl
          have small : st.clock < state.clock := by omega
          have stCode : st.code = originalRuntimeCode := meta'.1.trans code
          cases res with
          | none => rintro ⟨_, h⟩; cases h
          | some r =>
            cases r with
            | returned v =>
              dsimp only
              split
              · set resumed := setVarHOLFinite name v { st with locals := state.locals }
                have smallR : resumed.clock < state.clock := small
                exact evaluate_noRaiseProg good hgood continuation children.2 resumed stCode
              · rintro ⟨_, h⟩; cases h
            | exception _ _ => exact ih
            | _ => rintro ⟨_, h⟩; cases h
  | _ => simp [shape, noRaiseProg] at supported
termination_by (state.clock, sizeOf program)
decreasing_by
  all_goals
    simp_wf
    apply lex_of
    try subst shape
    try simp only [setVarHOLFinite, decClockHOLFinite, callEntryStateHOLFinite,
      ProgHOL.seq.sizeOf_spec, ProgHOL.ite.sizeOf_spec, ProgHOL.dec.sizeOf_spec,
      ProgHOL.while.sizeOf_spec, ProgHOL.decCall.sizeOf_spec, ProgHOL.call.sizeOf_spec, true_and]
    first
      | exact Or.inl smallR
      | exact Or.inl smaller
      | exact Or.inl small
      | omega
      | (rcases Nat.lt_or_eq_of_le mclock with h | h
         · exact Or.inl h
         · exact Or.inr ⟨h, by simp +arith⟩)
      | exact Or.inr ⟨rfl, by simp +arith⟩

def u256FromBeCallees (f : MlS) : Bool :=
  f == ofString "bswap64" || f == ofString "u256_from_be"

theorem u256FromBeCallees_good :
    ∀ function, u256FromBeCallees function = true → ∀ values body callee rs,
      PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup function values =
        some (body, callee, rs) →
      noRaiseProg u256FromBeCallees body = true := by
  intro function hfn values body callee rs hfound
  obtain ⟨params, rs', hinst⟩ := lookupCode_installed hfound
  simp only [u256FromBeCallees, Bool.or_eq_true, beq_iff_eq] at hfn
  rcases hfn with rfl | rfl
  · rw [lookup_bswap64] at hinst
    have heq := (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1
    rw [← heq]; rfl
  · rw [lookup_u256_from_be] at hinst
    have heq := (Prod.mk.inj (Prod.mk.inj (Option.some.inj hinst)).2).1
    rw [← heq]; rfl

theorem alloc_body_no_evmErr {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hcode : s.code = originalRuntimeCode) :
    ¬ IsEvmErr (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_alloc)).1 := by
  have hbody_eq : sourceFnBody Guest.Software.guestFn_alloc =
      .dec (ofString "p") .one (.var .global (ofString "heap_ptr"))
        (.seq
          (.ite (.cmp .lower (.op .sub [.const (BitVec.ofNat 64 2952790016), .var .local (ofString "p")])
              (.var .local (ofString "n")))
            (.call (some (none, none)) (ofString "trap_with") [.const 1])
            .skip)
          (.dec (ofString "q") .one
            (.op .and [.op .add [.var .local (ofString "p"), .var .local (ofString "n"), .const 7],
              .op .sub [.const 0, .const 8]])
            (.seq
              (.ite (.cmp .lower (.const (BitVec.ofNat 64 2952790016)) (.var .local (ofString "q")))
                (.call (some (none, none)) (ofString "trap_with") [.const 1])
                .skip)
              (.seq
                (.assign .global (ofString "heap_ptr") (.var .local (ofString "q")))
                (.return (.var .local (ofString "p"))))))) := rfl
  have htrap : ∀ (t : PanSemStateFiniteExact 64 F), t.code = originalRuntimeCode →
      let out := evaluateHOLFiniteState t (.call (some (none, none)) (ofString "trap_with") [.const 1])
      out.1 ≠ none ∧ ¬ IsEvmErr out.1 := by
    intro t htc; dsimp only
    rw [evaluateHOLFiniteState_call]
    rcases hargs : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) [.const 1] with _ | vals
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
                  rcases htr2 : evaluateHOLFiniteState s2 (.call (some (none, none)) (ofString "trap_with") [.const 1]) with ⟨r2, t2⟩
                  rw [htr2] at ht2
                  cases r2 with
                  | none => exact absurd rfl ht2.1
                  | some _ => exact ht2.2
              · rintro ⟨_, h⟩; cases h
            · rintro ⟨_, h⟩; cases h
        · have ht1 := htrap s1 hcode
          rcases htr1 : evaluateHOLFiniteState s1 (.call (some (none, none)) (ofString "trap_with") [.const 1]) with ⟨r1, t1⟩
          rw [htr1] at ht1
          cases r1 with
          | none => exact absurd rfl ht1.1
          | some _ => exact ht1.2
      · rintro ⟨_, h⟩; cases h
    · rintro ⟨_, h⟩; cases h

private theorem heapGap_disj_world_and_frames {F : Type}
    {s : PanSemStateFiniteExact 64 F} {S Nd : List Nat} {x : Ivl}
    (hA : ArenaOK s) (hWT : WorldTypedWith s S Nd)
    (hFW_all : ∀ ec ∈ evmChain s, FrameWF s S ec)
    (hx : Inside x (globN s "heap_ptr") heapLimit) :
    IvlsDisj [x] (worldTypedIvls s S Nd ++ ((evmChain s).map (frameObjects s)).flatten) := by
  intro y hy i hi
  simp only [List.mem_singleton] at hy; subst hy
  have hlim_ss : heapLimit = scratchStart := rfl
  have hfm : scratchStart ≤ globN s "frame_mem_ptr" := hA.2.2.1
  have hsp : globN s "frame_mem_ptr" ≤ globN s "scratch_ptr" := hA.2.2.2.1
  have hy1 : globN s "heap_ptr" ≤ y.1 := hx.1
  have hy2 : y.1 + y.2 ≤ heapLimit := hx.2
  have hdj_heap : ∀ j : Ivl, Inside j sourceBase (globN s "heap_ptr") → Disj y j := fun j hj =>
    Or.inr (Or.inr (Or.inr (by have hj2 := hj.2; omega)))
  have hdj_above : ∀ j : Ivl, scratchStart ≤ j.1 → Disj y j := fun j hj =>
    Or.inr (Or.inr (Or.inl (by omega)))
  rcases List.mem_append.1 hi with hwti | hfo
  · rcases worldTypedIvls_allocated hWT hwti with hz | hal
    · exact Or.inr (Or.inl hz)
    · rcases hal with hh | hsc
      · exact hdj_heap i hh
      · exact hdj_above i (by have hsc1 := hsc.1; omega)
  · obtain ⟨fo, hfo_map, hi_fo⟩ := List.mem_flatten.1 hfo
    obtain ⟨ec, hec, rfl⟩ := List.mem_map.1 hfo_map
    have hFW := hFW_all ec hec
    unfold frameObjects at hi_fo
    rcases List.mem_append.1 hi_fo with hhead7 | hlogobj
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hhead7
      rcases hhead7 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hdj_above _ (by have h : globN s "scratch_ptr" ≤ ec.1 := (hFW.1 (ec.1, 280) (by simp)).1.1; omega)
      · exact hdj_above _ (by have h : globN s "scratch_ptr" ≤ ec.2 := (hFW.1 (ec.2, 104) (by simp)).1.1; omega)
      · exact hdj_above _ (by have h : globN s "scratch_ptr" ≤ memW s (ec.1 + 8) := (hFW.1 (memW s (ec.1 + 8), 32 * memW s (ec.1 + 232)) (by simp)).1.1; omega)
      · exact hdj_above _ (by have h : scratchStart ≤ memW s (ec.1 + 24) := hFW.2.1.1; omega)
      · exact hdj_above _ (by have h : globN s "scratch_ptr" ≤ memW s (ec.1 + 88) := (hFW.1 (memW s (ec.1 + 88), 24) (by simp)).1.1; omega)
      · rcases hFW.2.2.2.2.2.2.2.2.2.2.2.2.1 with hh | hsc
        · exact hdj_heap _ hh
        · exact hdj_above _ (by have hsc1 : globN s "scratch_ptr" ≤ (frameLogs s ec).1 := hsc.1; omega)
      · rcases hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with ⟨hz, _⟩ | ⟨hh, _⟩
        · unfold frameRet; rw [if_pos hz]; exact Or.inr (Or.inl rfl)
        · exact hdj_heap _ hh
    · unfold frameLogObjects at hlogobj
      obtain ⟨idx, hidx_mem, hi_own⟩ := List.mem_flatMap.1 hlogobj
      have hidx : idx < memW s (memW s (ec.1 + 88) + 8) := List.mem_range.1 hidx_mem
      have hi_rec : i ∈ logRecordIvls s (memW s (memW s (memW s (ec.1 + 88)) + 8 * idx)) :=
        (List.mem_filter.1 hi_own).1
      rcases hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with hz | ⟨_, _, _, _, hent⟩
      · have he88_in : globN s "scratch_ptr" ≤ memW s (ec.1 + 88) := (hFW.1 (memW s (ec.1 + 88), 24) (by simp)).1.1
        have hss : 0 < scratchStart := by rw [R11Shards.scratchStart_val]; decide
        omega
      · obtain ⟨_, _, h_r0, _, _, h_r1, h_r2, h_r3⟩ := hent idx hidx
        unfold logRecordIvls at hi_rec
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi_rec
        rcases hi_rec with rfl | rfl | rfl | rfl
        · exact hdj_heap _ h_r0
        · exact hdj_heap _ h_r1
        · exact hdj_heap _ h_r2
        · exact hdj_heap _ h_r3

private theorem globals_update_twice_restore
    (g : HolFiniteMapExact MlS (ValueHOL 64)) (k : MlS) (v1 v2 : ValueHOL 64)
    (hk : g.lookup k = some v1) :
    (g.update (k, v2)).update (k, v1) = g := by
  apply HolFiniteMapExact.ext
  funext x
  by_cases hx : x = k
  · subst hx
    simp [HolFiniteMapExact.lookup_update, FUPDATE, hk]
  · have hkx : k ≠ x := Ne.symm hx
    simp [HolFiniteMapExact.lookup_update, FUPDATE, hx, hkx]

private theorem decCall_general_step {F : Type}
    (s0 t : PanSemStateFiniteExact 64 F) (nm fname : MlS) (sh : ShapeHOL)
    (args : List (ExpHOL 64)) (vals : List (ValueHOL 64)) (cont : ProgHOL 64)
    (hargs : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) args = some vals)
    (hnt : (evaluateHOLFiniteState t (.decCall nm sh fname args cont)).1 ≠ some .timeOut)
    (hbody : ∀ body cal rs,
      lookupCodeHOLFinite t.code.lookup fname vals = some (body, cal, rs) →
      t.clock ≠ 0 →
      (¬ IsEvmErr (evaluateHOLFiniteState (callEntryStateHOLFinite t cal) body).1) ∧
      (∀ val_ret sal,
        evaluateHOLFiniteState (callEntryStateHOLFinite t cal) body = (some (.returned val_ret), sal) →
        (shapeEqHOL (shapeOfHOLExact val_ret) sh && shapeEqHOL (shapeOfHOLExact val_ret) rs) = true →
        (evaluateHOLFiniteState (setVarHOLFinite nm val_ret { sal with locals := t.locals }) cont).1 ≠ some .timeOut →
        OpDispatchPost s0
          (evaluateHOLFiniteState (setVarHOLFinite nm val_ret { sal with locals := t.locals }) cont).1
          (evaluateHOLFiniteState (setVarHOLFinite nm val_ret { sal with locals := t.locals }) cont).2)) :
    OpDispatchPost s0
      (evaluateHOLFiniteState t (.decCall nm sh fname args cont)).1
      (evaluateHOLFiniteState t (.decCall nm sh fname args cont)).2 := by
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt ⊢
  rw [hargs] at hnt ⊢; dsimp only at hnt ⊢
  rcases hlk : lookupCodeHOLFinite t.code.lookup fname vals with _ | ⟨body, cal, rs⟩
  · exact opDispatchPost_error s0 _
  · rw [hlk] at hnt; dsimp only at hnt ⊢
    by_cases hclk : t.clock = 0
    · simp [hclk] at hnt
    · simp only [hclk, ↓reduceIte] at hnt ⊢
      obtain ⟨hne, hret⟩ := hbody body cal rs hlk hclk
      rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite t cal) body with ⟨ral, sal⟩
      simp only [hrun] at hnt hne ⊢
      cases ral with
      | none => exact opDispatchPost_error s0 _
      | some ral0 =>
        cases ral0 with
        | timeOut => simp at hnt
        | «break» | «continue» | error => exact opDispatchPost_error s0 _
        | finalFfi _ =>
          exact opDispatchPost_other (fun _ h => by cases h) (by rintro ⟨_, h⟩; cases h)
        | exception eid ev =>
          refine opDispatchPost_other (fun _ h => by cases h) ?_
          rintro ⟨v, h⟩; injection h with h'; injection h' with he hw
          exact hne ⟨v, by rw [he, hw]⟩
        | returned val_al =>
          dsimp only at hnt ⊢
          split
          · rename_i hsh_ok
            let resumed := setVarHOLFinite nm val_al { sal with locals := t.locals }
            have hnt_res : (evaluateHOLFiniteState resumed cont).1 ≠ some .timeOut := by
              intro hto
              rw [if_pos hsh_ok] at hnt
              exact hnt hto
            have hb := hret val_al sal hrun hsh_ok hnt_res
            exact opDispatchPost_congr_lc rfl rfl rfl hb
          · exact opDispatchPost_error s0 _

private theorem seq_step {F : Type}
    (s0 t : PanSemStateFiniteExact 64 F) (p1 p2 : ProgHOL 64)
    (hnt : (evaluateHOLFiniteState t (.seq p1 p2)).1 ≠ some .timeOut)
    (hp1 : (evaluateHOLFiniteState t p1).1 ≠ some .timeOut →
      ((evaluateHOLFiniteState t p1).1 = none →
        (evaluateHOLFiniteState (evaluateHOLFiniteState t p1).2 p2).1 ≠ some .timeOut →
        OpDispatchPost s0
          (evaluateHOLFiniteState (evaluateHOLFiniteState t p1).2 p2).1
          (evaluateHOLFiniteState (evaluateHOLFiniteState t p1).2 p2).2) ∧
      ((evaluateHOLFiniteState t p1).1 ≠ none →
        (∀ rv, (evaluateHOLFiniteState t p1).1 ≠ some (.returned rv)) ∧
        ¬ IsEvmErr (evaluateHOLFiniteState t p1).1)) :
    OpDispatchPost s0
      (evaluateHOLFiniteState t (.seq p1 p2)).1
      (evaluateHOLFiniteState t (.seq p1 p2)).2 := by
  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
  have hnt1 : (evaluateHOLFiniteState t p1).1 ≠ some .timeOut := by
    rintro hto
    rcases hr : evaluateHOLFiniteState t p1 with ⟨o, st'⟩
    simp only [hr] at hto hnt
    subst hto
    exact hnt rfl
  obtain ⟨hnone, hsome⟩ := hp1 hnt1
  rcases hr : evaluateHOLFiniteState t p1 with ⟨o, st'⟩
  simp only [hr] at hnt hnone hsome ⊢
  cases o with
  | none =>
    exact hnone rfl hnt
  | some r0 =>
    obtain ⟨hnr, hne⟩ := hsome (by simp)
    exact opDispatchPost_other hnr hne

private theorem heapGap_bre_to_evmStep {F : Type}
    {t t5 : PanSemStateFiniteExact 64 F} {markw : BitVec 64}
    (hInv : EvmInv t)
    (hmark_nat : markw.toNat = globN t "heap_ptr")
    (hmark_le : markw.toNat + 32 ≤ InitECandidate.Solver.HeapPotential.cMax.toNat)
    (hmark_8 : markw.toNat % 8 = 0)
    (heff : ByteRegionEffect t t5 [(markw.toNat, 32)]) :
    EvmInv t5 ∧ evmChain t5 = evmChain t ∧ evmR t5 = evmR t := by
  obtain ⟨hAt, S_t, hInvAt_t⟩ := hInv
  have hWt := hInvAt_t.1
  have hFW_all := hInvAt_t.2.2.2.2.1
  have hAT := hInvAt_t.2.2.2.2.2.2.2.2.2.1
  obtain ⟨Nd1, hTr1⟩ := hWt.2.2.2
  obtain ⟨Nd2, hTr2, hAT2⟩ := hAT
  obtain ⟨hTr_int, hne_int⟩ := R11Shards.triesTypedWith_inter hTr1 hTr2
  set Nd := Nd1.filter (fun n => decide (n ∈ Nd2))
  have hAT_Nd : ∀ o ∈ ((evmChain t).map (frameObjects t)).flatten, ∀ j ∈ nodeExtents t Nd, Disj o j :=
    fun o ho j hj => hAT2 o ho j (hne_int j hj).2
  have hx_in : Inside (markw.toNat, 32) (globN t "heap_ptr") heapLimit := by
    refine ⟨by dsimp only; omega, ?_⟩
    dsimp only
    have hcMax_val : InitECandidate.Solver.HeapPotential.cMax.toNat = 2952790016 := rfl
    have hhl_val : heapLimit = 2952790016 := rfl
    omega
  have hdj_t5 := heapGap_disj_world_and_frames hAt.2
    ⟨hWt.1, hWt.2.1, hWt.2.2.1, hTr_int⟩ hFW_all hx_in
  have hStep5 : EvmStep [] t t5 :=
    ByteRegionEffect.to_evmStep_nil_with hAt hInvAt_t hTr_int hAT_Nd hdj_t5 heff
  have hch_t5 : evmChain t5 = evmChain t := hStep5.2.2.2
  have hRl8_m : ∀ x ∈ ([(markw.toNat, 32)] : List Ivl), x.1 % 8 = 0 := by
    intro x hx; simp only [List.mem_singleton] at hx; subst hx; exact hmark_8
  have hR_t5 : evmR t5 = evmR t := by
    refine evmR_eq_of_chain_and_words hch_t5 (fun ec hec => ?_)
    have hFW_ec := hFW_all ec hec
    have hb1 := (frameWF_bounds hAt.2 hFW_ec).1
    have he1_8 : ec.1 % 8 = 0 := (hFW_ec.1 (ec.1, 280) (by simp)).2.1
    have hdj_ec : ∀ x ∈ ([(markw.toNat, 32)] : List Ivl), Disj x (ec.1, 280) := by
      intro x hx
      apply hdj_t5 x hx (ec.1, 280)
      apply List.mem_append_right
      exact List.mem_flatten.2 ⟨frameObjects t ec, List.mem_map.2 ⟨ec, hec, rfl⟩, by simp [frameObjects]⟩
    exact ⟨memW_eq_of_disj_eff heff hRl8_m hb1 he1_8 (by omega) (by omega) hdj_ec,
           memW_eq_of_disj_eff heff hRl8_m hb1 he1_8 (by omega) (by omega) hdj_ec⟩
  exact ⟨hStep5.1, hch_t5, hR_t5⟩

theorem op_calldataload_spec : OpHandlerSpec (ofString "op_calldataload") := by
  refine opHandlerSpec_of_run 536 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_calldataload rfl ?_
  intro F s0 _
  dsimp only [Guest.Software.guestFn_op_calldataload, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine HandlerRun.decCall_simple eps_stack_pop ?_
  refine HandlerRun.seq_charge_gas_const (by decide) ?_
  refine HandlerRun.dec_simple ?_
  refine HandlerRun.decCall_simple eps_sat_word ?_
  -- Remaining program at charged = true:
  -- decCall "mark" .one "heap_mark" []
  --   (decCall "tmp" .one "alloc" [32]
  --     (seq (call "buffer_read" [...])
  --       (decCall "v" (comb [1,1,1,1]) "u256_from_be" [tmp, 32]
  --         (seq (call "heap_release" [mark])
  --           (seq (call "stack_push" [v])
  --             (seq (call "pc_add" [1]) (return 0)))))))
  intro t hc hInv hlen hR _ hnt
  simp only [↓reduceIte] at hR
  -- Extract heap_ptr word `markw` from `ArenaOK t` (`GlobalsWord t`)
  have hhp_mem : "heap_ptr" ∈ guestGlobalNames := by decide
  obtain ⟨markw, hmark_gw⟩ := hInv.1.2.2.2.2.2.2.2.2.2 "heap_ptr" hhp_mem
  have hmark_lk : t.globals.lookup (ofString "heap_ptr") = some (.val (.word markw)) := hmark_gw
  have hmark_nat : markw.toNat = globN t "heap_ptr" := by simp [globN, hmark_lk]
  have hmark_le : markw.toNat ≤ InitECandidate.Solver.HeapPotential.cMax.toNat := by
    have h1 := hInv.1.2.2.1
    rw [hmark_nat]; exact h1
  have hmark_8 : markw.toNat % 8 = 0 := by
    rw [hmark_nat]; exact hInv.1.2.2.2.2.2.2.1
  -- Step 1: `decCall "mark" .one "heap_mark" []`
  have hargs_hm : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) [] = some [] := rfl
  have hlook_hm := pan_zero_arg_lookup t.code.lookup (ofString "heap_mark")
    (sourceFnBody Guest.Software.guestFn_heap_mark) .one (by rw [hc]; exact lookup_heap_mark)
  refine decCall_general_step s0 t (ofString "mark") (ofString "heap_mark") .one [] [] _ hargs_hm hnt ?_
  clear hnt
  intro body_hm cal_hm rs_hm hlk_hm hclk_t
  have hEq_hm := Option.some.inj (hlk_hm.symm.trans hlook_hm)
  obtain ⟨rfl, hEq_hm2⟩ := Prod.mk.inj hEq_hm
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq_hm2
  have hhm_body : evaluateHOLFiniteState (callEntryStateHOLFinite t HolFiniteMapExact.empty)
      (sourceFnBody Guest.Software.guestFn_heap_mark) =
      (some (.returned (.val (.word markw))),
       emptyLocalsHOLFinite (callEntryStateHOLFinite t HolFiniteMapExact.empty)) := by
    dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_heap_mark,
      InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
      InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural]
    rw [evaluateHOLFiniteState_return]
    have hev_hp : @evalHOLExact 64 F _ (callEntryStateHOLFinite t HolFiniteMapExact.empty).toExact
        (fun a => Classical.propDecidable ((callEntryStateHOLFinite t HolFiniteMapExact.empty).memaddrs a))
        (.var .global (ofString "heap_ptr")) = some (.val (.word markw)) := hmark_lk
    rw [hev_hp]; dsimp only
    have hsz : sizeOfShapeWithContextHOL (callEntryStateHOLFinite t HolFiniteMapExact.empty).structs
        (shapeOfHOLExact (.val (.word markw) : ValueHOL 64)) ≤ 32 := by
      simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
    rw [if_pos hsz]
  have hne_hm : ¬ IsEvmErr (evaluateHOLFiniteState (callEntryStateHOLFinite t HolFiniteMapExact.empty)
      (sourceFnBody Guest.Software.guestFn_heap_mark)).1 := by
    rw [hhm_body]; rintro ⟨_, h⟩; cases h
  refine ⟨hne_hm, ?_⟩
  intro val_hm shm hrun_hm _ hnt
  have hEq_ret := Prod.mk.inj (hrun_hm.symm.trans hhm_body)
  have hval_hm : val_hm = .val (.word markw) := by injection hEq_ret.1 with h'; injection h'
  subst hval_hm
  rcases hEq_ret with ⟨_, rfl⟩
  set t1 := setVarHOLFinite (ofString "mark") (.val (.word markw))
    { emptyLocalsHOLFinite (callEntryStateHOLFinite t HolFiniteMapExact.empty) with locals := t.locals }
  -- Step 2: `decCall "tmp" .one "alloc" [.const 32]` on `t1`
  have hargs_al : evalListHOLFinite t1 (h := fun a => Classical.propDecidable (t1.memaddrs a)) [.const (32#64)] =
      some [.val (.word (32#64))] := rfl
  have hlook_al := pan_one_word_lookup t1.code.lookup (ofString "alloc") (ofString "n")
    (sourceFnBody Guest.Software.guestFn_alloc) (32#64) (by change t.code.lookup _ = _; rw [hc]; exact lookup_alloc)
  refine decCall_general_step s0 t1 (ofString "tmp") (ofString "alloc") .one
    [.const (32#64)] [.val (.word (32#64))] _ hargs_al hnt ?_
  clear hnt
  intro body_al cal_al rs_al hlk_al hclk_t1
  have hEq_al := Option.some.inj (hlk_al.symm.trans hlook_al)
  obtain ⟨rfl, hEq_al2⟩ := Prod.mk.inj hEq_al
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq_al2
  refine ⟨alloc_body_no_evmErr _ hc, ?_⟩
  intro val_al sal hrun_al _ hnt
  let cal_al := HolFiniteMapExact.empty.update (ofString "n", ValueHOL.val (.word (32#64)))
  let ent_al := callEntryStateHOLFinite t1 cal_al
  have hal_gen := M13.evaluate_alloc_body_general ent_al markw (32#64) hc hmark_le hmark_lk
    (by simp [ent_al, cal_al, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
  have hal_meta := PanRunBounded.evaluateHOLFiniteState_metadata ent_al (sourceFnBody Guest.Software.guestFn_alloc)
  have hal_ba := evaluate_baseAddr ent_al (sourceFnBody Guest.Software.guestFn_alloc)
  have hrun_al' : evaluateHOLFiniteState ent_al (sourceFnBody Guest.Software.guestFn_alloc) = (some (.returned val_al), sal) := hrun_al
  rw [hrun_al'] at hal_gen hal_meta hal_ba
  dsimp only at hal_gen hal_meta hal_ba
  obtain ⟨rfl, hsal_glob, hsal_mem, hbnd32, hq_le, _⟩ := hal_gen val_al rfl
  let q : BitVec 64 := (markw + ((32#64) + 7)) &&& ((0 : BitVec 64) - 8)
  set t2 := setVarHOLFinite (ofString "tmp") (.val (.word markw)) { sal with locals := t1.locals }
  have ht2_code : t2.code = originalRuntimeCode := hal_meta.1.trans hc
  have ht2_ma : t2.memaddrs = ordinaryDomain := hal_meta.2.1.trans hInv.1.1.memaddrs
  have ht2_be : t2.be = t.be := hal_meta.2.2.1
  have ht2_sh : t2.shMemaddrs = t.shMemaddrs := hal_meta.2.2.2.1
  have ht2_ba : t2.baseAddr = t.baseAddr := hal_ba
  have ht2_glob : t2.globals = t.globals.update (ofString "heap_ptr", .val (.word q)) := hsal_glob
  have ht2_mem : t2.memory = t.memory := hsal_mem
  have ht2_tmp : t2.locals.lookup (ofString "tmp") = some (.val (.word markw)) := by
    simp [t2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have ht2_mark : t2.locals.lookup (ofString "mark") = some (.val (.word markw)) := by
    have hne : ofString "tmp" ≠ ofString "mark" := by decide
    simp [t2, t1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne]
  -- Step 3: `seq (call "buffer_read" [bExp, blExp, sExp, 32, tmp]) ...`
  let bExp : ExpHOL 64 := .load .one (.op .add [.var .local (ofString "msg"), .const (88#64)])
  let blExp : ExpHOL 64 := .load .one (.op .add [.var .local (ofString "msg"), .const (96#64)])
  let sExp : ExpHOL 64 := .var .local (ofString "s")
  refine seq_step s0 t2 _ _ hnt ?_
  clear hnt
  intro hnt_br
  by_cases hargs_br_ok :
      (∃ bw : BitVec 64, @evalHOLExact 64 F _ t2.toExact (fun a => Classical.propDecidable (t2.memaddrs a)) bExp = some (.val (.word bw))) ∧
      (∃ blw : BitVec 64, @evalHOLExact 64 F _ t2.toExact (fun a => Classical.propDecidable (t2.memaddrs a)) blExp = some (.val (.word blw))) ∧
      (∃ sw : BitVec 64, @evalHOLExact 64 F _ t2.toExact (fun a => Classical.propDecidable (t2.memaddrs a)) sExp = some (.val (.word sw)))
  · obtain ⟨⟨bw, hbw⟩, ⟨blw, hblw⟩, ⟨sw, hsw⟩⟩ := hargs_br_ok
    have hbnd_m32 : markw.toNat + (32#64).toNat < 2 ^ 64 := by
      have hcMax_val : InitECandidate.Solver.HeapPotential.cMax.toNat = 2952790016 := rfl
      have h32 : (32#64).toNat = 32 := rfl
      omega
    have hbr := eval_call_buffer_read_bre t2 bExp blExp sExp (.const (32#64)) (.var .local (ofString "tmp"))
      bw blw sw (32#64) markw [(markw.toNat, 32)] ht2_code ht2_ma hbw hblw hsw rfl ht2_tmp hbnd_m32
      (fun _ => ⟨(markw.toNat, 32), List.mem_singleton.2 rfl, le_refl _, le_refl _⟩)
      hnt_br
    refine ⟨?_, fun hne => hbr.2 hne⟩
    intro hnone hnt
    obtain ⟨heff_br, ht3_loc⟩ := hbr.1 hnone
    set t3 := (evaluateHOLFiniteState t2
      (.call (some (none, none)) (ofString "buffer_read")
        [bExp, blExp, sExp, .const (32#64), .var .local (ofString "tmp")])).2
    have ht3_code : t3.code = originalRuntimeCode := heff_br.code.trans ht2_code
    have ht3_tmp : t3.locals.lookup (ofString "tmp") = some (.val (.word markw)) := by
      rw [ht3_loc]; exact ht2_tmp
    have ht3_mark : t3.locals.lookup (ofString "mark") = some (.val (.word markw)) := by
      rw [ht3_loc]; exact ht2_mark
    -- Step 4: `decCall "v" (comb [1,1,1,1]) "u256_from_be" [tmp, 32]` on `t3`
    have hargs_ub : evalListHOLFinite t3 (h := fun a => Classical.propDecidable (t3.memaddrs a))
        [.var .local (ofString "tmp"), .const (32#64)] =
        some [.val (.word markw), .val (.word (32#64))] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, ht3_tmp]
    refine decCall_general_step s0 t3 (ofString "v") (ofString "u256_from_be") _
      [.var .local (ofString "tmp"), .const (32#64)]
      [.val (.word markw), .val (.word (32#64))] _ hargs_ub hnt ?_
    clear hnt
    intro body_ub cal_ub rs_ub hlk_ub hclk_t3
    have hlk_ub_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "u256_from_be")
        [.val (.word markw), .val (.word (32#64))] = some (body_ub, cal_ub, rs_ub) := by
      rwa [← ht3_code]
    have hro_ub : readOnlyProg opRoCallees body_ub = true :=
      installed_body_readOnly 86 (by rw [guestAst_len]; decide)
        Guest.Software.guestFn_u256_from_be rfl opRoCallees rfl hlk_ub_orig
    have hnr_ub : noRaiseProg u256FromBeCallees body_ub = true :=
      u256FromBeCallees_good (ofString "u256_from_be") (by decide)
        [.val (.word markw), .val (.word (32#64))] body_ub cal_ub rs_ub hlk_ub_orig
    have hub_no_evm : ¬ IsEvmErr (evaluateHOLFiniteState (callEntryStateHOLFinite t3 cal_ub) body_ub).1 :=
      evaluate_noRaiseProg u256FromBeCallees u256FromBeCallees_good body_ub hnr_ub
        (callEntryStateHOLFinite t3 cal_ub) ht3_code
    refine ⟨hub_no_evm, ?_⟩
    intro v_ub sub hrun_ub hsh_ub hnt
    have hub_safe := evaluate_readOnlyProg opRoCallees opRoCallees_good body_ub hro_ub
      (callEntryStateHOLFinite t3 cal_ub) ht3_code
    rw [hrun_ub] at hub_safe
    have hlf_ub : LocFrame (callEntryStateHOLFinite t3 cal_ub) sub :=
      SafeOrTrapped.to_resumes hub_safe (Or.inl ⟨v_ub, rfl⟩)
    set t4 := setVarHOLFinite (ofString "v") v_ub { sub with locals := t3.locals }
    have ht4_lf : LocFrame t3 t4 := by
      unfold LocFrame at hlf_ub ⊢
      simp only [t4, setVarHOLFinite]
      rw [hlf_ub]; cases t3; rfl
    have ht4_code : t4.code = originalRuntimeCode := by
      rw [ht4_lf]; exact ht3_code
    have ht4_mark : t4.locals.lookup (ofString "mark") = some (.val (.word markw)) := by
      have hne : ofString "v" ≠ ofString "mark" := by decide
      simp [t4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne, ht3_mark]
    -- Step 5: `seq (call "heap_release" [mark]) (seq (call "stack_push" [v]) (seq (call "pc_add" [1]) (return 0)))`
    refine seq_step s0 t4 _ _ hnt ?_
    clear hnt
    intro hnt_hr
    rw [evaluateHOLFiniteState_call] at hnt_hr ⊢
    have hargs_hr : evalListHOLFinite t4
        (h := fun a => Classical.propDecidable (t4.memaddrs a))
        [.var .local (ofString "mark")] = some [.val (.word markw)] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, ht4_mark]
    have hlook_hr := pan_one_word_lookup t4.code.lookup (ofString "heap_release")
      (ofString "m") (sourceFnBody Guest.Software.guestFn_heap_release) markw
      (by rw [ht4_code]; exact lookup_heap_release)
    rw [hargs_hr] at hnt_hr ⊢; dsimp only at hnt_hr ⊢
    rw [hlook_hr] at hnt_hr ⊢; dsimp only at hnt_hr ⊢
    by_cases hclk_t4 : t4.clock = 0
    · simp [hclk_t4] at hnt_hr
    · simp only [hclk_t4, ↓reduceIte] at hnt_hr ⊢
      let cal_hr := HolFiniteMapExact.empty.update (ofString "m", ValueHOL.val (.word markw))
      let ent_hr := callEntryStateHOLFinite t4 cal_hr
      have hhr_body : evaluateHOLFiniteState ent_hr
          (sourceFnBody Guest.Software.guestFn_heap_release) =
          (some (.returned (.val (.word 0))),
           emptyLocalsHOLFinite (setKvarHOLFinite .global (ofString "heap_ptr") (.val (.word markw)) ent_hr)) := by
        dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_heap_release,
          InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
          InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
          InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
          InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural]
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
        have hm_loc : ent_hr.locals.lookup (ofString "m") = some (.val (.word markw)) := by
          simp [ent_hr, cal_hr, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have hlk_hp4 : ent_hr.globals.lookup (ofString "heap_ptr") = some (.val (.word q)) := by
          have hg4 : ent_hr.globals = t2.globals := by
            change t4.globals = t2.globals
            rw [ht4_lf, heff_br.globals]
          rw [hg4, ht2_glob]
          simp [HolFiniteMapExact.lookup_update, FUPDATE]
        simp [evalHOLExact, hm_loc, isValidValueHOLFinite, isValidValueHOLExact,
          lookupKvarHOLFinite, lookupKvarHOLExact, hlk_hp4,
          shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite,
          evaluateHOLFiniteState_return, sizeOfShapeWithContextHOL]
      rw [hhr_body]; dsimp only
      have hsh0_one : shapeEqHOL (shapeOfHOLExact (.val (.word (0 : BitVec 64)) : ValueHOL 64)) .one = true := by
        simp [shapeOfHOLExact, shapeEqHOL]
      rw [if_pos hsh0_one]; dsimp only
      refine ⟨?_, fun hne => absurd rfl hne⟩
      intro _ hnt
      set t5 : PanSemStateFiniteExact 64 F :=
        { emptyLocalsHOLFinite (setKvarHOLFinite .global (ofString "heap_ptr") (.val (.word markw)) ent_hr) with
          locals := t4.locals }
      have ht5_glob : t5.globals = t.globals := by
        have hg4 : ent_hr.globals = t2.globals := by
          change t4.globals = t2.globals
          rw [ht4_lf, heff_br.globals]
        change ent_hr.globals.update (ofString "heap_ptr", .val (.word markw)) = t.globals
        rw [hg4, ht2_glob]
        exact globals_update_twice_restore t.globals (ofString "heap_ptr")
          (.val (.word markw)) (.val (.word q)) hmark_lk
      have ht5_code : t5.code = originalRuntimeCode := ht4_code
      have ht4_mem : t4.memory = t3.memory := by rw [ht4_lf]
      have ht5_mem : t5.memory = t3.memory := ht4_mem
      have heff_t_t5 : ByteRegionEffect t t5 [(markw.toNat, 32)] := by
        refine ⟨ht5_code.trans hc.symm, ?_, ?_, ?_, ?_, ht5_glob, ?_, ?_, ?_⟩
        · change t4.memaddrs = t.memaddrs
          rw [ht4_lf, heff_br.memaddrs, ht2_ma, hInv.1.1.memaddrs]
        · change t4.shMemaddrs = t.shMemaddrs
          rw [ht4_lf, heff_br.shMemaddrs, ht2_sh]
        · change t4.baseAddr = t.baseAddr
          rw [ht4_lf, heff_br.baseAddr, ht2_ba]
        · change t4.be = t.be
          rw [ht4_lf, heff_br.be, ht2_be]
        · intro a hna
          rw [ht5_mem]
          have hna2 : ¬ t2.memaddrs a := by
            rw [ht2_ma, ← hInv.1.1.memaddrs]; exact hna
          rw [heff_br.out_dom a hna2, ht2_mem]
        · intro a ha
          rw [ht5_mem, heff_br.cell_frame a ha, ht2_mem]
        · intro b hb hno
          have hbe5 : t5.be = t.be := by
            change t4.be = t.be; rw [ht4_lf, heff_br.be, ht2_be]
          have hbe53 : t5.be = t3.be := by
            change t4.be = t3.be; rw [ht4_lf]
          have hmb5 : memB t5 b = memB t3 b := by
            unfold memB; rw [ht5_mem, hbe53]
          have hmb2 : memB t2 b = memB t b := by
            unfold memB; rw [ht2_mem, ht2_be]
          rw [hmb5, heff_br.byte_frame b hb hno, hmb2]
      have hmark32_le : markw.toNat + 32 ≤ InitECandidate.Solver.HeapPotential.cMax.toNat := by
        have h32 : (32#64 : BitVec 64).toNat = 32 := rfl
        omega
      obtain ⟨hInv_t5, hch_t5, hR_t5⟩ :=
        heapGap_bre_to_evmStep hInv hmark_nat hmark32_le hmark_8 heff_t_t5
      have hlen_t5 : (evmChain t5).length = (evmChain s0).length := by
        rw [hch_t5]; exact hlen
      have hR_lt_t5 : if true then evmR t5 < evmR s0 else evmR t5 ≤ evmR s0 := by
        simp only [↓reduceIte, hR_t5]; exact hR
      -- Step 6: Finish tail `seq (call "stack_push" [v]) (seq (call "pc_add" [1]) (return 0))` via `HandlerRun`!
      have htail : HandlerRun s0 (fun _ => True) true
          (.seq (.call (some (none, none)) (ofString "stack_push") [.var .local (ofString "v")])
            (.seq (.call (some (none, none)) (ofString "pc_add") [.const (1#64)])
              (.return (.const (0#64))))) :=
        HandlerRun.seq_call_simple eps_stack_push
          (HandlerRun.seq_call_simple eps_pc_add (HandlerRun.ret _))
      exact htail t5 ht5_code hInv_t5 hlen_t5 hR_lt_t5 trivial hnt
  · -- If any argument of `buffer_read` fails to evaluate to a single word:
    rw [evaluateHOLFiniteState_call]
    rcases hargs_br : evalListHOLFinite t2
        (h := fun a => Classical.propDecidable (t2.memaddrs a))
        [bExp, blExp, sExp, .const (32#64), .var .local (ofString "tmp")] with _ | vals_br
    · dsimp only
      refine ⟨(fun h => by cases h), fun _ => ⟨(fun _ h => by cases h), ?_⟩⟩
      rintro ⟨v, h⟩
      cases h
    · dsimp only
      rcases hlk_br : lookupCodeHOLFinite t2.code.lookup (ofString "buffer_read") vals_br with
        _ | ⟨body_br, cal_br, rs_br⟩
      · dsimp only
        refine ⟨(fun h => by cases h), fun _ => ⟨(fun _ h => by cases h), ?_⟩⟩
        rintro ⟨v, h⟩
        cases h
      · exfalso
        apply hargs_br_ok
        have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
          t2.code.lookup (ofString "buffer_read") vals_br body_br cal_br rs_br hlk_br
        rw [ht2_code] at hx
        simp only [Flapjack.lookupCodeHOLExact, lookup_buffer_read] at hx
        split at hx
        · rename_i hcond
          have hlen5 : vals_br.length = 5 := by
            have hl := hcond.2.1
            simpa using hl.symm
          rcases vals_br with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | ⟨v4, _ | ⟨v5, _ | _⟩⟩⟩⟩⟩
          all_goals try (simp at hlen5)
          have hsh123 : shapeEqHOL .one (shapeOfHOLExact v1) = true ∧
              shapeEqHOL .one (shapeOfHOLExact v2) = true ∧
              shapeEqHOL .one (shapeOfHOLExact v3) = true := by
            have hs := hcond.2.2
            simp only [List.map, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
              List.zip_cons_cons, List.zip_nil_right] at hs
            exact ⟨hs.1, hs.2.1, hs.2.2.1⟩
          have hw_of_one : ∀ u : ValueHOL 64, shapeEqHOL .one (shapeOfHOLExact u) = true →
              ∃ w : BitVec 64, u = .val (.word w) := by
            intro u hu
            rcases u with ⟨⟨w⟩⟩ | _ | _
            · exact ⟨w, rfl⟩
            · simp [shapeOfHOLExact, shapeEqHOL] at hu
            · simp [shapeOfHOLExact, shapeEqHOL] at hu
          obtain ⟨bw, rfl⟩ := hw_of_one v1 hsh123.1
          obtain ⟨blw, rfl⟩ := hw_of_one v2 hsh123.2.1
          obtain ⟨sw, rfl⟩ := hw_of_one v3 hsh123.2.2
          change @evalListHOLExact 64 F _ t2.toExact (fun a => Classical.propDecidable (t2.memaddrs a))
            [bExp, blExp, sExp, .const (32#64), .var .local (ofString "tmp")] =
            some [.val (.word bw), .val (.word blw), .val (.word sw), v4, v5] at hargs_br
          have hb4 : @evalHOLExact 64 F _ t2.toExact (fun a => Classical.propDecidable (t2.memaddrs a))
              (.const (32#64)) = some (.val (.word (32#64))) := rfl
          have hb5 : @evalHOLExact 64 F _ t2.toExact (fun a => Classical.propDecidable (t2.memaddrs a))
              (.var .local (ofString "tmp")) = some (.val (.word markw)) := by
            simp [evalHOLExact, ht2_tmp]
          rcases hb1 : @evalHOLExact 64 F _ t2.toExact (fun a => Classical.propDecidable (t2.memaddrs a)) bExp with _ | u1
          · simp [evalListHOLExact, hb1] at hargs_br
          · rcases hb2 : @evalHOLExact 64 F _ t2.toExact (fun a => Classical.propDecidable (t2.memaddrs a)) blExp with _ | u2
            · simp [evalListHOLExact, hb1, hb2] at hargs_br
            · rcases hb3 : @evalHOLExact 64 F _ t2.toExact (fun a => Classical.propDecidable (t2.memaddrs a)) sExp with _ | u3
              · simp [evalListHOLExact, hb1, hb2, hb3] at hargs_br
              · simp [evalListHOLExact, hb1, hb2, hb3, hb4, hb5] at hargs_br
                obtain ⟨rfl, rfl, rfl, _⟩ := hargs_br
                exact ⟨⟨bw, rfl⟩, ⟨blw, rfl⟩, ⟨sw, rfl⟩⟩
        · cases hx

end InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers
