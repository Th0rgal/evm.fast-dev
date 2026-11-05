import InitECandidate.Solver.Wave8GuestInv.Deliveries.M11.RlpMemcpyLemmas
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M13.StoreAllocHelpers
import InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.Common
import InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.ReadOnly
import InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.StackPush

/-! # Memory Expansion, `buffer_read`, `memzero`, and Heap-Gap Helpers (`OpHandlers-B`) -/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB

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
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers
open InitECandidate.Solver.Wave8Contracts.M23

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
  | .store _ _ | .storeByte _ _ => true
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
  | store dst val =>
    rw [evaluateHOLFiniteState_store]
    split
    · split
      · split
        · rintro ⟨_, h⟩; cases h
        · rintro ⟨_, h⟩; cases h
      · rintro ⟨_, h⟩; cases h
    · rintro ⟨_, h⟩; cases h
  | storeByte dst val =>
    rw [evaluateHOLFiniteState_storeByte]
    split
    · split
      · split
        · rintro ⟨_, h⟩; cases h
        · rintro ⟨_, h⟩; cases h
      · rintro ⟨_, h⟩; cases h
    · rintro ⟨_, h⟩; cases h
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

theorem globals_update_twice_restore
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

theorem decCall_general_step {F : Type}
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

theorem seq_step {F : Type}
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


/-! ## 7. `frame_mem_alloc`, `FrameMemByteEff`, and `evmInv_of_head_mem_extend` -/

theorem lookup_frame_mem_alloc :
    originalRuntimeCode.lookup (ofString "frame_mem_alloc") =
      some ([(ofString "n", .one)], sourceFnBody Guest.Software.guestFn_frame_mem_alloc, .one) :=
  lookup_of_guestAst_getElem 10 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_frame_mem_alloc) rfl

theorem frame_mem_alloc_body_no_evmErr {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hcode : s.code = originalRuntimeCode) :
    ¬ IsEvmErr (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_frame_mem_alloc)).1 := by
  have hbody_eq : sourceFnBody Guest.Software.guestFn_frame_mem_alloc =
      .dec (ofString "p") .one (.var .global (ofString "frame_mem_ptr"))
        (.seq
          (.ite (.cmp .lower (.op .sub [.var .global (ofString "scratch_ptr"), .var .local (ofString "p")])
              (.var .local (ofString "n")))
            (.call (some (none, none)) (ofString "trap_with") [.const 6])
            .skip)
          (.dec (ofString "q") .one
            (.op .and [.op .add [.var .local (ofString "p"), .var .local (ofString "n"), .const 7],
              .op .sub [.const 0, .const 8]])
            (.seq
              (.ite (.cmp .lower (.var .global (ofString "scratch_ptr")) (.var .local (ofString "q")))
                (.call (some (none, none)) (ofString "trap_with") [.const 6])
                .skip)
              (.seq
                (.assign .global (ofString "frame_mem_ptr") (.var .local (ofString "q")))
                (.return (.var .local (ofString "p"))))))) := rfl
  have htrap : ∀ (t : PanSemStateFiniteExact 64 F), t.code = originalRuntimeCode →
      let out := evaluateHOLFiniteState t (.call (some (none, none)) (ofString "trap_with") [.const 6])
      out.1 ≠ none ∧ ¬ IsEvmErr out.1 := by
    intro t htc; dsimp only
    rw [evaluateHOLFiniteState_call]
    rcases hargs : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) [.const 6] with _ | vals
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
                  rcases htr2 : evaluateHOLFiniteState s2 (.call (some (none, none)) (ofString "trap_with") [.const 6]) with ⟨r2, t2⟩
                  rw [htr2] at ht2
                  cases r2 with
                  | none => exact absurd rfl ht2.1
                  | some _ => exact ht2.2
              · rintro ⟨_, h⟩; cases h
            · rintro ⟨_, h⟩; cases h
        · have ht1 := htrap s1 hcode
          rcases htr1 : evaluateHOLFiniteState s1 (.call (some (none, none)) (ofString "trap_with") [.const 6]) with ⟨r1, t1⟩
          rw [htr1] at ht1
          cases r1 with
          | none => exact absurd rfl ht1.1
          | some _ => exact ht1.2
      · rintro ⟨_, h⟩; cases h
    · rintro ⟨_, h⟩; cases h

theorem frame_mem_alloc_body_run {F : Type}
    (state : PanSemStateFiniteExact 64 F) (p sp n : BitVec 64)
    (hcode : state.code = originalRuntimeCode)
    (hp_lookup : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word p)))
    (hsp_lookup : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word sp)))
    (hn : state.locals.lookup (ofString "n") = some (.val (.word n))) :
    let out := evaluateHOLFiniteState state (sourceFnBody Guest.Software.guestFn_frame_mem_alloc)
    let q := (p + (n + 7)) &&& ((0 : BitVec 64) - 8)
    ∀ retVal : ValueHOL 64, out.1 = some (.returned retVal) →
      retVal = .val (.word p) ∧ ¬ ((sp - p).toNat < n.toNat) ∧ ¬ (sp.toNat < q.toNat) ∧
      out.2 = { state with
        globals := (state.globals.update (ofString "frame_mem_ptr", .val (.word q)))
        locals := out.2.locals
        clock := out.2.clock } := by
  dsimp only
  have hbody_eq : sourceFnBody Guest.Software.guestFn_frame_mem_alloc =
      .dec (ofString "p") .one (.var .global (ofString "frame_mem_ptr"))
        (.seq
          (.ite (.cmp .lower (.op .sub [.var .global (ofString "scratch_ptr"), .var .local (ofString "p")])
              (.var .local (ofString "n")))
            (.call (some (none, none)) (ofString "trap_with") [.const 6])
            .skip)
          (.dec (ofString "q") .one
            (.op .and [.op .add [.var .local (ofString "p"), .var .local (ofString "n"), .const 7],
              .op .sub [.const 0, .const 8]])
            (.seq
              (.ite (.cmp .lower (.var .global (ofString "scratch_ptr")) (.var .local (ofString "q")))
                (.call (some (none, none)) (ofString "trap_with") [.const 6])
                .skip)
              (.seq
                (.assign .global (ofString "frame_mem_ptr") (.var .local (ofString "q")))
                (.return (.var .local (ofString "p"))))))) := rfl
  rw [hbody_eq, evaluateHOLFiniteState_dec_total]
  have hp_eval : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a))
      (.var .global (ofString "frame_mem_ptr")) = some (.val (.word p)) := hp_lookup
  dsimp only
  rw [hp_eval]
  have hsh_p : shapeEqHOL .one (shapeOfHOLExact (.val (.word p))) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  dsimp only
  rw [if_pos hsh_p]
  dsimp only
  let pState := setVarHOLFinite (ofString "p") (.val (.word p)) state
  have hp_loc : pState.locals.lookup (ofString "p") = some (.val (.word p)) := by
    simp [pState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hn_loc : pState.locals.lookup (ofString "n") = some (.val (.word n)) := by
    simp [pState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn,
      show ofString "p" ≠ ofString "n" by decide]
  have hsp_p : pState.globals.lookup (ofString "scratch_ptr") = some (.val (.word sp)) := hsp_lookup
  have hcode_p : pState.code = originalRuntimeCode := hcode
  rw [evaluateHOLFiniteState_seq_line780]
  have hev1 : @evalHOLExact 64 F _ pState.toExact
      (fun a => Classical.propDecidable (pState.memaddrs a))
      (.cmp .lower (.op .sub [.var .global (ofString "scratch_ptr"), .var .local (ofString "p")])
        (.var .local (ofString "n"))) =
      some (.val (.word (if (sp - p).toNat < n.toNat then 1 else 0))) := by
    simp only [evalHOLExact, evalListHOLExact, hsp_p, hp_loc, hn_loc,
      Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, decide_eq_true_eq]
    rfl
  by_cases hcmp1 : (sp - p).toNat < n.toNat
  · have hite1 : evaluateHOLFiniteState pState
        (.ite (.cmp .lower (.op .sub [.var .global (ofString "scratch_ptr"), .var .local (ofString "p")])
            (.var .local (ofString "n")))
          (.call (some (none, none)) (ofString "trap_with") [.const 6])
          .skip) =
        evaluateHOLFiniteState pState (.call (some (none, none)) (ofString "trap_with") [.const 6]) := by
      rw [evaluateHOLFiniteState_ite, hev1, if_pos hcmp1]; simp
    rw [hite1]
    have hno_none := evaluate_call_trap_with_no_none pState 6 hcode_p
    have hno_ret := fun w => evaluate_call_trap_with_no_return pState 6 w hcode_p
    rcases htr : evaluateHOLFiniteState pState (.call (some (none, none)) (ofString "trap_with") [.const 6]) with ⟨r1, s1⟩
    rw [htr] at hno_none hno_ret
    cases r1 with
    | none => exact absurd rfl hno_none
    | some r1' =>
      intro retVal hret
      exact False.elim (hno_ret retVal hret)
  · have hite1 : evaluateHOLFiniteState pState
        (.ite (.cmp .lower (.op .sub [.var .global (ofString "scratch_ptr"), .var .local (ofString "p")])
            (.var .local (ofString "n")))
          (.call (some (none, none)) (ofString "trap_with") [.const 6])
          .skip) = (none, pState) := by
      rw [evaluateHOLFiniteState_ite, hev1, if_neg hcmp1]; simp [evaluateHOLFiniteState_skip]
    rw [hite1]
    dsimp only
    rw [evaluateHOLFiniteState_dec_total]
    let q : BitVec 64 := (p + (n + 7)) &&& ((0 : BitVec 64) - 8)
    have hq_eval : @evalHOLExact 64 F _ pState.toExact
        (fun a => Classical.propDecidable (pState.memaddrs a))
        (.op .and [.op .add [.var .local (ofString "p"), .var .local (ofString "n"), .const 7],
          .op .sub [.const 0, .const 8]]) = some (.val (.word q)) := by
      simp only [evalHOLExact, evalListHOLExact, hp_loc, hn_loc,
        wordOpHOL, wordOp, valueIsWord, valueWord, List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr]
      exact congrArg (fun w => some (ValueHOL.val (HolWordLab.word w)))
        (InitECandidate.Solver.HeapPotential.alloc_q_word_eq p n)
    dsimp only
    rw [hq_eval]
    have hsh_q : shapeEqHOL .one (shapeOfHOLExact (.val (.word q))) = true := by
      simp [shapeEqHOL, shapeOfHOLExact]
    dsimp only
    rw [if_pos hsh_q]
    dsimp only
    let qState := setVarHOLFinite (ofString "q") (.val (.word q)) pState
    have hq_loc : qState.locals.lookup (ofString "q") = some (.val (.word q)) := by
      simp [qState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hp_loc_q : qState.locals.lookup (ofString "p") = some (.val (.word p)) := by
      simp [qState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hp_loc,
        show ofString "q" ≠ ofString "p" by decide]
    have hsp_q : qState.globals.lookup (ofString "scratch_ptr") = some (.val (.word sp)) := hsp_lookup
    have hcode_q : qState.code = originalRuntimeCode := hcode
    rw [evaluateHOLFiniteState_seq_line780]
    have hev2 : @evalHOLExact 64 F _ qState.toExact
        (fun a => Classical.propDecidable (qState.memaddrs a))
        (.cmp .lower (.var .global (ofString "scratch_ptr")) (.var .local (ofString "q"))) =
        some (.val (.word (if sp.toNat < q.toNat then 1 else 0))) := by
      simp only [evalHOLExact, hsp_q, hq_loc, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, decide_eq_true_eq]
    by_cases hcmp2 : sp.toNat < q.toNat
    · have hite2 : evaluateHOLFiniteState qState
          (.ite (.cmp .lower (.var .global (ofString "scratch_ptr")) (.var .local (ofString "q")))
            (.call (some (none, none)) (ofString "trap_with") [.const 6])
            .skip) =
          evaluateHOLFiniteState qState (.call (some (none, none)) (ofString "trap_with") [.const 6]) := by
        rw [evaluateHOLFiniteState_ite, hev2, if_pos hcmp2]; simp
      rw [hite2]
      have hno_none := evaluate_call_trap_with_no_none qState 6 hcode_q
      have hno_ret := fun w => evaluate_call_trap_with_no_return qState 6 w hcode_q
      rcases htr : evaluateHOLFiniteState qState (.call (some (none, none)) (ofString "trap_with") [.const 6]) with ⟨r2, s2⟩
      rw [htr] at hno_none hno_ret
      cases r2 with
      | none => exact absurd rfl hno_none
      | some r2' =>
        intro retVal hret
        exact False.elim (hno_ret retVal hret)
    · have hite2 : evaluateHOLFiniteState qState
          (.ite (.cmp .lower (.var .global (ofString "scratch_ptr")) (.var .local (ofString "q")))
            (.call (some (none, none)) (ofString "trap_with") [.const 6])
            .skip) = (none, qState) := by
        rw [evaluateHOLFiniteState_ite, hev2, if_neg hcmp2]; simp [evaluateHOLFiniteState_skip]
      rw [hite2]
      dsimp only
      have hp_g : qState.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word p)) := hp_lookup
      have heval_end : evaluateHOLFiniteState qState
          (.seq (.assign .global (ofString "frame_mem_ptr") (.var .local (ofString "q")))
            (.return (.var .local (ofString "p")))) =
          (some (.returned (.val (.word p))),
            emptyLocalsHOLFinite (setGlobalHOLFinite (ofString "frame_mem_ptr") (.val (.word q)) qState)) := by
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
        simp [evalHOLExact, hq_loc, hp_loc_q, isValidValueHOLExact, lookupKvarHOLExact, hp_g,
          shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite, setGlobalHOLFinite,
          evaluateHOLFiniteState_return, sizeOfShapeWithContextHOL]
      rw [heval_end]
      intro retVal hret
      injection hret with hr
      injection hr with hr'
      exact ⟨hr'.symm, hcmp1, hcmp2, rfl⟩

theorem frame_mem_alloc_arith (p sp n : BitVec 64)
    (hp_le_sp : p.toNat ≤ sp.toNat)
    (hsp_le : sp.toNat ≤ scratchEnd)
    (hp_al : p.toNat % 8 = 0)
    (hcmp1 : ¬ ((sp - p).toNat < n.toNat))
    (hcmp2 : ¬ (sp.toNat < ((p + (n + 7)) &&& ((0 : BitVec 64) - 8)).toNat)) :
    let q := (p + (n + 7)) &&& ((0 : BitVec 64) - 8)
    q.toNat = p.toNat + (n.toNat + 7) / 8 * 8 ∧
    q.toNat ≤ sp.toNat ∧ q.toNat % 8 = 0 ∧ p.toNat ≤ q.toNat := by
  intro q
  have hse : scratchEnd < 2 ^ 64 - 8 := by rw [R11Shards.scratchEnd_val]; decide
  have hsub : (sp - p).toNat = sp.toNat - p.toNat := by
    rw [BitVec.toNat_sub]; omega
  have hn_le : n.toNat ≤ sp.toNat - p.toNat := by omega
  have h7 : (7 : BitVec 64).toNat = 7 := rfl
  have hn7 : (n + 7).toNat = n.toNat + 7 := by
    rw [BitVec.toNat_add, h7]; omega
  have hsum : (p + (n + 7)).toNat = p.toNat + n.toNat + 7 := by
    rw [BitVec.toNat_add, hn7]; omega
  have hq_nat : q.toNat = (p + (n + 7)).toNat / 8 * 8 :=
    and_neg8_toNat (p + (n + 7))
  rw [hsum] at hq_nat
  have hq_le : q.toNat ≤ sp.toNat := Nat.le_of_not_lt hcmp2
  exact ⟨by omega, hq_le, by omega, by omega⟩

structure FrameMemByteEff {F : Type} (s post : PanSemStateFiniteExact 64 F) (Rl : List Ivl) : Prop where
  code       : post.code = s.code
  memaddrs   : post.memaddrs = s.memaddrs
  shMemaddrs : post.shMemaddrs = s.shMemaddrs
  baseAddr   : post.baseAddr = s.baseAddr
  be         : post.be = s.be
  glob_other : ∀ g : String, ofString g ≠ ofString "frame_mem_ptr" → post.globals.lookup (ofString g) = s.globals.lookup (ofString g)
  out_dom    : ∀ a : BitVec 64, ¬ s.memaddrs a → post.memory a = s.memory a
  cell_frame : ∀ a : BitVec 64, (∀ i ∈ Rl, ¬ CellHits a.toNat i) → post.memory a = s.memory a
  byte_frame : ∀ b : Nat, b < 2 ^ 64 → (∀ i ∈ Rl, ¬ InIvl b i) → memB post b = memB s b

theorem FrameMemByteEff.of_bre {F : Type} {s post : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (h : ByteRegionEffect s post Rl) : FrameMemByteEff s post Rl :=
  ⟨h.code, h.memaddrs, h.shMemaddrs, h.baseAddr, h.be, fun _ _ => by rw [h.globals],
   h.out_dom, h.cell_frame, h.byte_frame⟩


theorem FrameMemByteEff.refl {F : Type} (s : PanSemStateFiniteExact 64 F) (Rl : List Ivl) :
    FrameMemByteEff s s Rl :=
  ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩

theorem FrameMemByteEff.with_locals_clock {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {Rl : List Ivl} (h : FrameMemByteEff s post Rl)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) :
    FrameMemByteEff s { post with locals := L, clock := k } Rl :=
  ⟨h.code, h.memaddrs, h.shMemaddrs, h.baseAddr, h.be, h.glob_other,
   h.out_dom, h.cell_frame, h.byte_frame⟩

theorem FrameMemByteEff.trans {F : Type} {a b c : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (h1 : FrameMemByteEff a b Rl) (h2 : FrameMemByteEff b c Rl) :
    FrameMemByteEff a c Rl := by
  refine ⟨h2.code.trans h1.code, h2.memaddrs.trans h1.memaddrs,
    h2.shMemaddrs.trans h1.shMemaddrs, h2.baseAddr.trans h1.baseAddr,
    h2.be.trans h1.be, fun g hg => (h2.glob_other g hg).trans (h1.glob_other g hg), ?_, ?_, ?_⟩
  · intro x hx
    have hxb : ¬ b.memaddrs x := by rw [h1.memaddrs]; exact hx
    rw [h2.out_dom x hxb, h1.out_dom x hx]
  · intro x hx; rw [h2.cell_frame x hx, h1.cell_frame x hx]
  · intro x hx hno; rw [h2.byte_frame x hx hno, h1.byte_frame x hx hno]

theorem FrameMemByteEff.mono {F : Type} {s post : PanSemStateFiniteExact 64 F} {R1 R2 : List Ivl}
    (h : FrameMemByteEff s post R1)
    (hsub : ∀ i ∈ R1, ∃ j ∈ R2, j.1 ≤ i.1 ∧ i.1 + i.2 ≤ j.1 + j.2) :
    FrameMemByteEff s post R2 := by
  refine ⟨h.code, h.memaddrs, h.shMemaddrs, h.baseAddr, h.be, h.glob_other, h.out_dom, ?_, ?_⟩
  · intro a ha; apply h.cell_frame a; intro i hi ⟨hc1, hc2⟩
    obtain ⟨j, hj, h1, h2⟩ := hsub i hi
    exact ha j hj ⟨by omega, by omega⟩
  · intro b hb hno; apply h.byte_frame b hb; intro i hi ⟨hb1, hb2⟩
    obtain ⟨j, hj, h1, h2⟩ := hsub i hi
    exact hno j hj ⟨by omega, by omega⟩

theorem FrameMemByteEff.to_bre_dummy {F : Type} {s post : PanSemStateFiniteExact 64 F} {Rl : List Ivl}
    (h : FrameMemByteEff s post Rl) :
    ByteRegionEffect s { post with globals := s.globals } Rl :=
  ⟨h.code, h.memaddrs, h.shMemaddrs, h.baseAddr, h.be, rfl,
   h.out_dom, h.cell_frame, h.byte_frame⟩

theorem evmInv_of_head_mem_extend {F : Type}
    {s post : PanSemStateFiniteExact 64 F} {freshIvl : Ivl}
    (hInv : EvmInv s)
    (hApost : ArenaReady post)
    (hfm_le : globN s "frame_mem_ptr" ≤ globN post "frame_mem_ptr")
    (heff : FrameMemByteEff s post [freshIvl, (globN s "ev", 280), (memW s (globN s "ev" + 24), memW s (globN s "ev" + 40))])
    (hfresh : freshIvl = (0, 0) ∨
      (freshIvl.1 % 8 = 0 ∧ freshIvl.2 % 8 = 0 ∧
        Inside freshIvl (globN s "frame_mem_ptr") (globN post "frame_mem_ptr")))
    (he0_other : ∀ off, off + 8 ≤ 280 → off % 8 = 0 → off ≠ 32 → off ≠ 40 →
      memW post (globN s "ev" + off) = memW s (globN s "ev" + off))
    (hnew_mem :
      (freshIvl.2 = 0 ∧ memW post (globN s "ev" + 40) = memW s (globN s "ev" + 40)) ∨
      (freshIvl.2 ≠ 0 ∧
        memW s (globN s "ev" + 24) + memW s (globN s "ev" + 40) = freshIvl.1 ∧
        memW post (globN s "ev" + 40) = memW s (globN s "ev" + 40) + freshIvl.2))
    (hlen_le_cap : memW post (globN s "ev" + 32) ≤ memW post (globN s "ev" + 40)) :
    EvmInv post ∧ evmChain post = evmChain s ∧ evmR post = evmR s := by
  obtain ⟨hAs, S, hW, hch_ne, hch_len, hch_last, hFW_all, hFR_all, hRW, hFO_pw, hFO_disj, hAT, hMarks, hRoles, hGas⟩ := hInv
  obtain ⟨Nd_at, hTr_at, hAT_at⟩ := hAT
  have hWT : WorldTypedWith s S Nd_at := ⟨hW.1, hW.2.1, hW.2.2.1, hTr_at⟩
  set e0 := globN s "ev"
  set c0 := globN s "cur_cont"
  set oldMem : Ivl := (memW s (e0 + 24), memW s (e0 + 40))
  have hch_cons : ∃ tl, evmChain s = (e0, c0) :: tl := ⟨_, rfl⟩
  obtain ⟨chTail, hch_eq⟩ := hch_cons
  have hhead_mem : (e0, c0) ∈ evmChain s := by rw [hch_eq]; exact List.mem_cons_self
  have hhead_FW := hFW_all _ hhead_mem
  obtain ⟨hb1, _, _, _⟩ := frameWF_bounds hAs.2 hhead_FW
  dsimp only at hb1
  have he0_8 : e0 % 8 = 0 := (hhead_FW.1 (e0, 280) (by simp)).2.1
  have holdMem_8 : oldMem.1 % 8 = 0 := hhead_FW.2.2.1.1
  have holdMem_sz8 : oldMem.2 % 8 = 0 := hhead_FW.2.2.1.2.1
  have hRl_list : ∀ x ∈ ([freshIvl, (e0, 280), oldMem] : List Ivl), x.1 % 8 = 0 := by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rcases hfresh with rfl | ⟨h8, _⟩
      · rfl
      · exact h8
    · exact he0_8
    · exact holdMem_8
  have hdom_eq : post.memaddrs = s.memaddrs := heff.memaddrs
  have hglob_eq : ∀ g, ofString g ≠ ofString "frame_mem_ptr" → globN post g = globN s g :=
    fun g hg => OpHandlers.globN_eq_of_lookup_eq (heff.glob_other g hg)
  have hh : globN s "heap_ptr" ≤ globN post "heap_ptr" := by rw [hglob_eq "heap_ptr" (by decide)]
  have hsc_le : globN post "scratch_ptr" ≤ globN s "scratch_ptr" := by rw [hglob_eq "scratch_ptr" (by decide)]
  have hfo_disj_wti : ∀ o ∈ frameObjects s (e0, c0), ∀ i ∈ worldTypedIvls s S Nd_at, i.2 = 0 ∨ Disj o i := by
    intro o ho i hi
    unfold worldTypedIvls at hi; simp only [List.mem_append] at hi
    rcases hi with ((((h1 | h2) | h3) | h4) | h5) | h6
    · obtain ⟨t, ht, hfp⟩ := List.mem_flatMap.1 h1
      exact Or.inr ((hFO_disj _ hhead_mem o ho).1 t ht i hfp)
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 h2
      exact Or.inr ((hFO_disj _ hhead_mem o ho).2 _ (typedRec_in_fixedObjects s hr))
    · simp only [List.mem_singleton] at h3; subst h3
      have hfix_j : (if globN s "journal_cap" = 0 then 0 else globN s "journal", 32 * globN s "journal_cap") ∈ fixedObjects s := by
        unfold fixedObjects; exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (by simp)))
      exact Or.inr ((hFO_disj _ hhead_mem o ho).2 _ hfix_j)
    · exact Or.inr ((hFO_disj _ hhead_mem o ho).2 _ (blockOut_in_fixedObjects h4))
    · exact Or.inr ((hFO_disj _ hhead_mem o ho).2 _ (bal_in_fixedObjects h5))
    · exact Or.inr (hAT_at o (List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨_, hhead_mem, rfl⟩, ho⟩) i h6)
  have hfresh_disj_alloc : ∀ i : Ivl, Allocated s i → Disj freshIvl i := by
    intro i hal
    rcases hfresh with rfl | ⟨_, _, hfin⟩
    · exact Or.inl rfl
    · obtain ⟨hfin1, hfin2⟩ := hfin
      have h1 := hAs.2.2.1; have h2 := hAs.2.2.2.1
      have h3 := hApost.2.2.2.2.1
      rw [hglob_eq "scratch_ptr" (by decide)] at h3
      rw [R11Shards.heapLimit_val] at h1; rw [R11Shards.scratchStart_val] at h2
      rcases hal with hheap | hscr
      · obtain ⟨_, hhi2⟩ := hheap
        exact Or.inr (Or.inr (Or.inr (by omega)))
      · obtain ⟨hlo1, _⟩ := hscr
        exact Or.inr (Or.inr (Or.inl (by omega)))
  have hwrite_disj_wti : ∀ x ∈ ([freshIvl, (e0, 280), oldMem] : List Ivl),
      ∀ i ∈ worldTypedIvls s S Nd_at, i.2 = 0 ∨ Disj x i := by
    intro x hx i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rcases worldTypedIvls_allocated hWT hi with hi0 | hal
      · exact Or.inl hi0
      · exact Or.inr (hfresh_disj_alloc i hal)
    · exact hfo_disj_wti (e0, 280) (by simp [frameObjects]) i hi
    · exact hfo_disj_wti oldMem (by simp [frameObjects, oldMem]) i hi
  have hcellG : SameTypedCells s { post with globals := s.globals } S Nd_at :=
    ByteRegionEffect.sameTypedCells (Rl := []) (extra := [freshIvl, (e0, 280), oldMem])
      hAs.1.memaddrs hWT (fun _ h => by simp at h) hwrite_disj_wti (by simpa using heff.to_bre_dummy)
  have hcell : SameTypedCells s post S Nd_at := hcellG
  have hfeq : fixedObjects post = fixedObjects s := by
    unfold fixedObjects
    rw [blockOutObjects_eq hAs.2 hWT.2.2.1 hcell (hglob_eq "bo" (by decide)),
        balObjects_eq hAs.2 hWT.1 hWT.2.2.1 hcell (hglob_eq "bal_accounts" (by decide)),
        hglob_eq "journal" (by decide),
        hglob_eq "journal_cap" (by decide)]
    congr 3
    apply List.map_congr_left
    intro gn hgn
    have hne : ofString gn.1 ≠ ofString "frame_mem_ptr" := by clear * - hgn; revert gn hgn; decide
    rw [hglob_eq gn.1 hne]
  have hFT_post := fixedTyped_of_eq hApost hWT.2.2.1 hh hsc_le hfeq
  have hcg : ∀ g ∈ coreWorldGlobals, globN post g = globN s g := by
    intro g hg
    have hne : ofString g ≠ ofString "frame_mem_ptr" := by clear * - hg; revert g hg; decide
    exact hglob_eq g hne
  obtain ⟨hWT_post, _⟩ := worldTypedWith_congr_w1 hAs hApost hh hsc_le hcg hcell hWT
    ⟨hFT_post, fun o ho => Or.inl (by rw [← hfeq]; exact ho)⟩
  have hW_post : WorldTyped post S :=
    ⟨hWT_post.1, hWT_post.2.1, hWT_post.2.2.1, Nd_at, hWT_post.2.2.2⟩
  have hmemW_disj : ∀ {base sz k : Nat}, base + sz ≤ 2 ^ 64 → base % 8 = 0 → k % 8 = 0 → k + 8 ≤ sz →
      (∀ x ∈ ([freshIvl, (e0, 280), oldMem] : List Ivl), Disj x (base, sz)) →
      memW post (base + k) = memW s (base + k) := by
    intro base sz k hbnd hb8 hk8 hk hdj
    unfold memW
    have ha : base + k < 2 ^ 64 := by omega
    have hbk8 : (base + k) % 8 = 0 := by omega
    have hbit : (BitVec.ofNat 64 (base + k)).toNat = base + k := Nat.mod_eq_of_lt ha
    rw [heff.cell_frame (BitVec.ofNat 64 (base + k))]
    intro x hx; rw [hbit]
    exact not_cellHits_of_disj_aligned (i := (base, sz)) hbk8 (hRl_list x hx)
      (Nat.le_add_right base k) (Nat.add_le_add_left hk base) (R11Shards.Disj.symm (hdj x hx))
  have hpw_head_tail :
      (frameObjects s (e0, c0)).Pairwise Disj ∧
      (∀ o1 ∈ frameObjects s (e0, c0),
        ∀ ec ∈ chTail, ∀ o2 ∈ frameObjects s ec, Disj o1 o2) := by
    have hpw := hFO_pw
    rw [hch_eq, List.map_cons, List.flatten_cons, List.pairwise_append] at hpw
    refine ⟨hpw.1, fun o1 ho1 ec hec o2 ho2 => hpw.2.2 o1 ho1 o2 ?_⟩
    exact List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨ec, hec, rfl⟩, ho2⟩
  have hfresh_disj_fo : ∀ ec ∈ evmChain s, ∀ o ∈ frameObjects s ec, Disj freshIvl o := by
    intro ec hec o ho
    rcases hfresh with rfl | ⟨_, _, hfin⟩
    · exact Or.inl rfl
    · obtain ⟨hfin1, hfin2⟩ := hfin
      have hFW := hFW_all ec hec
      have h1 := hAs.2.2.1; have h2 := hAs.2.2.2.1
      have h3 := hApost.2.2.2.2.1
      rw [hglob_eq "scratch_ptr" (by decide)] at h3
      rw [R11Shards.heapLimit_val] at h1; rw [R11Shards.scratchStart_val] at h2
      unfold frameObjects at ho
      rcases List.mem_append.1 ho with ho7 | holog
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at ho7
        rcases ho7 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · obtain ⟨hin1, _⟩ := (hFW.1 (ec.1, 280) (by simp)).1
          exact Or.inr (Or.inr (Or.inl (by dsimp only at hin1 ⊢; omega)))
        · obtain ⟨hin1, _⟩ := (hFW.1 (ec.2, 104) (by simp)).1
          exact Or.inr (Or.inr (Or.inl (by dsimp only at hin1 ⊢; omega)))
        · obtain ⟨hin1, _⟩ := (hFW.1 (memW s (ec.1 + 8), 32 * memW s (ec.1 + 232)) (by simp)).1
          exact Or.inr (Or.inr (Or.inl (by dsimp only at hin1 ⊢; omega)))
        · obtain ⟨_, hin2⟩ := hFW.2.1
          exact Or.inr (Or.inr (Or.inr (by dsimp only at hin2 ⊢; omega)))
        · obtain ⟨hin1, _⟩ := (hFW.1 (memW s (ec.1 + 88), 24) (by simp)).1
          exact Or.inr (Or.inr (Or.inl (by dsimp only at hin1 ⊢; omega)))
        · rcases hFW.2.2.2.2.2.2.2.2.2.2.2.2.1 with ⟨_, hin2⟩ | ⟨hin1, _⟩
          · exact Or.inr (Or.inr (Or.inr (by omega)))
          · exact Or.inr (Or.inr (Or.inl (by omega)))
        · rcases hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with ⟨hz, _⟩ | ⟨⟨_, hin2⟩, _⟩
          · unfold frameRet; simp [hz]; exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (Or.inr (by omega)))
      · unfold frameLogObjects at holog; dsimp only at holog
        obtain ⟨idx, hidx_mem, ho_own⟩ := List.mem_flatMap.1 holog
        rw [List.mem_range] at hidx_mem
        rcases hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with hz | ⟨_, _, _, _, hent⟩
        · obtain ⟨hin1, _⟩ := (hFW.1 (memW s (ec.1 + 88), 24) (by simp)).1
          dsimp only at hin1; omega
        · have hle := (hent idx hidx_mem).2
          have ho_rec := (List.mem_filter.1 ho_own).1
          simp only [logRecordIvls, List.mem_cons, List.not_mem_nil, or_false] at ho_rec
          rcases ho_rec with rfl | rfl | rfl | rfl
          · obtain ⟨_, hin2⟩ := hle.2.1; exact Or.inr (Or.inr (Or.inr (by dsimp only at hin2 ⊢; omega)))
          · obtain ⟨_, hin2⟩ := hle.2.2.2.2.1; exact Or.inr (Or.inr (Or.inr (by dsimp only at hin2 ⊢; omega)))
          · obtain ⟨_, hin2⟩ := hle.2.2.2.2.2.1; exact Or.inr (Or.inr (Or.inr (by dsimp only at hin2 ⊢; omega)))
          · obtain ⟨_, hin2⟩ := hle.2.2.2.2.2.2; exact Or.inr (Or.inr (Or.inr (by dsimp only at hin2 ⊢; omega)))
  have hdisj_old_fresh : ∀ o : Ivl, Disj oldMem o → Disj freshIvl o →
      Disj (memW post (e0 + 24), memW post (e0 + 40)) o := by
    intro o hd_old hd_fr
    have he24_eq := he0_other 24 (by omega) (by omega) (by omega) (by omega)
    rw [he24_eq]
    rcases hnew_mem with ⟨_, h40_eq⟩ | ⟨hnz, hcontig, h40_eq⟩
    · rw [h40_eq]; exact hd_old
    · rw [h40_eq]
      rcases hd_fr with hz | hz | hlt | hgt
      · exact absurd hz hnz
      · exact Or.inr (Or.inl hz)
      · exact Or.inr (Or.inr (Or.inl (by dsimp only [oldMem] at hcontig hlt ⊢; omega)))
      · rcases hd_old with hoz | hoz | holt | hogt
        · dsimp only [oldMem] at hoz
          rw [hoz] at hcontig ⊢
          simp only [Nat.add_zero, Nat.zero_add] at hcontig ⊢
          rw [hcontig]
          exact Or.inr (Or.inr (Or.inr hgt))
        · exact Or.inr (Or.inl hoz)
        · by_cases hoz0 : o.2 = 0
          · exact Or.inr (Or.inl hoz0)
          · have hle_f : freshIvl.1 ≤ o.1 := by rw [← hcontig]; exact holt
            exact False.elim (by omega)
        · exact Or.inr (Or.inr (Or.inr hogt))
  have hhead_pw := hpw_head_tail.1
  unfold frameObjects at hhead_pw
  have hp0 := List.pairwise_cons.1 hhead_pw
  have hp1 := List.pairwise_cons.1 hp0.2
  have hp2 := List.pairwise_cons.1 hp1.2
  have hp3 := List.pairwise_cons.1 hp2.2
  have hdisj_write_nonmem : ∀ ec ∈ evmChain s,
      (∀ x ∈ ([freshIvl, (e0, 280), oldMem] : List Ivl), Disj x (ec.2, 104)) ∧
      (∀ x ∈ ([freshIvl, (e0, 280), oldMem] : List Ivl), Disj x (memW s (ec.1 + 88), 24)) ∧
      (∀ x ∈ ([freshIvl, (e0, 280), oldMem] : List Ivl), Disj x (frameLogs s ec)) ∧
      (∀ i < memW s (memW s (ec.1 + 88) + 8),
        ∀ x ∈ ([freshIvl, (e0, 280), oldMem] : List Ivl),
          Disj x (memW s (memW s (memW s (ec.1 + 88)) + 8 * i), 40)) := by
    intro ec hec
    have hlog_in : ∀ i < memW s (memW s (ec.1 + 88) + 8),
        (memW s (memW s (memW s (ec.1 + 88)) + 8 * i), 40) ∈ frameLogObjects s ec := by
      intro i hi; unfold frameLogObjects; dsimp only
      exact List.mem_flatMap.2 ⟨i, List.mem_range.2 hi,
        by unfold logOwnedIvls logRecordIvls; exact List.mem_filter.2 ⟨by simp, by simp⟩⟩
    rw [hch_eq, List.mem_cons] at hec
    rcases hec with rfl | htail
    · have hmem_head : (e0, c0) ∈ evmChain s := hhead_mem
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl
        · exact hfresh_disj_fo _ hmem_head _ (by simp [frameObjects])
        · exact hp0.1 _ (by simp)
        · exact R11Shards.Disj.symm (hp1.1 _ (by simp [oldMem]))
      · intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl
        · exact hfresh_disj_fo _ hmem_head _ (by simp [frameObjects])
        · exact hp0.1 _ (by simp)
        · exact hp3.1 _ (by simp)
      · intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl
        · exact hfresh_disj_fo _ hmem_head _ (by simp [frameObjects])
        · exact hp0.1 _ (by simp)
        · exact hp3.1 _ (by simp)
      · intro i hi x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        have hli := hlog_in i hi
        rcases hx with rfl | rfl | rfl
        · exact hfresh_disj_fo _ hmem_head _ (by unfold frameObjects; exact List.mem_append_right _ hli)
        · exact hp0.1 _ (by simp [hli])
        · exact hp3.1 _ (by simp [hli])
    · have hmem_ec : ec ∈ evmChain s := by rw [hch_eq]; exact List.mem_cons_of_mem _ htail
      have hall : ∀ o2 ∈ frameObjects s ec, ∀ x ∈ ([freshIvl, (e0, 280), oldMem] : List Ivl), Disj x o2 := by
        intro o2 ho2 x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl
        · exact hfresh_disj_fo ec hmem_ec o2 ho2
        · exact hpw_head_tail.2 _ (by simp [frameObjects]) ec htail o2 ho2
        · exact hpw_head_tail.2 _ (by simp [frameObjects, oldMem]) ec htail o2 ho2
      exact ⟨hall _ (by simp [frameObjects]),
             hall _ (by simp [frameObjects]),
             hall _ (by simp [frameObjects]),
             fun i hi => hall _ (by unfold frameObjects; exact List.mem_append_right _ (hlog_in i hi))⟩
  have htail_rec_eq : ∀ ec ∈ chTail, ∀ k, k + 8 ≤ 280 → k % 8 = 0 → memW post (ec.1 + k) = memW s (ec.1 + k) := by
    intro ec htail k hk hk8
    have hec : ec ∈ evmChain s := by rw [hch_eq]; exact List.mem_cons_of_mem _ htail
    have hFW := hFW_all ec hec
    obtain ⟨hb_e, _, _, _⟩ := frameWF_bounds hAs.2 hFW
    have he8 : ec.1 % 8 = 0 := (hFW.1 (ec.1, 280) (by simp)).2.1
    apply hmemW_disj hb_e he8 hk8 hk
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact hfresh_disj_fo ec hec (ec.1, 280) (by simp [frameObjects])
    · exact hpw_head_tail.2 _ (by simp [frameObjects]) ec htail _ (by simp [frameObjects])
    · exact hpw_head_tail.2 _ (by simp [frameObjects, oldMem]) ec htail _ (by simp [frameObjects])
  have hrec_eq : ∀ ec ∈ evmChain s,
      (∀ k, k + 8 ≤ 280 → k % 8 = 0 → k ≠ 32 → k ≠ 40 → memW post (ec.1 + k) = memW s (ec.1 + k)) ∧
      (∀ k, k + 8 ≤ 104 → k % 8 = 0 → memW post (ec.2 + k) = memW s (ec.2 + k)) ∧
      (∀ k, k + 8 ≤ 24 → k % 8 = 0 → memW post (memW s (ec.1 + 88) + k) = memW s (memW s (ec.1 + 88) + k)) := by
    intro ec hec
    have hFW := hFW_all ec hec
    obtain ⟨_, hb_c, hb_88, _⟩ := frameWF_bounds hAs.2 hFW
    have hc8 : ec.2 % 8 = 0 := (hFW.1 (ec.2, 104) (by simp)).2.1
    have h88_8 : (memW s (ec.1 + 88)) % 8 = 0 := (hFW.1 (memW s (ec.1 + 88), 24) (by simp)).2.1
    obtain ⟨hd_c, hd_88, _, _⟩ := hdisj_write_nonmem ec hec
    refine ⟨?_,
      fun k hk hk8 => hmemW_disj hb_c hc8 hk8 hk hd_c,
      fun k hk hk8 => hmemW_disj hb_88 h88_8 hk8 hk hd_88⟩
    intro k hk hk8 hk_32 hk_40
    rw [hch_eq, List.mem_cons] at hec
    rcases hec with rfl | htail
    · exact he0_other k hk hk8 hk_32 hk_40
    · exact htail_rec_eq ec htail k hk hk8
  have hchain_aux : ∀ (fuel e c : Nat),
      (∀ ec ∈ evmChainFrom s fuel e c, ec ∈ evmChain s) →
      evmChainFrom post fuel e c = evmChainFrom s fuel e c := by
    intro fuel; induction fuel with
    | zero => intros; rfl
    | succ fuel ih =>
      intro e c hsub
      have hec : (e, c) ∈ evmChain s := hsub (e, c) (by simp [evmChainFrom])
      obtain ⟨_, hc_eq, _⟩ := hrec_eq (e, c) hec
      have hc16 := hc_eq 16 (by omega) (by omega)
      have hc0 : memW post c = memW s c := by simpa using hc_eq 0 (by omega) (by omega)
      have hc8 := hc_eq 8 (by omega) (by omega)
      simp only [evmChainFrom, hc16, hc0, hc8]
      split
      · rfl
      · rename_i hne16
        rw [ih]; intro ec' hec'; exact hsub ec' (by simp [evmChainFrom, hne16, hec'])
  have hchain_eq : evmChain post = evmChain s := by
    unfold evmChain
    rw [hglob_eq "ev" (by decide), hglob_eq "cur_cont" (by decide)]
    exact hchain_aux _ _ _ (fun _ h => h)
  have hframeLogs_eq : ∀ ec ∈ evmChain s, frameLogs post ec = frameLogs s ec := by
    intro ec hec
    obtain ⟨he_eq, _, h88_eq⟩ := hrec_eq ec hec
    unfold frameLogs
    rw [he_eq 88 (by omega) (by omega) (by omega) (by omega),
        show memW post (memW s (ec.1 + 88)) = memW s (memW s (ec.1 + 88)) by simpa using h88_eq 0 (by omega) (by omega),
        h88_eq 16 (by omega) (by omega)]
  have hframeRet_eq : ∀ ec ∈ evmChain s, frameRet post ec = frameRet s ec := by
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    unfold frameRet
    rw [he_eq 216 (by omega) (by omega) (by omega) (by omega),
        he_eq 144 (by omega) (by omega) (by omega) (by omega)]
  have hlogs_congr : ∀ ec ∈ evmChain s,
      frameLogObjects post ec = frameLogObjects s ec ∧ LogsListOK post (memW post (ec.1 + 88)) := by
    intro ec hec
    have hFW := hFW_all ec hec
    obtain ⟨_, _, _, hfob⟩ := frameWF_bounds hAs.2 hFW
    obtain ⟨he_eq, _, h88_eq⟩ := hrec_eq ec hec
    obtain ⟨_, _, hd_fl, hd_lr⟩ := hdisj_write_nonmem ec hec
    have hl0 : memW post (memW s (ec.1 + 88)) = memW s (memW s (ec.1 + 88)) := by
      simpa using h88_eq 0 (by omega) (by omega)
    have hl8 := h88_eq 8 (by omega) (by omega)
    have hl16 := h88_eq 16 (by omega) (by omega)
    have harr_eq : ∀ i, i < memW s (memW s (ec.1 + 88) + 8) →
        memW post ((memW s (memW s (ec.1 + 88))) + 8 * i) = memW s ((memW s (memW s (ec.1 + 88))) + 8 * i) := by
      intro i hi
      have hfl_in : frameLogs s ec ∈ frameObjects s ec := by simp [frameObjects]
      have hlen_le : memW s (memW s (ec.1 + 88) + 8) ≤ memW s (memW s (ec.1 + 88) + 16) :=
        hFW.2.2.2.2.2.2.2.2.2.2.2.1
      have hfl_b : (frameLogs s ec).1 + (frameLogs s ec).2 ≤ 2 ^ 64 := by
        rcases hfob _ hfl_in with h0 | hb
        · unfold frameLogs at h0; dsimp only at h0; omega
        · exact hb
      have hfl_8 : (memW s (memW s (ec.1 + 88))) % 8 = 0 := hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
      exact hmemW_disj hfl_b hfl_8 (by omega) (by unfold frameLogs; dsimp only; omega) hd_fl
    have hlr_eq : ∀ i (_hi : i < memW s (memW s (ec.1 + 88) + 8)) off, off + 8 ≤ 40 → off % 8 = 0 →
        memW post ((memW s (memW s (memW s (ec.1 + 88)) + 8 * i)) + off) =
          memW s ((memW s (memW s (memW s (ec.1 + 88)) + 8 * i)) + off) := by
      intro i hi off hoff hoff8
      have hlr_in : (memW s (memW s (memW s (ec.1 + 88)) + 8 * i), 40) ∈ frameObjects s ec := by
        unfold frameObjects; apply List.mem_append_right
        unfold frameLogObjects; dsimp only
        exact List.mem_flatMap.2 ⟨i, List.mem_range.2 hi,
          by unfold logOwnedIvls logRecordIvls; exact List.mem_filter.2 ⟨by simp, by simp⟩⟩
      have hlr_b : memW s (memW s (memW s (ec.1 + 88)) + 8 * i) + 40 ≤ 2 ^ 64 := by
        rcases hfob _ hlr_in with h0 | hb
        · dsimp only at h0; omega
        · exact hb
      have hlr_8 : (memW s (memW s (memW s (ec.1 + 88)) + 8 * i)) % 8 = 0 := by
        rcases hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with hz | ⟨_, _, _, _, hent⟩
        · obtain ⟨he88_in, _⟩ := (hFW.1 (memW s (ec.1 + 88), 24) (by simp)).1
          have h1 := hAs.2.2.2.1; have h2 := hAs.2.2.2.2.1
          rw [R11Shards.scratchStart_val] at h1; dsimp only at he88_in; omega
        · exact (hent i hi).2.1.1
      exact hmemW_disj hlr_b hlr_8 hoff8 hoff (hd_lr i hi)
    refine ⟨?_, ?_⟩
    · unfold frameLogObjects; dsimp only
      rw [he_eq 88 (by omega) (by omega) (by omega) (by omega), hl8]
      apply List.flatMap_congr; intro i hi; rw [List.mem_range] at hi
      rw [hl0, harr_eq i hi]
      have r0 := hlr_eq i hi 0 (by omega) (by omega)
      have r8 := hlr_eq i hi 8 (by omega) (by omega)
      have r16 := hlr_eq i hi 16 (by omega) (by omega)
      have r24 := hlr_eq i hi 24 (by omega) (by omega)
      have r32 := hlr_eq i hi 32 (by omega) (by omega)
      simp only [Nat.add_zero] at r0
      unfold logOwnedIvls logRecordIvls
      rw [r0, r8, r16, r24, r32, hglob_eq "vm_system_address" (by decide)]
    · rw [he_eq 88 (by omega) (by omega) (by omega) (by omega)]
      rcases hFW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with hz | ⟨hw_l, hal_l, hlt28, hle_cap, hent⟩
      · exact Or.inl hz
      · right
        refine ⟨(wordsOK_congr_dom hdom_eq).2 hw_l, allocated_mono_scr hh hsc_le hal_l,
          by rw [hl8]; exact hlt28, by rw [hl8, hl16]; exact hle_cap, fun i hi => ?_⟩
        rw [hl8] at hi; rw [hl0]
        obtain ⟨hwa, hle⟩ := hent i hi
        refine ⟨(wordAt_congr_dom hdom_eq).2 hwa, ?_⟩
        rw [harr_eq i hi]
        have r0 := hlr_eq i hi 0 (by omega) (by omega)
        have r8 := hlr_eq i hi 8 (by omega) (by omega)
        have r16 := hlr_eq i hi 16 (by omega) (by omega)
        have r24 := hlr_eq i hi 24 (by omega) (by omega)
        have r32 := hlr_eq i hi 32 (by omega) (by omega)
        simp only [Nat.add_zero] at r0
        unfold LogEntryOK at hle ⊢
        rw [r0, r8, r16, r24, r32, hglob_eq "heap_ptr" (by decide)]
        exact ⟨(wordsOK_congr_dom hdom_eq).2 hle.1, hle.2⟩
  have htail_fo_eq : ∀ ec ∈ chTail, frameObjects post ec = frameObjects s ec := by
    intro ec htail
    have hec : ec ∈ evmChain s := by rw [hch_eq]; exact List.mem_cons_of_mem _ htail
    unfold frameObjects
    rw [htail_rec_eq ec htail 8 (by omega) (by omega),
        htail_rec_eq ec htail 232 (by omega) (by omega),
        htail_rec_eq ec htail 24 (by omega) (by omega),
        htail_rec_eq ec htail 40 (by omega) (by omega),
        htail_rec_eq ec htail 88 (by omega) (by omega),
        hframeLogs_eq ec hec, hframeRet_eq ec hec, (hlogs_congr ec hec).1]
  have hfs_eq : ∀ ec ∈ evmChain s, frameScratch post ec = frameScratch s ec := by
    intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    unfold frameScratch
    rw [he_eq 8 (by omega) (by omega) (by omega) (by omega),
        he_eq 232 (by omega) (by omega) (by omega) (by omega),
        he_eq 88 (by omega) (by omega) (by omega) (by omega)]
  have hfo_post_cases : ∀ ec ∈ evmChain s, ∀ o ∈ frameObjects post ec,
      o ∈ frameObjects s ec ∨ (ec = (e0, c0) ∧ o = (memW post (e0 + 24), memW post (e0 + 40))) := by
    intro ec hec o ho
    rw [hch_eq, List.mem_cons] at hec
    rcases hec with rfl | htail
    · unfold frameObjects at ho
      rw [he0_other 8 (by omega) (by omega) (by omega) (by omega),
          he0_other 232 (by omega) (by omega) (by omega) (by omega),
          he0_other 88 (by omega) (by omega) (by omega) (by omega),
          hframeLogs_eq _ hhead_mem, hframeRet_eq _ hhead_mem, (hlogs_congr _ hhead_mem).1] at ho
      rcases List.mem_append.1 ho with ho7 | holog
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at ho7
        rcases ho7 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact Or.inl (by simp [frameObjects])
        · exact Or.inl (by simp [frameObjects])
        · exact Or.inl (by simp [frameObjects])
        · exact Or.inr ⟨rfl, rfl⟩
        · exact Or.inl (by simp [frameObjects])
        · exact Or.inl (by simp [frameObjects])
        · exact Or.inl (by simp [frameObjects])
      · exact Or.inl (by unfold frameObjects; exact List.mem_append_right _ holog)
    · left; rwa [htail_fo_eq ec htail] at ho
  have hframeRoleSlots_eq : frameRoleSlots post (evmChain s) = frameRoleSlots s (evmChain s) := by
    unfold frameRoleSlots; apply List.flatMap_congr; intro ec hec
    obtain ⟨he_eq, _, _⟩ := hrec_eq ec hec
    rw [he_eq 136 (by omega) (by omega) (by omega) (by omega),
        he_eq 168 (by omega) (by omega) (by omega) (by omega),
        he_eq 176 (by omega) (by omega) (by omega) (by omega)]
  have hfp_eq_all : ∀ t ∈ S, htabFootprint post t = htabFootprint s t :=
    fun t ht => htabFootprint_eq hcell ht (hWT.1.2.1 t ht).1
  have hR_eq : evmR post = evmR s :=
    evmR_eq_of_chain_and_words hchain_eq (fun ec hec =>
      ⟨(hrec_eq ec hec).1 64 (by omega) (by omega) (by omega) (by omega),
       (hrec_eq ec hec).1 192 (by omega) (by omega) (by omega) (by omega)⟩)
  refine ⟨⟨hApost, S, hW_post, ?_⟩, hchain_eq, hR_eq⟩
  dsimp only; rw [hchain_eq]
  refine ⟨hch_ne, hch_len, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨ec, hec, hk0⟩ := hch_last
    have hec_mem := List.mem_of_mem_getLast? hec
    exact ⟨ec, hec, by rw [(hrec_eq ec hec_mem).2.1 16 (by omega) (by omega)]; exact hk0⟩
  · intro ec hec
    obtain ⟨he_eq, _, h88_eq⟩ := hrec_eq ec hec
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, _, c17⟩ := hFW_all ec hec
    have hlo_ok := (hlogs_congr ec hec).2
    have hmsg_ok : MsgOwned post S (memW post (ec.1 + 112)) := by
      rw [he_eq 112 (by omega) (by omega) (by omega) (by omega)]
      obtain ⟨hal_m, hw_m, hdt, hdf, hdfo, Nd_m, hTr_m, hdj_m⟩ := c17
      obtain ⟨hTr_int, hsub_int⟩ := R11Shards.triesTypedWith_inter hTr_at hTr_m
      set Ndi := Nd_at.filter (fun n => decide (n ∈ Nd_m))
      have hcell_i : SameTypedCells s post S Ndi := by
        have hwti_sub : ∀ i ∈ worldTypedIvls s S Ndi, i ∈ worldTypedIvls s S Nd_at := by
          intro i hi; unfold worldTypedIvls at hi ⊢
          rcases List.mem_append.1 hi with hpre | hne
          · exact List.mem_append_left _ hpre
          · apply List.mem_append_right; unfold nodeExtents at hne ⊢
            obtain ⟨n, hn, hnx⟩ := List.mem_flatMap.1 hne
            exact List.mem_flatMap.2 ⟨n, (List.mem_filter.1 hn).1, hnx⟩
        refine ⟨hcell.1, hcell.2.1, hcell.2.2.1, hcell.2.2.2.1,
          fun a ha ha8 ⟨i, hi, h1, h2⟩ => hcell.2.2.2.2.1 a ha ha8 ⟨i, hwti_sub i hi, h1, h2⟩,
          fun b hb ⟨i, hi, h1, h2⟩ => hcell.2.2.2.2.2 b hb ⟨i, hwti_sub i hi, h1, h2⟩⟩
      obtain ⟨hWT_i_post, _⟩ := worldTypedWith_congr_w1 hAs hApost hh hsc_le hcg hcell_i
        ⟨hWT.1, hWT.2.1, hWT.2.2.1, hTr_int⟩
        ⟨hFT_post, fun o ho => Or.inl (by rw [← hfeq]; exact ho)⟩
      refine ⟨allocated_mono_scr hh hsc_le hal_m, (wordsOK_congr_dom hdom_eq).2 hw_m,
        fun t ht i hi => by rw [hfp_eq_all t ht] at hi; exact hdt t ht i hi,
        by rw [hfeq]; exact hdf,
        ?_,
        Ndi, hWT_i_post.2.2.2, fun o ho j hj => ?_⟩
      · rw [hchain_eq]; intro ec' hec' o ho
        rcases hfo_post_cases ec' hec' o ho with ho_old | ⟨_, rfl⟩
        · exact hdfo ec' hec' o ho_old
        · exact R11Shards.Disj.symm (hdisj_old_fresh (memW s (ec.1 + 112), 176)
            (R11Shards.Disj.symm (hdfo _ hhead_mem oldMem (by simp [frameObjects, oldMem])))
            (hfresh_disj_alloc (memW s (ec.1 + 112), 176) hal_m))
      · rw [nodeExtents_eq hTr_int.1 hcell_i] at hj
        exact hdj_m o ho j (hsub_int j hj).2
    unfold FrameWF; dsimp only
    rw [he_eq 8 (by omega) (by omega) (by omega) (by omega),
        he_eq 16 (by omega) (by omega) (by omega) (by omega),
        he_eq 232 (by omega) (by omega) (by omega) (by omega),
        he_eq 88 (by omega) (by omega) (by omega) (by omega),
        he_eq 24 (by omega) (by omega) (by omega) (by omega),
        he_eq 136 (by omega) (by omega) (by omega) (by omega),
        he_eq 168 (by omega) (by omega) (by omega) (by omega),
        he_eq 176 (by omega) (by omega) (by omega) (by omega),
        h88_eq 16 (by omega) (by omega), h88_eq 8 (by omega) (by omega),
        hframeLogs_eq ec hec,
        he_eq 216 (by omega) (by omega) (by omega) (by omega),
        he_eq 144 (by omega) (by omega) (by omega) (by omega),
        hframeRet_eq ec hec,
        hglob_eq "scratch_ptr" (by decide),
        hglob_eq "heap_ptr" (by decide),
        hglob_eq "evm_empty" (by decide)]
    rw [he_eq 88 (by omega) (by omega) (by omega) (by omega)] at hlo_ok
    have hret_in_post : (memW s (ec.1 + 216) = 0 ∧ memW s (ec.1 + 144) = globN s "evm_empty") ∨
        Inside (frameRet s ec) sourceBase (globN s "heap_ptr") ∧ WordsOK post (frameRet s ec) := by
      rcases c15 with h0 | ⟨hin, hw⟩
      · exact Or.inl h0
      · exact Or.inr ⟨hin, (wordsOK_congr_dom hdom_eq).2 hw⟩
    rw [hch_eq, List.mem_cons] at hec
    rcases hec with rfl | htail
    · have hc2_post : Inside (memW s (e0 + 24), memW post (e0 + 40)) scratchStart (globN post "frame_mem_ptr") ∧
          WordsOK post (memW s (e0 + 24), memW post (e0 + 40)) := by
        rcases hnew_mem with ⟨_, h40_eq⟩ | ⟨hnz, hcontig, h40_eq⟩
        · rw [h40_eq]
          exact ⟨⟨c2.1, le_trans c2.2 hfm_le⟩, (wordsOK_congr_dom hdom_eq).2 c3⟩
        · rcases hfresh with rfl | ⟨_, hfsz8, hfin1, hfin2⟩
          · exact absurd rfl hnz
          · rw [h40_eq]
            have hin_new : Inside (memW s (e0 + 24), memW s (e0 + 40) + freshIvl.2) scratchStart (globN post "frame_mem_ptr") :=
              ⟨c2.1, by dsimp only at hcontig hfin2 ⊢; omega⟩
            have hsb_le_ss : sourceBase ≤ scratchStart := by decide
            have hse_le_he : scratchEnd ≤ heapEnd := by decide
            have hfp_le_se : globN post "frame_mem_ptr" ≤ scratchEnd :=
              le_trans hApost.2.2.2.2.1 hApost.2.2.2.2.2.1
            have hw_new : WordsOK post (memW s (e0 + 24), memW s (e0 + 40) + freshIvl.2) :=
              Wave8Contracts.M26.wordsOK_of_guestInv post hApost.1
                (memW s (e0 + 24)) (memW s (e0 + 40) + freshIvl.2)
                holdMem_8 (by dsimp only [oldMem] at holdMem_sz8; omega)
                (le_trans hsb_le_ss c2.1) (le_trans hin_new.2 (le_trans hfp_le_se hse_le_he))
            exact ⟨hin_new, hw_new⟩
      exact ⟨fun i hi => ⟨(c1 i hi).1, (wordsOK_congr_dom hdom_eq).2 (c1 i hi).2⟩,
        hc2_post.1, hc2_post.2, c4, c5, c6, hlen_le_cap, c8, c9, c10, c11, c12,
        c13, (wordsOK_congr_dom hdom_eq).2 c14, hret_in_post, hlo_ok, hmsg_ok⟩
    · rw [htail_rec_eq ec htail 32 (by omega) (by omega),
          htail_rec_eq ec htail 40 (by omega) (by omega)]
      exact ⟨fun i hi => ⟨(c1 i hi).1, (wordsOK_congr_dom hdom_eq).2 (c1 i hi).2⟩,
        ⟨c2.1, le_trans c2.2 hfm_le⟩, (wordsOK_congr_dom hdom_eq).2 c3, c4, c5, c6, c7, c8, c9, c10, c11, c12,
        c13, (wordsOK_congr_dom hdom_eq).2 c14, hret_in_post, hlo_ok, hmsg_ok⟩
  · intro ec hec
    have htail : ec ∈ chTail := by rw [hch_eq, List.tail_cons] at hec; exact hec
    unfold FrameRoom
    rw [htail_rec_eq ec htail 16 (by omega) (by omega),
        htail_rec_eq ec htail 232 (by omega) (by omega)]
    exact hFR_all ec hec
  · intro i hi
    have hi0 : (evmChain s)[i]'(by omega) ∈ evmChain s := List.getElem_mem _
    have hi1_tail : (evmChain s)[i + 1] ∈ chTail := by simp [hch_eq]
    rw [(hrec_eq _ hi0).2.1 80 (by omega) (by omega),
        (hrec_eq _ hi0).2.1 72 (by omega) (by omega),
        htail_rec_eq _ hi1_tail 40 (by omega) (by omega)]
    exact hRW i hi
  · have htail_map_eq : chTail.map (frameObjects post) = chTail.map (frameObjects s) :=
      List.map_congr_left htail_fo_eq
    rw [hch_eq, List.map_cons, List.flatten_cons, htail_map_eq, List.pairwise_append]
    have hFO_pw' := hFO_pw
    rw [hch_eq, List.map_cons, List.flatten_cons, List.pairwise_append] at hFO_pw'
    refine ⟨?_, hFO_pw'.2.1, ?_⟩
    · unfold frameObjects
      rw [he0_other 8 (by omega) (by omega) (by omega) (by omega),
          he0_other 232 (by omega) (by omega) (by omega) (by omega),
          he0_other 88 (by omega) (by omega) (by omega) (by omega),
          hframeLogs_eq _ hhead_mem, hframeRet_eq _ hhead_mem, (hlogs_congr _ hhead_mem).1]
      change ((e0, 280) :: (c0, 104) :: (memW s (e0 + 8), 32 * memW s (e0 + 232)) ::
        (memW post (e0 + 24), memW post (e0 + 40)) :: (memW s (e0 + 88), 24) ::
        frameLogs s (e0, c0) :: frameRet s (e0, c0) :: frameLogObjects s (e0, c0)).Pairwise Disj
      refine List.pairwise_cons.2 ⟨?_, List.pairwise_cons.2 ⟨?_, List.pairwise_cons.2 ⟨?_, List.pairwise_cons.2 ⟨?_, hp3.2⟩⟩⟩⟩
      · intro o ho; simp only [List.mem_cons] at ho
        rcases ho with rfl | rfl | rfl | ho_rest
        · exact hp0.1 _ (by simp)
        · exact hp0.1 _ (by simp)
        · exact R11Shards.Disj.symm (hdisj_old_fresh (e0, 280)
            (R11Shards.Disj.symm (hp0.1 oldMem (by simp [oldMem])))
            (hfresh_disj_fo _ hhead_mem (e0, 280) (by simp [frameObjects])))
        · exact hp0.1 _ (by simp [ho_rest])
      · intro o ho; simp only [List.mem_cons] at ho
        rcases ho with rfl | rfl | ho_rest
        · exact hp1.1 _ (by simp)
        · exact R11Shards.Disj.symm (hdisj_old_fresh (c0, 104)
            (R11Shards.Disj.symm (hp1.1 oldMem (by simp [oldMem])))
            (hfresh_disj_fo _ hhead_mem (c0, 104) (by simp [frameObjects])))
        · exact hp1.1 _ (by simp [ho_rest])
      · intro o ho; simp only [List.mem_cons] at ho
        rcases ho with rfl | ho_rest
        · exact R11Shards.Disj.symm (hdisj_old_fresh (memW s (e0 + 8), 32 * memW s (e0 + 232))
            (R11Shards.Disj.symm (hp2.1 oldMem (by simp [oldMem])))
            (hfresh_disj_fo _ hhead_mem _ (by simp [frameObjects])))
        · exact hp2.1 _ (by simp [ho_rest])
      · intro o ho
        have ho_in : o ∈ frameObjects s (e0, c0) := by
          unfold frameObjects
          simp only [List.mem_cons] at ho
          rcases ho with rfl | rfl | rfl | ho_log
          · simp
          · simp
          · simp
          · exact List.mem_append_right _ ho_log
        exact hdisj_old_fresh o (hp3.1 o ho) (hfresh_disj_fo _ hhead_mem o ho_in)
    · intro o1 ho1 o2 ho2
      obtain ⟨l2, hl2, ho2_in⟩ := List.mem_flatten.1 ho2
      obtain ⟨ec2, hec2, rfl⟩ := List.mem_map.1 hl2
      have hec2_mem : ec2 ∈ evmChain s := by rw [hch_eq]; exact List.mem_cons_of_mem _ hec2
      rcases hfo_post_cases _ hhead_mem o1 ho1 with ho1_old | ⟨_, rfl⟩
      · exact hFO_pw'.2.2 o1 ho1_old o2 ho2
      · exact hdisj_old_fresh o2
          (hFO_pw'.2.2 oldMem (by simp [frameObjects, oldMem]) o2 ho2)
          (hfresh_disj_fo ec2 hec2_mem o2 ho2_in)
  · intro ec hec o ho
    rw [hfeq]
    rcases hfo_post_cases ec hec o ho with ho_old | ⟨_, rfl⟩
    · exact ⟨fun t ht i hi => by rw [hfp_eq_all t ht] at hi; exact (hFO_disj ec hec o ho_old).1 t ht i hi,
        (hFO_disj ec hec o ho_old).2⟩
    · refine ⟨fun t ht i hi => ?_, fun j hj => ?_⟩
      · rw [hfp_eq_all t ht] at hi
        exact hdisj_old_fresh i
          ((hFO_disj _ hhead_mem oldMem (by simp [frameObjects, oldMem])).1 t ht i hi)
          (hfresh_disj_alloc i ((hWT.1.2.1 t ht).2 i hi).1)
      · rcases hWT.2.2.1.1 j hj with hj0 | ⟨hal_j, _⟩
        · exact Or.inr (Or.inl hj0)
        · exact hdisj_old_fresh j
            ((hFO_disj _ hhead_mem oldMem (by simp [frameObjects, oldMem])).2 j hj)
            (hfresh_disj_alloc j hal_j)
  · refine ⟨Nd_at, hWT_post.2.2.2, fun o ho j hj => ?_⟩
    rw [nodeExtents_eq hTr_at.1 hcell] at hj
    obtain ⟨fo, hfo_map, ho_in⟩ := List.mem_flatten.1 ho
    obtain ⟨ec, hec, rfl⟩ := List.mem_map.1 hfo_map
    rcases hfo_post_cases ec hec o ho_in with ho_old | ⟨_, rfl⟩
    · exact hAT_at o (List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨ec, hec, rfl⟩, ho_old⟩) j hj
    · rcases worldTypedIvls_allocated hWT (mem_worldTypedIvls_nodeExtents hj) with hj0 | hal_j
      · exact Or.inr (Or.inl hj0)
      · exact hdisj_old_fresh j
          (hAT_at oldMem (List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨_, hhead_mem, rfl⟩, by simp [frameObjects, oldMem]⟩) j hj)
          (hfresh_disj_alloc j hal_j)
  · have hworldRefs_eq : worldTableRefs post S = worldTableRefs s S := by
      unfold worldTableRefs recordSlots
      rw [hglob_eq "ws" (by decide), hglob_eq "bs" (by decide), hglob_eq "ts" (by decide),
          show globalTableRoots.map (globN post) = globalTableRoots.map (globN s) by
            simp only [globalTableRoots, List.map,
              hglob_eq "bal_accounts" (by decide),
              hglob_eq "bal_idx_accts" (by decide),
              hglob_eq "bal_idx_stor" (by decide)],
          balRecords_eq hWT.1 hcell (hglob_eq "bal_accounts" (by decide)),
          hglob_eq "journal_n" (by decide), hglob_eq "journal" (by decide)]
      have hws_sl : (if globN s "ws" = 0 then [] else wsTableSlots.map fun k => memW post (globN s "ws" + k)) =
          (if globN s "ws" = 0 then [] else wsTableSlots.map fun k => memW s (globN s "ws" + k)) := by
        split; · rfl
        rename_i hnz; apply List.map_congr_left; intro k hk
        exact memW_typedRec_eq hAs.2 hWT.2.2.1 hcell (sz := 40) (by decide) hnz
          (by simp only [wsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk; rcases hk with rfl | rfl <;> omega)
      have hbs_sl : (if globN s "bs" = 0 then [] else bsTableSlots.map fun k => memW post (globN s "bs" + k)) =
          (if globN s "bs" = 0 then [] else bsTableSlots.map fun k => memW s (globN s "bs" + k)) := by
        split; · rfl
        rename_i hnz; apply List.map_congr_left; intro k hk
        exact memW_typedRec_eq hAs.2 hWT.2.2.1 hcell (sz := 80) (by decide) hnz
          (by simp only [bsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk; rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
      have hts_sl : (if globN s "ts" = 0 then [] else tsTableSlots.map fun k => memW post (globN s "ts" + k)) =
          (if globN s "ts" = 0 then [] else tsTableSlots.map fun k => memW s (globN s "ts" + k)) := by
        split; · rfl
        rename_i hnz; apply List.map_congr_left; intro k hk
        exact memW_typedRec_eq hAs.2 hWT.2.2.1 hcell (sz := 72) (by decide) hnz
          (by simp only [tsTableSlots, List.mem_cons, List.not_mem_nil, or_false] at hk; rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
      have hnest_bs : (if globN s "bs" ≠ 0 ∧ memW post (globN s "bs" + 32) ∈ S then htabValues post (memW post (globN s "bs" + 32)) else []) =
          (if globN s "bs" ≠ 0 ∧ memW s (globN s "bs" + 32) ∈ S then htabValues s (memW s (globN s "bs" + 32)) else []) := by
        by_cases hnz : globN s "bs" = 0
        · simp [hnz]
        · rw [memW_typedRec_eq hAs.2 hWT.2.2.1 hcell (sz := 80) (by decide) hnz (by omega)]
          by_cases hmS : memW s (globN s "bs" + 32) ∈ S
          · simp [hnz, hmS, htabValues_eq hcell hmS (hWT.1.2.1 _ hmS).1]
          · simp [hnz, hmS]
      have hnest_ts : (if globN s "ts" ≠ 0 ∧ memW post (globN s "ts" + 32) ∈ S then htabValues post (memW post (globN s "ts" + 32)) else []) =
          (if globN s "ts" ≠ 0 ∧ memW s (globN s "ts" + 32) ∈ S then htabValues s (memW s (globN s "ts" + 32)) else []) := by
        by_cases hnz : globN s "ts" = 0
        · simp [hnz]
        · rw [memW_typedRec_eq hAs.2 hWT.2.2.1 hcell (sz := 72) (by decide) hnz (by omega)]
          by_cases hmS : memW s (globN s "ts" + 32) ∈ S
          · simp [hnz, hmS, htabValues_eq hcell hmS (hWT.1.2.1 _ hmS).1]
          · simp [hnz, hmS]
      have hbal_fl : (balRecords s).flatMap (fun ad => [memW post ad, memW post (ad + 8)]) =
          (balRecords s).flatMap (fun ad => [memW s ad, memW s (ad + 8)]) := by
        apply List.flatMap_congr; intro ad had
        have had_mem := balRecord_ivl_mem had
        rcases fixedObject_le_2pow64 hAs.2 hWT.2.2.1 (bal_in_fixedObjects had_mem) with h0 | had_bnd
        · dsimp only at h0; omega
        · dsimp only at had_bnd
          have hwti_ad := mem_worldTypedIvls_bal (S := S) (Nd := Nd_at) had_mem
          rw [memW_eq_of_cellHits hcell (by omega) hwti_ad ⟨by dsimp only; omega, by dsimp only; omega⟩,
              memW_eq_of_cellHits hcell (by omega) hwti_ad ⟨by dsimp only; omega, by dsimp only; omega⟩]
      have hjrn_mp : (List.range (globN s "journal_n")).map (fun k => memW post (globN s "journal" + 32 * k)) =
          (List.range (globN s "journal_n")).map (fun k => memW s (globN s "journal" + 32 * k)) := by
        apply List.map_congr_left; intro k hk; rw [List.mem_range] at hk
        have hjc_le := hWT.2.1.1
        have hjc_ne : globN s "journal_cap" ≠ 0 := by omega
        rcases hWT.2.1.2.2.1 with h0 | ⟨hal, _⟩
        · exact absurd h0 hjc_ne
        · have hbnd := allocated_le_2pow64 hAs.2 hal; dsimp only at hbnd
          have hkle : 32 * k + 8 ≤ 32 * globN s "journal_cap" := by omega
          exact memW_eq_of_cellHits hcell (by omega) (mem_worldTypedIvls_journal (S := S) (Nd := Nd_at) hjc_ne)
            ⟨by dsimp only; omega, by dsimp only; omega⟩
      dsimp only
      rw [hglob_eq "bs" (by decide), hglob_eq "ts" (by decide),
          hws_sl, hbs_sl, hts_sl, hnest_bs, hnest_ts, hbal_fl, hjrn_mp]
    have hdelEx_iff : ∀ i t, DelExclusive post S (evmChain s) i t ↔ DelExclusive s S (evmChain s) i t := by
      intro i t; unfold DelExclusive; rw [hworldRefs_eq]
      refine and_congr Iff.rfl (forall_congr' fun j => forall_congr' fun hj =>
        forall_congr' fun k => imp_congr_right fun hk => ?_)
      have hj_mem : (evmChain s)[j] ∈ evmChain s := List.getElem_mem _
      have hk_ok : k + 8 ≤ 280 ∧ k % 8 = 0 ∧ k ≠ 32 ∧ k ≠ 40 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl <;> exact ⟨by omega, by omega, by omega, by omega⟩
      rw [(hrec_eq _ hj_mem).1 k hk_ok.1 hk_ok.2.1 hk_ok.2.2.1 hk_ok.2.2.2]
    intro i hi
    have hi_mem : (evmChain s)[i]'(by omega) ∈ evmChain s := List.getElem_mem _
    have hm_eq := (hrec_eq _ hi_mem).2.1 48 (by omega) (by omega)
    have hmm_eq := (hrec_eq _ hi_mem).2.1 56 (by omega) (by omega)
    have he24_eq := (hrec_eq _ hi_mem).1 24 (by omega) (by omega) (by omega) (by omega)
    have htake_eq : ((evmChain s).take (i + 1)).map (fun ec => memW post (ec.1 + 136)) =
        ((evmChain s).take (i + 1)).map (fun ec => memW s (ec.1 + 136)) := by
      apply List.map_congr_left; intro ec hec
      exact (hrec_eq ec (List.mem_of_mem_take hec)).1 136 (by omega) (by omega) (by omega) (by omega)
    have hM := hMarks i hi; dsimp only at hM ⊢
    rw [hm_eq, hmm_eq, he24_eq, hfeq, htake_eq]
    obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9⟩ := hM
    refine ⟨m1, m2, m3, m4, ?_, ?_, m7, ?_, m9⟩
    · intro j hj hij
      have hj_tail : (evmChain s)[j] ∈ chTail := by
        rcases j with _ | j'
        · omega
        · simp [hch_eq]
      have hj_mem : (evmChain s)[j] ∈ evmChain s := List.getElem_mem _
      rw [hfs_eq _ hj_mem, htail_fo_eq _ hj_tail, hframeLogs_eq _ hj_mem,
          (hrec_eq _ hj_mem).1 112 (by omega) (by omega) (by omega) (by omega)]
      exact m5 j hj hij
    · rw [hfs_eq _ hi_mem]; exact m6
    · intro t ht
      rw [hfp_eq_all t ht, hdelEx_iff i t]; exact m8 t ht
  · rw [worldRoleSlots_eq hAs.2 hWT.1 hWT.2.2.1 hcell hcg,
        hframeRoleSlots_eq,
        journalRoleSlots_eq hAs.2 hWT.2.1 hWT.2.2.1 hcell hcg]
    unfold RolesOK at hRoles ⊢
    refine ⟨fun a ha => ?_, hRoles.2⟩
    obtain ⟨haS, hkl⟩ := hRoles.1 a ha
    have htb := ((hWT.1.2.1 a.1 haS).1.1 (a.1, 88) (by simp [htabFootprint])).1
    rw [htab_hdr_eq hcell haS htb 0 (by omega)]; exact ⟨haS, hkl⟩
  · have hsum_eq : ((evmChain s).map fun ec => memW post (ec.1 + 64) + memW post (ec.1 + 192)).sum =
        ((evmChain s).map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)).sum := by
      unfold evmR at hR_eq; rw [hchain_eq] at hR_eq; exact hR_eq
    rw [hsum_eq]; exact hGas


theorem lookup_ceil32 :
    originalRuntimeCode.lookup (ofString "ceil32") =
      some ([(ofString "v", .one)], sourceFnBody Guest.Software.guestFn_ceil32, .one) :=
  lookup_of_guestAst_getElem 442 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_ceil32) rfl

theorem lookup_mul64x64 :
    originalRuntimeCode.lookup (ofString "mul64x64") =
      some ([(ofString "a", .one), (ofString "b", .one)],
        sourceFnBody Guest.Software.guestFn_mul64x64, .comb [.one, .one]) :=
  lookup_of_guestAst_getElem 59 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_mul64x64) rfl

theorem lookup_memory_gas_cost :
    originalRuntimeCode.lookup (ofString "memory_gas_cost") =
      some ([(ofString "size", .one)], sourceFnBody Guest.Software.guestFn_memory_gas_cost, .one) :=
  lookup_of_guestAst_getElem 457 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_memory_gas_cost) rfl

theorem lookup_extend_memory_cost1 :
    originalRuntimeCode.lookup (ofString "extend_memory_cost1") =
      some ([(ofString "start", .comb [.one, .one, .one, .one]),
             (ofString "size", .comb [.one, .one, .one, .one])],
        sourceFnBody Guest.Software.guestFn_extend_memory_cost1, .comb [.one, .one]) :=
  lookup_of_guestAst_getElem 458 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_extend_memory_cost1) rfl

theorem lookup_extend_memory :
    originalRuntimeCode.lookup (ofString "extend_memory") =
      some ([(ofString "expand_by", .one)],
        sourceFnBody Guest.Software.guestFn_extend_memory, .one) :=
  lookup_of_guestAst_getElem 460 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_extend_memory) rfl

private theorem add_sat_body_exact {F : Type} (s : PanSemStateFiniteExact 64 F) {aw bw : BitVec 64}
    (ha : s.locals.lookup (ofString "a") = some (.val (.word aw)))
    (hb : s.locals.lookup (ofString "b") = some (.val (.word bw)))
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_add_sat)).1 =
      some (.returned v)) :
    ∃ rw : BitVec 64, v = .val (.word rw) ∧
      rw.toNat = if aw.toNat + bw.toNat < 2 ^ 64 then aw.toNat + bw.toNat else 2 ^ 64 - 1 := by
  have hbody : sourceFnBody Guest.Software.guestFn_add_sat =
      .dec (ofString "s") .one (.op .add [.var .local (ofString "a"), .var .local (ofString "b")])
        (.seq
          (.ite (.cmp .lower (.var .local (ofString "s")) (.var .local (ofString "a")))
            (.return (.const 18446744073709551615#64))
            .skip)
          (.return (.var .local (ofString "s")))) := rfl
  rw [hbody, evaluateHOLFiniteState_dec_total] at hret; dsimp only at hret
  have hsum : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x))
      (.op .add [.var .local (ofString "a"), .var .local (ofString "b")]) =
      some (.val (.word (aw + bw))) := by
    simp [evalHOLExact, evalListHOLExact, ha, hb, wordOpHOL, wordOp, valueIsWord, valueWord]
  rw [hsum] at hret; dsimp only at hret
  have hsh : shapeEqHOL .one (shapeOfHOLExact (.val (.word (aw + bw)))) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  rw [if_pos hsh] at hret; dsimp only at hret
  set s1 := setVarHOLFinite (ofString "s") (.val (.word (aw + bw))) s
  have hs1_s : s1.locals.lookup (ofString "s") = some (.val (.word (aw + bw))) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs1_a : s1.locals.lookup (ofString "a") = some (.val (.word aw)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ha,
      show ofString "s" ≠ ofString "a" by decide]
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hret
  have hcmp : @evalHOLExact 64 F _ s1.toExact (fun x => Classical.propDecidable (s1.memaddrs x))
      (.cmp .lower (.var .local (ofString "s")) (.var .local (ofString "a"))) =
      some (.val (.word (if (aw + bw) < aw then 1 else 0))) := by
    simp [evalHOLExact, hs1_s, hs1_a, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  rw [hcmp] at hret; dsimp only at hret
  have haw_lt := aw.isLt
  have hbw_lt := bw.isLt
  by_cases hlt : (aw + bw) < aw
  · have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
    simp only [hlt, ↓reduceIte, h10] at hret
    rw [evaluateHOLFiniteState_return] at hret; dsimp only [evalHOLExact] at hret
    have hsz : sizeOfShapeWithContextHOL s1.structs
        (shapeOfHOLExact (.val (.word 18446744073709551615#64))) ≤ 32 := by
      simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
    rw [if_pos hsz] at hret; dsimp only at hret
    injection hret with h1; injection h1 with hv
    refine ⟨18446744073709551615#64, hv.symm, ?_⟩
    rw [BitVec.lt_def, BitVec.toNat_add] at hlt
    have hover : ¬ (aw.toNat + bw.toNat < 2 ^ 64) := by
      intro hok; rw [Nat.mod_eq_of_lt hok] at hlt; omega
    rw [if_neg hover]; decide
  · simp only [hlt, ↓reduceIte, evaluateHOLFiniteState_skip] at hret
    rw [evaluateHOLFiniteState_return] at hret
    have hev_s : @evalHOLExact 64 F _ s1.toExact (fun x => Classical.propDecidable (s1.memaddrs x))
        (.var .local (ofString "s")) = some (.val (.word (aw + bw))) := hs1_s
    rw [hev_s] at hret; dsimp only at hret
    split at hret
    · injection hret with h1; injection h1 with hv
      refine ⟨aw + bw, hv.symm, ?_⟩
      rw [BitVec.lt_def, BitVec.toNat_add] at hlt
      have hok : aw.toNat + bw.toNat < 2 ^ 64 := by
        by_contra hover
        have hmod : (aw.toNat + bw.toNat) % 2 ^ 64 = aw.toNat + bw.toNat - 2 ^ 64 := by omega
        omega
      rw [if_pos hok, BitVec.toNat_add, Nat.mod_eq_of_lt hok]
    · simp at hret

private theorem ceil32_body_exact {F : Type} (s : PanSemStateFiniteExact 64 F) {vw : BitVec 64}
    (hcode : s.code = originalRuntimeCode)
    (hv_lk : s.locals.lookup (ofString "v") = some (.val (.word vw)))
    (ret : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_ceil32)).1 =
      some (.returned ret)) :
    ∃ cw : BitVec 64, ret = .val (.word cw) ∧
      (vw.toNat ≤ 2 ^ 64 - 32 →
        cw.toNat = ((vw.toNat + 31) / 32) * 32 ∧ vw.toNat ≤ cw.toNat ∧
        cw.toNat ≤ 2 ^ 64 - 32 ∧ cw.toNat % 32 = 0 ∧ (vw.toNat % 32 = 0 → cw.toNat = vw.toNat)) ∧
      (2 ^ 64 - 31 ≤ vw.toNat → cw.toNat = 2 ^ 64 - 1) := by
  have hbody : sourceFnBody Guest.Software.guestFn_ceil32 =
      .dec (ofString "r") .one (.op .and [.var .local (ofString "v"), .const 31#64])
        (.seq
          (.ite (.cmp .equal (.var .local (ofString "r")) (.const 0#64))
            (.return (.var .local (ofString "v")))
            .skip)
          (.decCall (ofString "s") .one (ofString "add_sat")
            [.var .local (ofString "v"), .op .sub [.const 32#64, .var .local (ofString "r")]]
            (.return (.var .local (ofString "s"))))) := rfl
  rw [hbody, evaluateHOLFiniteState_dec_total] at hret; dsimp only at hret
  have hand : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x))
      (.op .and [.var .local (ofString "v"), .const 31#64]) =
      some (.val (.word (vw &&& 31#64))) := by
    simp [evalHOLExact, evalListHOLExact, hv_lk, wordOpHOL, wordOp, valueIsWord, valueWord]
    rfl
  rw [hand] at hret; dsimp only at hret
  have hsh_r : shapeEqHOL .one (shapeOfHOLExact (.val (.word (vw &&& 31#64)))) = true := by
    simp [shapeEqHOL, shapeOfHOLExact]
  rw [if_pos hsh_r] at hret; dsimp only at hret
  set rw := vw &&& 31#64
  have hrw_nat : rw.toNat = vw.toNat % 32 := by
    change (vw &&& 31#64).toNat = vw.toNat % 32
    rw [BitVec.toNat_and, show (31#64 : BitVec 64).toNat = 2 ^ 5 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  set s1 := setVarHOLFinite (ofString "r") (.val (.word rw)) s
  have hs1_r : s1.locals.lookup (ofString "r") = some (.val (.word rw)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hs1_v : s1.locals.lookup (ofString "v") = some (.val (.word vw)) := by
    simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hv_lk,
      show ofString "r" ≠ ofString "v" by decide]
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hret
  have hcmp : @evalHOLExact 64 F _ s1.toExact (fun x => Classical.propDecidable (s1.memaddrs x))
      (.cmp .equal (.var .local (ofString "r")) (.const 0#64)) =
      some (.val (.word (if rw = 0#64 then 1 else 0))) := by
    simp [evalHOLExact, hs1_r, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  rw [hcmp] at hret; dsimp only at hret
  have hvw_lt := vw.isLt
  by_cases hr0 : rw = 0#64
  · have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
    simp only [hr0, ↓reduceIte, h10] at hret
    rw [evaluateHOLFiniteState_return] at hret
    have hev_v : @evalHOLExact 64 F _ s1.toExact (fun x => Classical.propDecidable (s1.memaddrs x))
        (.var .local (ofString "v")) = some (.val (.word vw)) := hs1_v
    rw [hev_v] at hret; dsimp only at hret
    have hsz : sizeOfShapeWithContextHOL s1.structs
        (shapeOfHOLExact (.val (.word vw))) ≤ 32 := by
      simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
    rw [if_pos hsz] at hret; dsimp only at hret
    injection hret with h1; injection h1 with hv
    have hmod0 : vw.toNat % 32 = 0 := by rw [← hrw_nat, hr0]; rfl
    refine ⟨vw, hv.symm, ?_, ?_⟩
    · intro hle; exact ⟨by omega, le_rfl, hle, hmod0, fun _ => rfl⟩
    · intro hge; omega
  · simp only [hr0, ↓reduceIte, evaluateHOLFiniteState_skip] at hret
    have hmod_pos : 0 < vw.toNat % 32 := by
      rw [← hrw_nat]
      by_contra hz
      apply hr0
      apply BitVec.eq_of_toNat_eq
      change rw.toNat = 0; omega
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hret
    have hargs : evalListHOLFinite s1 (h := fun x => Classical.propDecidable (s1.memaddrs x))
        [.var .local (ofString "v"), .op .sub [.const 32#64, .var .local (ofString "r")]] =
        some [.val (.word vw), .val (.word (32#64 - rw))] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hs1_v, hs1_r, wordOpHOL, wordOp, valueIsWord, valueWord]
    rw [hargs] at hret; dsimp only at hret
    have hlk := pan_two_word_lookup s1.code.lookup (ofString "add_sat") (ofString "a") (ofString "b")
      (sourceFnBody Guest.Software.guestFn_add_sat) vw (32#64 - rw) (by decide)
      (by change s.code.lookup _ = _; rw [hcode]; exact lookup_add_sat)
    rw [hlk] at hret; dsimp only at hret
    split at hret
    · simp at hret
    · let cal := (HolFiniteMapExact.empty.update (ofString "a", ValueHOL.val (.word vw))).update
        (ofString "b", ValueHOL.val (.word (32#64 - rw)))
      rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s1 cal)
          (sourceFnBody Guest.Software.guestFn_add_sat) with ⟨rb, pb⟩
      rw [hrun] at hret
      rcases rb with _ | rb
      · simp at hret
      · cases rb with
        | returned vb =>
          dsimp only at hret
          split at hret
          · dsimp only at hret
            have ha_lk : (callEntryStateHOLFinite s1 cal).locals.lookup (ofString "a") = some (.val (.word vw)) := by
              have hne : ofString "b" ≠ ofString "a" := by decide
              simp [cal, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne]
            have hb_lk : (callEntryStateHOLFinite s1 cal).locals.lookup (ofString "b") = some (.val (.word (32#64 - rw))) := by
              simp [cal, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
            obtain ⟨sw, rfl, hsw_nat⟩ := add_sat_body_exact (callEntryStateHOLFinite s1 cal) ha_lk hb_lk vb
              (by rw [hrun])
            set cs := setVarHOLFinite (ofString "s") (.val (.word sw)) { pb with locals := s1.locals }
            rw [evaluateHOLFiniteState_return] at hret
            have hev_s : @evalHOLExact 64 F _ cs.toExact (fun x => Classical.propDecidable (cs.memaddrs x))
                (.var .local (ofString "s")) = some (.val (.word sw)) := by
              simp [evalHOLExact, cs, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
            rw [hev_s] at hret; dsimp only at hret
            split at hret
            · injection hret with h1; injection h1 with hv
              have hsub_nat : (32#64 - rw).toNat = 32 - vw.toNat % 32 := by
                have hle_rw : rw.toNat ≤ 32 := by omega
                rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr hle_rw), hrw_nat]
                rfl
              rw [hsub_nat] at hsw_nat
              refine ⟨sw, hv.symm, ?_, ?_⟩
              · intro hle
                have hok : vw.toNat + (32 - vw.toNat % 32) < 2 ^ 64 := by omega
                rw [if_pos hok] at hsw_nat
                refine ⟨by omega, by omega, by omega, by omega, fun hm => by omega⟩
              · intro hge
                have hover : ¬ (vw.toNat + (32 - vw.toNat % 32) < 2 ^ 64) := by omega
                rw [if_neg hover] at hsw_nat
                exact hsw_nat
            · simp at hret
          · simp at hret
        | _ => simp at hret

private theorem eval_mul64x64_hi_nonzero {F : Type}
    (s : PanSemStateFiniteExact 64 F) {ww : BitVec 64}
    (hw_ge : 2 ^ 32 ≤ ww.toNat) (hw_lt : ww.toNat < 2 ^ 59)
    (ha : s.locals.lookup (ofString "a") = some (.val (.word ww)))
    (hb : s.locals.lookup (ofString "b") = some (.val (.word ww)))
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_mul64x64)).1 =
      some (.returned v)) :
    ∃ lo hi : BitVec 64, v = .rStruct [.val (.word lo), .val (.word hi)] ∧ hi ≠ 0#64 := by
  have hbody : sourceFnBody Guest.Software.guestFn_mul64x64 =
      .dec (ofString "a0") .one (.op .and [.var .local (ofString "a"), .const (4294967295#64)])
        (.dec (ofString "a1") .one (.shift .lsr (.var .local (ofString "a")) (.const (32#64)))
          (.dec (ofString "b0") .one (.op .and [.var .local (ofString "b"), .const (4294967295#64)])
            (.dec (ofString "b1") .one (.shift .lsr (.var .local (ofString "b")) (.const (32#64)))
              (.dec (ofString "p00") .one (.panop .mul [.var .local (ofString "a0"), .var .local (ofString "b0")])
                (.dec (ofString "p11") .one (.panop .mul [.var .local (ofString "a1"), .var .local (ofString "b1")])
                  (.dec (ofString "mid") (.comb [.one, .one]) (.rstruct [.const (0#64), .const (0#64)])
                    (.seq
                      (.primitive (ofString "mid") .addCarry
                        [.panop .mul [.var .local (ofString "a0"), .var .local (ofString "b1")],
                         .panop .mul [.var .local (ofString "a1"), .var .local (ofString "b0")],
                         .const (0#64)])
                      (.dec (ofString "lo") (.comb [.one, .one]) (.rstruct [.const (0#64), .const (0#64)])
                        (.seq
                          (.primitive (ofString "lo") .addCarry
                            [.var .local (ofString "p00"),
                             .shift .lsl (.rfield 0 (.var .local (ofString "mid"))) (.const (32#64)),
                             .const (0#64)])
                          (.dec (ofString "hi") .one
                            (.op .add
                              [.var .local (ofString "p11"),
                               .shift .lsr (.rfield 0 (.var .local (ofString "mid"))) (.const (32#64)),
                               .shift .lsl (.rfield 1 (.var .local (ofString "mid"))) (.const (32#64)),
                               .rfield 1 (.var .local (ofString "lo"))])
                            (.return (.rstruct [.rfield 0 (.var .local (ofString "lo")), .var .local (ofString "hi")])))))))))))) := rfl
  let a0 := ww &&& 4294967295#64
  let a1 := ww >>> (32 : Nat)
  let p00 := a0 * a0
  let p11 := a1 * a1
  let p01 := a0 * a1
  let mid := wordAddCarryHOL p01 p01 0#64
  let lo := wordAddCarryHOL p00 (mid.1 <<< (32 : Nat)) 0#64
  let hi := p11 + (mid.1 >>> (32 : Nat)) + (mid.2 <<< (32 : Nat)) + lo.2
  have h32 : (32#64 : BitVec 64).toNat = 32 := rfl
  have hand_w : wordOpHOL .and [ww, 4294967295#64] = some a0 := rfl
  have hlsr_w : wordShiftHOL .lsr ww 32 = some a1 := by simp [wordShiftHOL, a1]
  have hpo_mid : panPrimopHOLExact PrimOp.addCarry
      ([.val (.word p01), .val (.word p01), .val (.word 0#64)] : List (ValueHOL 64)) =
      some (.rStruct [.val (.word mid.1), .val (.word mid.2)]) := by
    simp [panPrimopHOLExact, mid]
  have hlsl_mid0 : wordShiftHOL .lsl mid.1 32 = some (mid.1 <<< (32 : Nat)) := by simp [wordShiftHOL]
  have hlsr_mid0 : wordShiftHOL .lsr mid.1 32 = some (mid.1 >>> (32 : Nat)) := by simp [wordShiftHOL]
  have hlsl_mid1 : wordShiftHOL .lsl mid.2 32 = some (mid.2 <<< (32 : Nat)) := by simp [wordShiftHOL]
  have hpo_lo : panPrimopHOLExact PrimOp.addCarry
      ([.val (.word p00), .val (.word (mid.1 <<< (32 : Nat))), .val (.word 0#64)] : List (ValueHOL 64)) =
      some (.rStruct [.val (.word lo.1), .val (.word lo.2)]) := by
    simp [panPrimopHOLExact, lo]
  have hadd4 : wordOpHOL .add [p11, mid.1 >>> (32 : Nat), mid.2 <<< (32 : Nat), lo.2] = some hi := by
    simp [wordOpHOL, wordOp, hi, BitVec.add_assoc]
  have hlk_eq {st : PanSemStateFiniteExact 64 F} (k : MlS) (u : ValueHOL 64) :
      (setVarHOLFinite k u st).locals.lookup k = some u := by
    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hlk_ne {st : PanSemStateFiniteExact 64 F} (k1 k2 : MlS) (u : ValueHOL 64) (hne : k1 ≠ k2) :
      (setVarHOLFinite k1 u st).locals.lookup k2 = st.locals.lookup k2 := by
    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne]
  have step_dec : ∀ {nm : MlS} {sh : ShapeHOL} {e : ExpHOL 64} {b : ProgHOL 64}
      {st : PanSemStateFiniteExact 64 F} {u : ValueHOL 64},
      @evalHOLExact 64 F _ st.toExact (fun x => Classical.propDecidable (st.memaddrs x)) e = some u →
      shapeEqHOL sh (shapeOfHOLExact u) = true →
      (evaluateHOLFiniteState st (.dec nm sh e b)).1 =
        (evaluateHOLFiniteState (setVarHOLFinite nm u st) b).1 := by
    intro nm sh e b st u hev hsh
    rw [evaluateHOLFiniteState_dec_total]; dsimp only
    rw [hev]; dsimp only; rw [if_pos hsh]
  have step_prim : ∀ {nm : MlS} {op : PrimOp} {args : List (ExpHOL 64)} {tl : ProgHOL 64}
      {st : PanSemStateFiniteExact 64 F} {vals : List (ValueHOL 64)} {u : ValueHOL 64},
      @evalListHOLExact 64 F _ st.toExact (fun x => Classical.propDecidable (st.memaddrs x)) args = some vals →
      panPrimopHOLExact op vals = some u →
      st.isValidValueHOLFinite .local nm u = true →
      (evaluateHOLFiniteState st (.seq (.primitive nm op args) tl)).1 =
        (evaluateHOLFiniteState (setVarHOLFinite nm u st) tl).1 := by
    intro nm op args tl st vals u hargs hpo hval
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_primitive, hargs]; dsimp only
    rw [hpo]; dsimp only; rw [if_pos hval]
  have hsh1 : ∀ w : BitVec 64, shapeEqHOL .one (shapeOfHOLExact (.val (.word w) : ValueHOL 64)) = true :=
    fun _ => by simp [shapeEqHOL, shapeOfHOLExact]
  have hsh2 : shapeEqHOL (.comb [.one, .one]) (shapeOfHOLExact (.rStruct [.val (.word (0#64)), .val (.word (0#64))] : ValueHOL 64)) = true := by
    simp [shapeEqHOL, shapeEqHOL.shapeEqListHOL, shapeOfHOLExact]
  rw [hbody] at hret
  rw [step_dec (u := .val (.word a0)) (by simp [evalHOLExact, evalListHOLExact, ha, valueIsWord, valueWord, hand_w]) (hsh1 _)] at hret
  set s1 := setVarHOLFinite (ofString "a0") (.val (.word a0)) s
  have hs1_a0 : s1.locals.lookup (ofString "a0") = some (.val (.word a0)) := hlk_eq _ _
  have hs1_a : s1.locals.lookup (ofString "a") = some (.val (.word ww)) := by
    rw [hlk_ne (ofString "a0") (ofString "a") _ (by decide)]; exact ha
  have hs1_b : s1.locals.lookup (ofString "b") = some (.val (.word ww)) := by
    rw [hlk_ne (ofString "a0") (ofString "b") _ (by decide)]; exact hb
  rw [step_dec (u := .val (.word a1)) (by simp [evalHOLExact, hs1_a, h32, hlsr_w]) (hsh1 _)] at hret
  set s2 := setVarHOLFinite (ofString "a1") (.val (.word a1)) s1
  have hs2_a1 : s2.locals.lookup (ofString "a1") = some (.val (.word a1)) := hlk_eq _ _
  have hs2_a0 : s2.locals.lookup (ofString "a0") = some (.val (.word a0)) := by
    rw [hlk_ne (ofString "a1") (ofString "a0") _ (by decide)]; exact hs1_a0
  have hs2_b : s2.locals.lookup (ofString "b") = some (.val (.word ww)) := by
    rw [hlk_ne (ofString "a1") (ofString "b") _ (by decide)]; exact hs1_b
  rw [step_dec (u := .val (.word a0)) (by simp [evalHOLExact, evalListHOLExact, hs2_b, valueIsWord, valueWord, hand_w]) (hsh1 _)] at hret
  set s3 := setVarHOLFinite (ofString "b0") (.val (.word a0)) s2
  have hs3_b0 : s3.locals.lookup (ofString "b0") = some (.val (.word a0)) := hlk_eq _ _
  have hs3_a1 : s3.locals.lookup (ofString "a1") = some (.val (.word a1)) := by
    rw [hlk_ne (ofString "b0") (ofString "a1") _ (by decide)]; exact hs2_a1
  have hs3_a0 : s3.locals.lookup (ofString "a0") = some (.val (.word a0)) := by
    rw [hlk_ne (ofString "b0") (ofString "a0") _ (by decide)]; exact hs2_a0
  have hs3_b : s3.locals.lookup (ofString "b") = some (.val (.word ww)) := by
    rw [hlk_ne (ofString "b0") (ofString "b") _ (by decide)]; exact hs2_b
  rw [step_dec (u := .val (.word a1)) (by simp [evalHOLExact, hs3_b, h32, hlsr_w]) (hsh1 _)] at hret
  set s4 := setVarHOLFinite (ofString "b1") (.val (.word a1)) s3
  have hs4_b1 : s4.locals.lookup (ofString "b1") = some (.val (.word a1)) := hlk_eq _ _
  have hs4_b0 : s4.locals.lookup (ofString "b0") = some (.val (.word a0)) := by
    rw [hlk_ne (ofString "b1") (ofString "b0") _ (by decide)]; exact hs3_b0
  have hs4_a1 : s4.locals.lookup (ofString "a1") = some (.val (.word a1)) := by
    rw [hlk_ne (ofString "b1") (ofString "a1") _ (by decide)]; exact hs3_a1
  have hs4_a0 : s4.locals.lookup (ofString "a0") = some (.val (.word a0)) := by
    rw [hlk_ne (ofString "b1") (ofString "a0") _ (by decide)]; exact hs3_a0
  rw [step_dec (u := .val (.word p00)) (by simp [evalHOLExact, evalListHOLExact, hs4_a0, hs4_b0, valueIsWord, valueWord, panOpHOL, p00]) (hsh1 _)] at hret
  set s5 := setVarHOLFinite (ofString "p00") (.val (.word p00)) s4
  have hs5_p00 : s5.locals.lookup (ofString "p00") = some (.val (.word p00)) := hlk_eq _ _
  have hs5_b1 : s5.locals.lookup (ofString "b1") = some (.val (.word a1)) := by
    rw [hlk_ne (ofString "p00") (ofString "b1") _ (by decide)]; exact hs4_b1
  have hs5_b0 : s5.locals.lookup (ofString "b0") = some (.val (.word a0)) := by
    rw [hlk_ne (ofString "p00") (ofString "b0") _ (by decide)]; exact hs4_b0
  have hs5_a1 : s5.locals.lookup (ofString "a1") = some (.val (.word a1)) := by
    rw [hlk_ne (ofString "p00") (ofString "a1") _ (by decide)]; exact hs4_a1
  have hs5_a0 : s5.locals.lookup (ofString "a0") = some (.val (.word a0)) := by
    rw [hlk_ne (ofString "p00") (ofString "a0") _ (by decide)]; exact hs4_a0
  rw [step_dec (u := .val (.word p11)) (by simp [evalHOLExact, evalListHOLExact, hs5_a1, hs5_b1, valueIsWord, valueWord, panOpHOL, p11]) (hsh1 _)] at hret
  set s6 := setVarHOLFinite (ofString "p11") (.val (.word p11)) s5
  have hs6_p11 : s6.locals.lookup (ofString "p11") = some (.val (.word p11)) := hlk_eq _ _
  have hs6_p00 : s6.locals.lookup (ofString "p00") = some (.val (.word p00)) := by
    rw [hlk_ne (ofString "p11") (ofString "p00") _ (by decide)]; exact hs5_p00
  have hs6_b1 : s6.locals.lookup (ofString "b1") = some (.val (.word a1)) := by
    rw [hlk_ne (ofString "p11") (ofString "b1") _ (by decide)]; exact hs5_b1
  have hs6_b0 : s6.locals.lookup (ofString "b0") = some (.val (.word a0)) := by
    rw [hlk_ne (ofString "p11") (ofString "b0") _ (by decide)]; exact hs5_b0
  have hs6_a1 : s6.locals.lookup (ofString "a1") = some (.val (.word a1)) := by
    rw [hlk_ne (ofString "p11") (ofString "a1") _ (by decide)]; exact hs5_a1
  have hs6_a0 : s6.locals.lookup (ofString "a0") = some (.val (.word a0)) := by
    rw [hlk_ne (ofString "p11") (ofString "a0") _ (by decide)]; exact hs5_a0
  rw [step_dec (u := .rStruct [.val (.word 0#64), .val (.word 0#64)]) (by simp [evalHOLExact, evalListHOLExact]) hsh2] at hret
  set s7 := setVarHOLFinite (ofString "mid") (.rStruct [.val (.word 0#64), .val (.word 0#64)]) s6
  have hs7_mid : s7.locals.lookup (ofString "mid") = some (.rStruct [.val (.word 0#64), .val (.word 0#64)]) := hlk_eq _ _
  have hs7_p11 : s7.locals.lookup (ofString "p11") = some (.val (.word p11)) := by
    rw [hlk_ne (ofString "mid") (ofString "p11") _ (by decide)]; exact hs6_p11
  have hs7_p00 : s7.locals.lookup (ofString "p00") = some (.val (.word p00)) := by
    rw [hlk_ne (ofString "mid") (ofString "p00") _ (by decide)]; exact hs6_p00
  have hs7_b1 : s7.locals.lookup (ofString "b1") = some (.val (.word a1)) := by
    rw [hlk_ne (ofString "mid") (ofString "b1") _ (by decide)]; exact hs6_b1
  have hs7_b0 : s7.locals.lookup (ofString "b0") = some (.val (.word a0)) := by
    rw [hlk_ne (ofString "mid") (ofString "b0") _ (by decide)]; exact hs6_b0
  have hs7_a1 : s7.locals.lookup (ofString "a1") = some (.val (.word a1)) := by
    rw [hlk_ne (ofString "mid") (ofString "a1") _ (by decide)]; exact hs6_a1
  have hs7_a0 : s7.locals.lookup (ofString "a0") = some (.val (.word a0)) := by
    rw [hlk_ne (ofString "mid") (ofString "a0") _ (by decide)]; exact hs6_a0
  have hp10 : a1 * a0 = p01 := BitVec.mul_comm a1 a0
  rw [step_prim
    (by simp [evalListHOLExact, evalHOLExact, hs7_a0, hs7_a1, hs7_b0, hs7_b1, valueIsWord, valueWord, panOpHOL, p01, hp10])
    hpo_mid
    (by simp [isValidValueHOLFinite, lookupKvarHOLFinite, hs7_mid, shapeEqHOL, shapeEqHOL.shapeEqListHOL, shapeOfHOLExact])] at hret
  set s8 := setVarHOLFinite (ofString "mid") (.rStruct [.val (.word mid.1), .val (.word mid.2)]) s7
  have hs8_mid : s8.locals.lookup (ofString "mid") = some (.rStruct [.val (.word mid.1), .val (.word mid.2)]) := hlk_eq _ _
  have hs8_p11 : s8.locals.lookup (ofString "p11") = some (.val (.word p11)) := by
    rw [hlk_ne (ofString "mid") (ofString "p11") _ (by decide)]; exact hs7_p11
  have hs8_p00 : s8.locals.lookup (ofString "p00") = some (.val (.word p00)) := by
    rw [hlk_ne (ofString "mid") (ofString "p00") _ (by decide)]; exact hs7_p00
  rw [step_dec (u := .rStruct [.val (.word 0#64), .val (.word 0#64)]) (by simp [evalHOLExact, evalListHOLExact]) hsh2] at hret
  set s9 := setVarHOLFinite (ofString "lo") (.rStruct [.val (.word 0#64), .val (.word 0#64)]) s8
  have hs9_lo : s9.locals.lookup (ofString "lo") = some (.rStruct [.val (.word 0#64), .val (.word 0#64)]) := hlk_eq _ _
  have hs9_mid : s9.locals.lookup (ofString "mid") = some (.rStruct [.val (.word mid.1), .val (.word mid.2)]) := by
    rw [hlk_ne (ofString "lo") (ofString "mid") _ (by decide)]; exact hs8_mid
  have hs9_p11 : s9.locals.lookup (ofString "p11") = some (.val (.word p11)) := by
    rw [hlk_ne (ofString "lo") (ofString "p11") _ (by decide)]; exact hs8_p11
  have hs9_p00 : s9.locals.lookup (ofString "p00") = some (.val (.word p00)) := by
    rw [hlk_ne (ofString "lo") (ofString "p00") _ (by decide)]; exact hs8_p00
  rw [step_prim
    (by simp [evalListHOLExact, evalHOLExact, hs9_p00, hs9_mid, h32, hlsl_mid0])
    hpo_lo
    (by simp [isValidValueHOLFinite, lookupKvarHOLFinite, hs9_lo, shapeEqHOL, shapeEqHOL.shapeEqListHOL, shapeOfHOLExact])] at hret
  set s10 := setVarHOLFinite (ofString "lo") (.rStruct [.val (.word lo.1), .val (.word lo.2)]) s9
  have hs10_lo : s10.locals.lookup (ofString "lo") = some (.rStruct [.val (.word lo.1), .val (.word lo.2)]) := hlk_eq _ _
  have hs10_mid : s10.locals.lookup (ofString "mid") = some (.rStruct [.val (.word mid.1), .val (.word mid.2)]) := by
    rw [hlk_ne (ofString "lo") (ofString "mid") _ (by decide)]; exact hs9_mid
  have hs10_p11 : s10.locals.lookup (ofString "p11") = some (.val (.word p11)) := by
    rw [hlk_ne (ofString "lo") (ofString "p11") _ (by decide)]; exact hs9_p11
  rw [step_dec (u := .val (.word hi))
    (by simp [evalHOLExact, evalListHOLExact, hs10_p11, hs10_mid, hs10_lo, valueIsWord, valueWord, h32, hlsr_mid0, hlsl_mid1, hadd4]) (hsh1 _)] at hret
  set s11 := setVarHOLFinite (ofString "hi") (.val (.word hi)) s10
  have hs11_hi : s11.locals.lookup (ofString "hi") = some (.val (.word hi)) := hlk_eq _ _
  have hs11_lo : s11.locals.lookup (ofString "lo") = some (.rStruct [.val (.word lo.1), .val (.word lo.2)]) := by
    rw [hlk_ne (ofString "hi") (ofString "lo") _ (by decide)]; exact hs10_lo
  rw [evaluateHOLFiniteState_return] at hret
  have hev_ret : @evalHOLExact 64 F _ s11.toExact (fun a => Classical.propDecidable (s11.memaddrs a))
      (.rstruct [.rfield 0 (.var .local (ofString "lo")), .var .local (ofString "hi")]) =
      some (.rStruct [.val (.word lo.1), .val (.word hi)]) := by
    simp [evalHOLExact, evalListHOLExact, hs11_lo, hs11_hi]
  rw [hev_ret] at hret; dsimp only at hret
  have hsz : sizeOfShapeWithContextHOL s11.structs
      (shapeOfHOLExact (.rStruct [.val (.word lo.1), .val (.word hi)] : ValueHOL 64)) ≤ 32 := by
    simp [shapeOfHOLExact, sizeOfShapeWithContextHOL, sizeOfShapesWithContextHOL]
  rw [if_pos hsz] at hret; dsimp only at hret
  injection hret with h1; injection h1 with hv
  refine ⟨lo.1, hi, hv.symm, ?_⟩
  have ha1_nat : a1.toNat = ww.toNat / 2 ^ 32 := by
    dsimp only [a1]; rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have ha1_pos : 1 ≤ a1.toNat := by omega
  have ha1_lt : a1.toNat < 2 ^ 27 := by
    have : (2 ^ 59 : Nat) = 2 ^ 27 * 2 ^ 32 := by decide
    omega
  have hp11_lt : a1.toNat * a1.toNat < 2 ^ 54 := by
    have hmul : a1.toNat * a1.toNat < 2 ^ 27 * 2 ^ 27 := Nat.mul_lt_mul'' ha1_lt ha1_lt
    have : (2 ^ 27 : Nat) * 2 ^ 27 = 2 ^ 54 := by decide
    omega
  have hp11_nat : p11.toNat = a1.toNat * a1.toNat := by
    dsimp only [p11]; rw [BitVec.toNat_mul, Nat.mod_eq_of_lt (by omega)]
  have hp11_pos : 1 ≤ p11.toNat := by
    rw [hp11_nat]; exact Nat.mul_le_mul ha1_pos ha1_pos
  have hmid0_lsr : (mid.1 >>> (32 : Nat)).toNat < 2 ^ 32 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have := mid.1.isLt
    have : (2 ^ 64 : Nat) = 2 ^ 32 * 2 ^ 32 := by decide
    omega
  have hcarry_bit : ∀ x y z : BitVec 64, (wordAddCarryHOL x y z).2 = 0 ∨ (wordAddCarryHOL x y z).2 = 1 := by
    intro x y z; unfold wordAddCarryHOL; split_ifs <;> simp <;> omega
  have hmid2_le : mid.2.toNat ≤ 1 := by
    rcases hcarry_bit p01 p01 0#64 with h | h
    · dsimp only [mid]; rw [h]; decide
    · dsimp only [mid]; rw [h]; decide
  have hmid2_lsl : (mid.2 <<< (32 : Nat)).toNat ≤ 2 ^ 32 := by
    rw [BitVec.toNat_shiftLeft]
    have : mid.2.toNat <<< 32 = mid.2.toNat * 2 ^ 32 := Nat.shiftLeft_eq mid.2.toNat 32
    rw [this, Nat.mod_eq_of_lt (by omega)]
    omega
  have hlo2_le : lo.2.toNat ≤ 1 := by
    rcases hcarry_bit p00 (mid.1 <<< (32 : Nat)) 0#64 with h | h
    · dsimp only [lo]; rw [h]; decide
    · dsimp only [lo]; rw [h]; decide
  have hhi_pos : 0 < hi.toNat := by
    dsimp only [hi]
    have hsum1 : (p11 + (mid.1 >>> (32 : Nat))).toNat = p11.toNat + (mid.1 >>> (32 : Nat)).toNat := by
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
    have hsum2 : (p11 + (mid.1 >>> (32 : Nat)) + (mid.2 <<< (32 : Nat))).toNat =
        p11.toNat + (mid.1 >>> (32 : Nat)).toNat + (mid.2 <<< (32 : Nat)).toNat := by
      rw [BitVec.toNat_add, hsum1, Nat.mod_eq_of_lt (by omega)]
    have hsum3 : (p11 + (mid.1 >>> (32 : Nat)) + (mid.2 <<< (32 : Nat)) + lo.2).toNat =
        p11.toNat + (mid.1 >>> (32 : Nat)).toNat + (mid.2 <<< (32 : Nat)).toNat + lo.2.toNat := by
      rw [BitVec.toNat_add, hsum2, Nat.mod_eq_of_lt (by omega)]
    omega
  intro hz; rw [hz] at hhi_pos; simp at hhi_pos

private theorem words_of_ge_of_ge {F : Type}
    (s : PanSemStateFiniteExact 64 F) {nw : BitVec 64}
    (hn_ge : 2 ^ 37 ≤ nw.toNat)
    (hcode : s.code = originalRuntimeCode)
    (hn : s.locals.lookup (ofString "n") = some (.val (.word nw)))
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_words_of)).1 =
      some (.returned v)) :
    ∃ ww : BitVec 64, v = .val (.word ww) ∧ 2 ^ 32 ≤ ww.toNat ∧ ww.toNat < 2 ^ 59 := by
  have hbody : sourceFnBody Guest.Software.guestFn_words_of =
      .decCall (ofString "c") .one (ofString "ceil32") [.var .local (ofString "n")]
        (.return (.shift .lsr (.var .local (ofString "c")) (.const 5#64))) := rfl
  rw [hbody, evaluateHOLFiniteState_decCall_fixClockRewrite] at hret
  have hargs : evalListHOLFinite s (h := fun x => Classical.propDecidable (s.memaddrs x))
      [.var .local (ofString "n")] = some [.val (.word nw)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hn]
  rw [hargs] at hret; dsimp only at hret
  have hlk := pan_one_word_lookup s.code.lookup (ofString "ceil32") (ofString "v")
    (sourceFnBody Guest.Software.guestFn_ceil32) nw
    (by rw [hcode]; exact lookup_ceil32)
  rw [hlk] at hret; dsimp only at hret
  split at hret
  · simp at hret
  · let cal := HolFiniteMapExact.empty.update (ofString "v", ValueHOL.val (.word nw))
    rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s cal)
        (sourceFnBody Guest.Software.guestFn_ceil32) with ⟨rb, pb⟩
    rw [hrun] at hret
    rcases rb with _ | rb
    · simp at hret
    · cases rb with
      | returned vb =>
        dsimp only at hret
        split at hret
        · dsimp only at hret
          have hv_lk : (callEntryStateHOLFinite s cal).locals.lookup (ofString "v") =
              some (.val (.word nw)) := by
            simp [cal, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          obtain ⟨cw, rfl, hlo, hhi⟩ := ceil32_body_exact (callEntryStateHOLFinite s cal) hcode hv_lk vb
            (by rw [hrun])
          have hcw_ge : 2 ^ 37 ≤ cw.toNat := by
            by_cases hle : nw.toNat ≤ 2 ^ 64 - 32
            · have := (hlo hle).1; omega
            · have := hhi (by omega); omega
          set cs := setVarHOLFinite (ofString "c") (.val (.word cw)) { pb with locals := s.locals }
          rw [evaluateHOLFiniteState_return] at hret
          have hcs_c : cs.locals.lookup (ofString "c") = some (.val (.word cw)) := by
            simp [cs, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          have h5 : (5#64 : BitVec 64).toNat = 5 := rfl
          have hshf : wordShiftHOL .lsr cw 5 = some (cw >>> (5 : Nat)) := by simp [wordShiftHOL]
          have hev : @evalHOLExact 64 F _ cs.toExact (fun a => Classical.propDecidable (cs.memaddrs a))
              (.shift .lsr (.var .local (ofString "c")) (.const 5#64)) =
              some (.val (.word (cw >>> (5 : Nat)))) := by
            simp [evalHOLExact, hcs_c, h5, hshf]
          rw [hev] at hret; dsimp only at hret
          split at hret
          · injection hret with h1; injection h1 with hv
            refine ⟨cw >>> (5 : Nat), hv.symm, ?_, ?_⟩
            · rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
              have : (2 ^ 37 : Nat) = 2 ^ 32 * 2 ^ 5 := by decide
              omega
            · rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
              have := cw.isLt
              have : (2 ^ 64 : Nat) = 2 ^ 59 * 2 ^ 5 := by decide
              omega
          · simp at hret
        · simp at hret
      | _ => simp at hret

private theorem memory_gas_cost_ge_twoPow37 {F : Type}
    (s : PanSemStateFiniteExact 64 F) {szw : BitVec 64}
    (hsz_ge : 2 ^ 37 ≤ szw.toNat)
    (hcode : s.code = originalRuntimeCode)
    (hsz_lk : s.locals.lookup (ofString "size") = some (.val (.word szw)))
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_memory_gas_cost)).1 =
      some (.returned v)) :
    v = .val (.word 18446744073709551615#64) := by
  have hbody : sourceFnBody Guest.Software.guestFn_memory_gas_cost =
      .decCall (ofString "w") .one (ofString "words_of") [.var .local (ofString "size")]
        (.decCall (ofString "sq") (.comb [.one, .one]) (ofString "mul64x64")
          [.var .local (ofString "w"), .var .local (ofString "w")]
          (.seq
            (.ite (.cmp .notEqual (.rfield 1 (.var .local (ofString "sq"))) (.const 0#64))
              (.return (.const 18446744073709551615#64))
              .skip)
            (.decCall (ofString "a") .one (ofString "add_sat")
              [.panop .mul [.var .local (ofString "w"), .const 3#64],
               .shift .lsr (.rfield 0 (.var .local (ofString "sq"))) (.const 9#64)]
              (.return (.var .local (ofString "a")))))) := rfl
  rw [hbody, evaluateHOLFiniteState_decCall_fixClockRewrite] at hret
  have hargs1 : evalListHOLFinite s (h := fun x => Classical.propDecidable (s.memaddrs x))
      [.var .local (ofString "size")] = some [.val (.word szw)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hsz_lk]
  rw [hargs1] at hret; dsimp only at hret
  have hlk1 := pan_one_word_lookup s.code.lookup (ofString "words_of") (ofString "n")
    (sourceFnBody Guest.Software.guestFn_words_of) szw
    (by rw [hcode]; exact lookup_words_of)
  rw [hlk1] at hret; dsimp only at hret
  split at hret
  · simp at hret
  · let cal1 := HolFiniteMapExact.empty.update (ofString "n", ValueHOL.val (.word szw))
    rcases hrun1 : evaluateHOLFiniteState (callEntryStateHOLFinite s cal1)
        (sourceFnBody Guest.Software.guestFn_words_of) with ⟨rb1, pb1⟩
    rw [hrun1] at hret
    have hpb1_code : pb1.code = originalRuntimeCode := by
      have hm := (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s cal1)
        (sourceFnBody Guest.Software.guestFn_words_of)).1
      rw [hrun1] at hm; exact hm.trans hcode
    rcases rb1 with _ | rb1
    · simp at hret
    · cases rb1 with
      | returned vb1 =>
        dsimp only at hret
        split at hret
        · dsimp only at hret
          have hn1 : (callEntryStateHOLFinite s cal1).locals.lookup (ofString "n") =
              some (.val (.word szw)) := by
            simp [cal1, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          obtain ⟨ww, rfl, hww_ge, hww_lt⟩ :=
            words_of_ge_of_ge (callEntryStateHOLFinite s cal1) hsz_ge hcode hn1 vb1 (by rw [hrun1])
          set s1 := setVarHOLFinite (ofString "w") (.val (.word ww)) { pb1 with locals := s.locals }
          have hs1_w : s1.locals.lookup (ofString "w") = some (.val (.word ww)) := by
            simp [s1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          have hs1_code : s1.code = originalRuntimeCode := hpb1_code
          rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hret
          have hargs2 : evalListHOLFinite s1 (h := fun x => Classical.propDecidable (s1.memaddrs x))
              [.var .local (ofString "w"), .var .local (ofString "w")] =
              some [.val (.word ww), .val (.word ww)] := by
            simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hs1_w]
          rw [hargs2] at hret; dsimp only at hret
          have hlk2 : lookupCodeHOLFinite s1.code.lookup (ofString "mul64x64")
              [.val (.word ww), .val (.word ww)] =
              some (sourceFnBody Guest.Software.guestFn_mul64x64,
                (HolFiniteMapExact.empty.update (ofString "a", ValueHOL.val (.word ww))).update
                  (ofString "b", ValueHOL.val (.word ww)),
                .comb [.one, .one]) := by
            have hd : ofString "a" ≠ ofString "b" := by decide
            have raw : lookupCodeHOLExact s1.code.lookup (ofString "mul64x64")
                [.val (.word ww), .val (.word ww)] =
                some (sourceFnBody Guest.Software.guestFn_mul64x64,
                  (fun key => if key = ofString "b" then some (.val (.word ww))
                    else if key = ofString "a" then some (.val (.word ww)) else none),
                  .comb [.one, .one]) := by
              simp [lookupCodeHOLExact, hs1_code, lookup_mul64x64, shapeOfHOLExact, shapeEqHOL, hd]
            unfold PanSemStateFiniteExact.lookupCodeHOLFinite
            split
            · rename_i missing; rw [raw] at missing; cases missing
            · rename_i foundBody foundLocals foundShape found
              have equal := Option.some.inj (found.symm.trans raw)
              obtain ⟨rfl, rest⟩ := Prod.mk.inj equal
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj rest
              apply congrArg (fun locals => some (sourceFnBody Guest.Software.guestFn_mul64x64, locals, ShapeHOL.comb [.one, .one]))
              apply HolFiniteMapExact.ext
              funext key
              by_cases hb_k : key = ofString "b"
              · subst key; simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY]
              · have hb_k' : ofString "b" ≠ key := Ne.symm hb_k
                by_cases ha_k : key = ofString "a"
                · subst key; simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY, hd, Ne.symm hd]
                · have ha_k' : ofString "a" ≠ key := Ne.symm ha_k
                  simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY, ha_k, hb_k, ha_k', hb_k']
          rw [hlk2] at hret; dsimp only at hret
          split at hret
          · simp at hret
          · let cal2 := (HolFiniteMapExact.empty.update (ofString "a", ValueHOL.val (.word ww))).update
              (ofString "b", ValueHOL.val (.word ww))
            rcases hrun2 : evaluateHOLFiniteState (callEntryStateHOLFinite s1 cal2)
                (sourceFnBody Guest.Software.guestFn_mul64x64) with ⟨rb2, pb2⟩
            rw [hrun2] at hret
            rcases rb2 with _ | rb2
            · simp at hret
            · cases rb2 with
              | returned vb2 =>
                dsimp only at hret
                split at hret
                · dsimp only at hret
                  have ha2 : (callEntryStateHOLFinite s1 cal2).locals.lookup (ofString "a") =
                      some (.val (.word ww)) := by
                    have hne : ofString "b" ≠ ofString "a" := by decide
                    simp [cal2, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne]
                  have hb2 : (callEntryStateHOLFinite s1 cal2).locals.lookup (ofString "b") =
                      some (.val (.word ww)) := by
                    simp [cal2, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                  obtain ⟨low, hiw, rfl, hhi_ne0⟩ :=
                    eval_mul64x64_hi_nonzero (callEntryStateHOLFinite s1 cal2) hww_ge hww_lt ha2 hb2 vb2 (by rw [hrun2])
                  set s2 := setVarHOLFinite (ofString "sq")
                    (.rStruct [.val (.word low), .val (.word hiw)]) { pb2 with locals := s1.locals }
                  have hs2_sq : s2.locals.lookup (ofString "sq") =
                      some (.rStruct [.val (.word low), .val (.word hiw)]) := by
                    simp [s2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hret
                  have h10 : ¬ ((1#64 : BitVec 64) = 0) := by decide
                  have hcmp : @evalHOLExact 64 F _ s2.toExact (fun x => Classical.propDecidable (s2.memaddrs x))
                      (.cmp .notEqual (.rfield 1 (.var .local (ofString "sq"))) (.const 0#64)) =
                      some (.val (.word 1#64)) := by
                    simp [evalHOLExact, hs2_sq, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hhi_ne0]
                  rw [hcmp] at hret; dsimp only at hret
                  rw [if_neg h10] at hret
                  rw [evaluateHOLFiniteState_return] at hret; dsimp only [evalHOLExact] at hret
                  have hsz : sizeOfShapeWithContextHOL s2.structs
                      (shapeOfHOLExact (.val (.word 18446744073709551615#64))) ≤ 32 := by
                    simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
                  rw [if_pos hsz] at hret; dsimp only at hret
                  injection hret with h1; injection h1 with hv; exact hv.symm
                · simp at hret
              | _ => simp at hret
        · simp at hret
      | _ => simp at hret

private theorem extend_memory_cost1_body_bounds {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (hcode : s.code = originalRuntimeCode)
    (v : ValueHOL 64)
    (hret : (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_extend_memory_cost1)).1 =
      some (.returned v)) :
    ∃ cw ebw : BitVec 64,
      v = .rStruct [.val (.word cw), .val (.word ebw)] ∧
      (ebw = 0#64 ∨
        ∃ before after : Nat,
          after < 2 ^ 37 ∧
          after % 32 = 0 ∧
          before < after ∧
          ebw.toNat = after - before ∧
          (memW s (globN s "ev" + 32) % 32 = 0 → before = memW s (globN s "ev" + 32))) := by
  have hbody : sourceFnBody Guest.Software.guestFn_extend_memory_cost1 =
      .decCall (ofString "z") .one (ofString "u256_is_zero") [.var .local (ofString "size")]
        (.seq
          (.ite (.cmp .notEqual (.var .local (ofString "z")) (.const 0#64))
            (.return (.rstruct [.const 0#64, .const 0#64]))
            .skip)
          (.decCall (ofString "s") .one (ofString "sat_word") [.var .local (ofString "start")]
            (.decCall (ofString "n") .one (ofString "sat_word") [.var .local (ofString "size")]
              (.decCall (ofString "endp") .one (ofString "add_sat") [.var .local (ofString "s"), .var .local (ofString "n")]
                (.seq
                  (.ite (.cmp .equal (.var .local (ofString "endp")) (.const 18446744073709551615#64))
                    (.return (.rstruct [.const 18446744073709551615#64, .const 0#64]))
                    .skip)
                  (.dec (ofString "cur") .one (.load .one (.op .add [.var .global (ofString "ev"), .const 32#64]))
                    (.decCall (ofString "before") .one (ofString "ceil32") [.var .local (ofString "cur")]
                      (.decCall (ofString "after") .one (ofString "ceil32") [.var .local (ofString "endp")]
                        (.seq
                          (.ite (.cmp .notLower (.var .local (ofString "before")) (.var .local (ofString "after")))
                            (.return (.rstruct [.const 0#64, .const 0#64]))
                            .skip)
                          (.decCall (ofString "ca") .one (ofString "memory_gas_cost") [.var .local (ofString "after")]
                            (.decCall (ofString "cb") .one (ofString "memory_gas_cost") [.var .local (ofString "before")]
                              (.seq
                                (.ite (.cmp .equal (.var .local (ofString "ca")) (.const 18446744073709551615#64))
                                  (.return (.rstruct [.const 18446744073709551615#64, .const 0#64]))
                                  .skip)
                                (.return (.rstruct
                                  [.op .sub [.var .local (ofString "ca"), .var .local (ofString "cb")],
                                   .op .sub [.var .local (ofString "after"), .var .local (ofString "before")]])))))))))))))) := rfl
  have hret_rstruct : ∀ (st : PanSemStateFiniteExact 64 F) (w1 w2 : BitVec 64),
      evaluateHOLFiniteState st (.return (.rstruct [.const w1, .const w2])) =
        (some (.returned (.rStruct [.val (.word w1), .val (.word w2)])), st.emptyLocalsHOLFinite) := by
    intro st w1 w2
    rw [evaluateHOLFiniteState_return]
    have hev : @evalHOLExact 64 F _ st.toExact (fun x => Classical.propDecidable (st.memaddrs x))
        (.rstruct [.const w1, .const w2]) =
        some (.rStruct [.val (.word w1), .val (.word w2)]) := by
      simp [evalHOLExact, evalListHOLExact]
    rw [hev]; dsimp only
    have hsz : sizeOfShapeWithContextHOL st.structs
        (shapeOfHOLExact (.rStruct [.val (.word w1), .val (.word w2)] : ValueHOL 64)) ≤ 32 := by
      simp [shapeOfHOLExact, sizeOfShapeWithContextHOL, sizeOfShapesWithContextHOL]
    rw [if_pos hsz]
  have step_ro_call : ∀ {st : PanSemStateFiniteExact 64 F} {nm fname : MlS} {args : List (ExpHOL 64)} {cont : ProgHOL 64},
      opRoCallees fname = true →
      st.code = originalRuntimeCode →
      LocFrame s st →
      (evaluateHOLFiniteState st (.decCall nm .one fname args cont)).1 = some (.returned v) →
      ∃ (w : BitVec 64) (st' : PanSemStateFiniteExact 64 F),
        st'.code = originalRuntimeCode ∧
        LocFrame s st' ∧
        st'.locals = st.locals.update (nm, .val (.word w)) ∧
        (∃ vals body callee rs,
          evalListHOLFinite st (h := fun x => Classical.propDecidable (st.memaddrs x)) args = some vals ∧
          lookupCodeHOLFinite originalRuntimeCode.lookup fname vals = some (body, callee, rs) ∧
          (evaluateHOLFiniteState (callEntryStateHOLFinite st callee) body).1 = some (.returned (.val (.word w)))) ∧
        (evaluateHOLFiniteState st' cont).1 = some (.returned v) := by
    intro st nm fname args cont hfn hst_c hst_lf hr
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hr
    rcases hargs : evalListHOLFinite st (h := fun x => Classical.propDecidable (st.memaddrs x)) args with _ | vals
    · rw [hargs] at hr; simp at hr
    · rw [hargs] at hr; dsimp only at hr
      rcases hl : lookupCodeHOLFinite st.code.lookup fname vals with _ | ⟨body, callee, rs⟩
      · rw [hl] at hr; simp at hr
      · rw [hl] at hr; dsimp only at hr
        split at hr
        · simp at hr
        · have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup fname vals = some (body, callee, rs) := by
            rwa [← hst_c]
          have hbody_ro := opRoCallees_good fname hfn vals body callee rs hl_orig
          have hsafe := evaluate_readOnlyProg opRoCallees opRoCallees_good body hbody_ro
            (callEntryStateHOLFinite st callee) hst_c
          rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite st callee) body with ⟨rb, pb⟩
          rw [hrun] at hr
          have hpb_c : pb.code = originalRuntimeCode := by
            have hm := (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite st callee) body).1
            rw [hrun] at hm; exact hm.trans hst_c
          rcases rb with _ | rb
          · simp at hr
          · cases rb with
            | returned vb =>
              dsimp only at hr
              split at hr
              · rename_i hsh_vb
                dsimp only at hr
                have hsh_one : shapeEqHOL (shapeOfHOLExact vb) .one = true := by
                  simp [Bool.and_eq_true] at hsh_vb; exact hsh_vb.1
                rcases vb with ⟨⟨w⟩⟩ | _ | _
                · have hlf_ce : LocFrame (callEntryStateHOLFinite st callee) pb := by
                    have hres := hsafe.to_resumes (by rw [hrun]; exact Or.inl ⟨.val (.word w), rfl⟩)
                    simpa [hrun] using hres
                  have hlf_st : LocFrame st pb := by
                    unfold LocFrame at hlf_ce ⊢; rw [hlf_ce]; rfl
                  let st' := setVarHOLFinite nm (.val (.word w)) { pb with locals := st.locals }
                  have hlf_st' : LocFrame s st' :=
                    hst_lf.trans (hlf_st.with_locals_clock (st.locals.update (nm, .val (.word w))) pb.clock)
                  exact ⟨w, st', hpb_c, hlf_st', rfl,
                    ⟨vals, body, callee, rs, rfl, hl_orig, by rw [hrun]⟩, hr⟩
                · simp [shapeOfHOLExact, shapeEqHOL] at hsh_one
                · simp [shapeOfHOLExact, shapeEqHOL] at hsh_one
              · simp at hr
            | _ => simp at hr
  have h10 : ¬ ((1#64 : BitVec 64) = 0) := by decide
  have h00 : (0#64 : BitVec 64) = 0 := rfl
  rw [hbody] at hret
  obtain ⟨zw, s1, hs1_c, hs1_lf, hs1_loc, _, hr1⟩ :=
    step_ro_call (by decide) hcode (LocFrame.refl s) hret
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hr1
  have hs1_z : s1.locals.lookup (ofString "z") = some (.val (.word zw)) := by
    rw [hs1_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hcmp_z : @evalHOLExact 64 F _ s1.toExact (fun x => Classical.propDecidable (s1.memaddrs x))
      (.cmp .notEqual (.var .local (ofString "z")) (.const 0#64)) =
      some (.val (.word (if zw ≠ 0#64 then (1#64 : BitVec 64) else 0#64))) := by
    simp [evalHOLExact, hs1_z, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  rw [hcmp_z] at hr1; dsimp only at hr1
  by_cases hzw : zw ≠ 0#64
  · rw [if_pos hzw] at hr1; rw [if_neg h10] at hr1; rw [hret_rstruct s1 0#64 0#64] at hr1
    injection hr1 with h1; injection h1 with hv
    exact ⟨0#64, 0#64, hv.symm, Or.inl rfl⟩
  · rw [if_neg hzw] at hr1; rw [if_pos h00] at hr1; rw [evaluateHOLFiniteState_skip] at hr1; dsimp only at hr1
    obtain ⟨sw, s2, hs2_c, hs2_lf, hs2_loc, _, hr2⟩ :=
      step_ro_call (by decide) hs1_c hs1_lf hr1
    obtain ⟨nw, s3, hs3_c, hs3_lf, hs3_loc, _, hr3⟩ :=
      step_ro_call (by decide) hs2_c hs2_lf hr2
    obtain ⟨endpw, s4, hs4_c, hs4_lf, hs4_loc, _, hr4⟩ :=
      step_ro_call (by decide) hs3_c hs3_lf hr3
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hr4
    have hs4_endp : s4.locals.lookup (ofString "endp") = some (.val (.word endpw)) := by
      rw [hs4_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
    have hcmp_endp : @evalHOLExact 64 F _ s4.toExact (fun x => Classical.propDecidable (s4.memaddrs x))
        (.cmp .equal (.var .local (ofString "endp")) (.const 18446744073709551615#64)) =
        some (.val (.word (if endpw = 18446744073709551615#64 then (1#64 : BitVec 64) else 0#64))) := by
      simp [evalHOLExact, hs4_endp, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    rw [hcmp_endp] at hr4; dsimp only at hr4
    by_cases hendp : endpw = 18446744073709551615#64
    · rw [if_pos hendp] at hr4; rw [if_neg h10] at hr4; rw [hret_rstruct s4 18446744073709551615#64 0#64] at hr4
      injection hr4 with h1; injection h1 with hv
      exact ⟨18446744073709551615#64, 0#64, hv.symm, Or.inl rfl⟩
    · rw [if_neg hendp] at hr4; rw [if_pos h00] at hr4; rw [evaluateHOLFiniteState_skip] at hr4; dsimp only at hr4
      rw [evaluateHOLFiniteState_dec_total] at hr4; dsimp only at hr4
      rcases hld_cur : @evalHOLExact 64 F _ s4.toExact (fun x => Classical.propDecidable (s4.memaddrs x))
          (.load .one (.op .add [.var .global (ofString "ev"), .const 32#64])) with _ | curv
      · rw [hld_cur] at hr4; simp at hr4
      · obtain ⟨curw, rfl, hcurw_nat⟩ := evalAt_loadG_word s4 "ev" 32#64 curv hld_cur
        rw [hld_cur] at hr4; dsimp only at hr4
        have hsh_cur : shapeEqHOL .one (shapeOfHOLExact (.val (.word curw))) = true := by
          simp [shapeEqHOL, shapeOfHOLExact]
        rw [if_pos hsh_cur] at hr4; dsimp only at hr4
        have hs4_mem : s4.memory = s.memory := by unfold LocFrame at hs4_lf; conv_lhs => rw [hs4_lf]
        have hs4_glob : s4.globals = s.globals := by unfold LocFrame at hs4_lf; conv_lhs => rw [hs4_lf]
        have hcur_eq : curw.toNat = memW s (globN s "ev" + 32) := by
          have h32 : (32#64 : BitVec 64).toNat = 32 := rfl
          rw [hcurw_nat, h32]
          simp [memW, globN, hs4_mem, hs4_glob]
        set s5 := setVarHOLFinite (ofString "cur") (.val (.word curw)) s4 with hs5_def
        have hs5_c : s5.code = originalRuntimeCode := hs4_c
        have hs5_lf : LocFrame s s5 := hs4_lf.with_locals_clock _ s4.clock
        have hs5_cur : s5.locals.lookup (ofString "cur") = some (.val (.word curw)) := by
          simp [hs5_def, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        obtain ⟨befw, s6, hs6_c, hs6_lf, hs6_loc, ⟨vals6, body6, cal6, rs6, hargs6, hl6, hrun6⟩, hr6⟩ :=
          step_ro_call (by decide) hs5_c hs5_lf hr4
        have hvals6 : vals6 = [.val (.word curw)] := by
          simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hs5_cur] at hargs6
          exact hargs6.symm
        subst hvals6
        obtain ⟨rfl, rfl, curw', hcur_inj, hcal6_v⟩ := one_word_arg_lookup lookup_ceil32 hl6
        injection hcur_inj with hcur_inj'; injection hcur_inj' with hcur_inj''; subst hcur_inj''
        have hbef_ex := ceil32_body_exact (callEntryStateHOLFinite s5 cal6) hs5_c hcal6_v
          (.val (.word befw)) hrun6
        obtain ⟨befw', hbef_inj, hbef_lo, hbef_hi⟩ := hbef_ex
        injection hbef_inj with hbef_inj'; injection hbef_inj' with hbef_inj''; subst hbef_inj''
        have hs6_endp : s6.locals.lookup (ofString "endp") = some (.val (.word endpw)) := by
          rw [hs6_loc]; simp [hs5_def, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs4_endp,
            show ofString "before" ≠ ofString "endp" by decide,
            show ofString "cur" ≠ ofString "endp" by decide]
        obtain ⟨aftw, s7, hs7_c, hs7_lf, hs7_loc, ⟨vals7, body7, cal7, rs7, hargs7, hl7, hrun7⟩, hr7⟩ :=
          step_ro_call (by decide) hs6_c hs6_lf hr6
        have hvals7 : vals7 = [.val (.word endpw)] := by
          simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hs6_endp] at hargs7
          exact hargs7.symm
        subst hvals7
        obtain ⟨rfl, rfl, endpw', hendp_inj, hcal7_v⟩ := one_word_arg_lookup lookup_ceil32 hl7
        injection hendp_inj with hendp_inj'; injection hendp_inj' with hendp_inj''; subst hendp_inj''
        obtain ⟨aftw', haft_inj, haft_lo, haft_hi⟩ := ceil32_body_exact (callEntryStateHOLFinite s6 cal7) hs6_c
          hcal7_v (.val (.word aftw)) hrun7
        injection haft_inj with haft_inj'; injection haft_inj' with haft_inj''; subst haft_inj''
        have hs7_bef : s7.locals.lookup (ofString "before") = some (.val (.word befw)) := by
          rw [hs7_loc, hs6_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "after" ≠ ofString "before" by decide]
        have hs7_aft : s7.locals.lookup (ofString "after") = some (.val (.word aftw)) := by
          rw [hs7_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hr7
        have hcmp_ba : @evalHOLExact 64 F _ s7.toExact (fun x => Classical.propDecidable (s7.memaddrs x))
            (.cmp .notLower (.var .local (ofString "before")) (.var .local (ofString "after"))) =
            some (.val (.word (if ¬ (befw < aftw) then (1#64 : BitVec 64) else 0#64))) := by
          simp [evalHOLExact, hs7_bef, hs7_aft, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
        rw [hcmp_ba] at hr7; dsimp only at hr7
        by_cases hba : ¬ (befw < aftw)
        · rw [if_pos hba] at hr7; rw [if_neg h10] at hr7; rw [hret_rstruct s7 0#64 0#64] at hr7
          injection hr7 with h1; injection h1 with hv
          exact ⟨0#64, 0#64, hv.symm, Or.inl rfl⟩
        · rw [if_neg hba] at hr7; rw [if_pos h00] at hr7; rw [evaluateHOLFiniteState_skip] at hr7; dsimp only at hr7
          have hba_lt : befw.toNat < aftw.toNat := BitVec.lt_def.1 (Classical.not_not.1 hba)
          obtain ⟨caw, s8, hs8_c, hs8_lf, hs8_loc, ⟨vals8, body8, cal8, rs8, hargs8, hl8, hrun8⟩, hr8⟩ :=
            step_ro_call (by decide) hs7_c hs7_lf hr7
          have hvals8 : vals8 = [.val (.word aftw)] := by
            simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hs7_aft] at hargs8
            exact hargs8.symm
          subst hvals8
          obtain ⟨rfl, rfl, aftw_arg, haft_arg_inj, hcal8_sz⟩ := one_word_arg_lookup lookup_memory_gas_cost hl8
          injection haft_arg_inj with h1; injection h1 with h2; subst h2
          obtain ⟨cbw, s9, hs9_c, hs9_lf, hs9_loc, _, hr9⟩ :=
            step_ro_call (by decide) hs8_c hs8_lf hr8
          have hs9_ca : s9.locals.lookup (ofString "ca") = some (.val (.word caw)) := by
            rw [hs9_loc, hs8_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE,
              show ofString "cb" ≠ ofString "ca" by decide]
          have hs9_cb : s9.locals.lookup (ofString "cb") = some (.val (.word cbw)) := by
            rw [hs9_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
          have hs9_bef : s9.locals.lookup (ofString "before") = some (.val (.word befw)) := by
            rw [hs9_loc, hs8_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs7_bef,
              show ofString "cb" ≠ ofString "before" by decide,
              show ofString "ca" ≠ ofString "before" by decide]
          have hs9_aft : s9.locals.lookup (ofString "after") = some (.val (.word aftw)) := by
            rw [hs9_loc, hs8_loc]; simp [HolFiniteMapExact.lookup_update, FUPDATE, hs7_aft,
              show ofString "cb" ≠ ofString "after" by decide,
              show ofString "ca" ≠ ofString "after" by decide]
          rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hr9
          have hcmp_ca : @evalHOLExact 64 F _ s9.toExact (fun x => Classical.propDecidable (s9.memaddrs x))
              (.cmp .equal (.var .local (ofString "ca")) (.const 18446744073709551615#64)) =
              some (.val (.word (if caw = 18446744073709551615#64 then (1#64 : BitVec 64) else 0#64))) := by
            simp [evalHOLExact, hs9_ca, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
          rw [hcmp_ca] at hr9; dsimp only at hr9
          by_cases hca_max : caw = 18446744073709551615#64
          · rw [if_pos hca_max] at hr9; rw [if_neg h10] at hr9; rw [hret_rstruct s9 18446744073709551615#64 0#64] at hr9
            injection hr9 with h1; injection h1 with hv
            exact ⟨18446744073709551615#64, 0#64, hv.symm, Or.inl rfl⟩
          · rw [if_neg hca_max] at hr9; rw [if_pos h00] at hr9; rw [evaluateHOLFiniteState_skip] at hr9; dsimp only at hr9
            rw [evaluateHOLFiniteState_return] at hr9
            have hev_ret : @evalHOLExact 64 F _ s9.toExact (fun x => Classical.propDecidable (s9.memaddrs x))
                (.rstruct
                  [.op .sub [.var .local (ofString "ca"), .var .local (ofString "cb")],
                   .op .sub [.var .local (ofString "after"), .var .local (ofString "before")]]) =
                some (.rStruct [.val (.word (caw - cbw)), .val (.word (aftw - befw))]) := by
              simp [evalHOLExact, evalListHOLExact, hs9_ca, hs9_cb, hs9_aft, hs9_bef,
                wordOpHOL, wordOp, valueIsWord, valueWord]
            rw [hev_ret] at hr9; dsimp only at hr9
            have hsz : sizeOfShapeWithContextHOL s9.structs
                (shapeOfHOLExact (.rStruct [.val (.word (caw - cbw)), .val (.word (aftw - befw))] : ValueHOL 64)) ≤ 32 := by
              simp [shapeOfHOLExact, sizeOfShapeWithContextHOL, sizeOfShapesWithContextHOL]
            rw [if_pos hsz] at hr9; dsimp only at hr9
            injection hr9 with h1; injection h1 with hv
            have haft_lt37 : aftw.toNat < 2 ^ 37 := by
              by_contra hge
              have hca_eq := memory_gas_cost_ge_twoPow37 (callEntryStateHOLFinite s7 cal8)
                (Nat.le_of_not_lt hge) hs7_c hcal8_sz (.val (.word caw)) hrun8
              injection hca_eq with h1; injection h1 with h2
              exact hca_max h2
            have hendp_le : endpw.toNat ≤ 2 ^ 64 - 32 := by
              by_contra hgt
              have haft_max_nat := haft_hi (by omega)
              omega
            have haft_eq := haft_lo hendp_le
            have haft_mod : aftw.toNat % 32 = 0 := by omega
            have hcur_le : curw.toNat ≤ 2 ^ 64 - 32 := by
              by_contra hgt
              have := hbef_hi (by omega)
              omega
            have hbef_eq := hbef_lo hcur_le
            have hsub_nat : (aftw - befw).toNat = aftw.toNat - befw.toNat :=
              BitVec.toNat_sub_of_le (BitVec.le_def.2 (Nat.le_of_lt hba_lt))
            refine ⟨caw - cbw, aftw - befw, hv.symm, Or.inr ⟨befw.toNat, aftw.toNat, haft_lt37, haft_mod, hba_lt, hsub_nat, ?_⟩⟩
            intro hcur_al
            rw [← hcur_eq] at hcur_al ⊢
            omega

/-- `extend_memory_cost1` is read-only and returns `[cw, ebw]` where either `ebw = 0` or
    `ebw = after - before` with `after < 2^37`, `after % 32 = 0`, `before < after`,
    and `before = mem_len` whenever `mem_len % 32 = 0`. -/
theorem eps_extend_memory_cost1_bounds :
    EvmPreservingSpec (fun _ => True)
      (fun s v post =>
        LocFrame s post ∧
        ∃ cw ebw : BitVec 64,
          v = .rStruct [.val (.word cw), .val (.word ebw)] ∧
          (ebw = 0#64 ∨
            ∃ before after : Nat,
              after < 2 ^ 37 ∧
              after % 32 = 0 ∧
              before < after ∧
              ebw.toNat = after - before ∧
              (memW s (globN s "ev" + 32) % 32 = 0 → before = memW s (globN s "ev" + 32))))
      (ofString "extend_memory_cost1") := by
  obtain ⟨params, body, retShape, hlk, hro⟩ := eps_extend_memory_cost1
  have hlk_eq := lookup_extend_memory_cost1.symm.trans hlk
  injection hlk_eq with hprod
  rcases Prod.mk.inj hprod with ⟨rfl, hprod2⟩
  rcases Prod.mk.inj hprod2 with ⟨hbody_eq, rfl⟩
  subst hbody_eq
  refine ⟨_, _, _, lookup_extend_memory_cost1, ?_⟩
  intro F s hcode hInv hP hlookup hnt
  have hs := hro s hcode hInv hP hlookup hnt
  dsimp only at hs ⊢
  refine ⟨fun v hv => ?_, hs.2⟩
  obtain ⟨h1, h2, h3, hlf⟩ := hs.1 v hv
  exact ⟨h1, h2, h3, hlf, extend_memory_cost1_body_bounds s hcode v hv⟩

/-! ## `extend_memory` and `op_keccak` specs -/

/-- Head-frame EVM memory layout condition for `extend_memory`:
    `ev + 32` (`mem_len`) is 32-byte aligned, and the current memory buffer ends at `frame_mem_ptr`
    (`mem + mem_cap = frame_mem_ptr`). -/
def HeadMemAligned {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  memW s (globN s "ev" + 32) % 32 = 0 ∧
  (memW s (globN s "ev" + 24) + memW s (globN s "ev" + 40) = globN s "frame_mem_ptr")

/-- Precondition for `extend_memory(expand_by)`: `expand_by` is a word bounded so that
    `mem_len + expand_by < 2^37` (so `nlen + 1024` does not wrap `BitVec 64`), `(mem_len + expand_by) % 8 = 0`,
    and either `expand_by = 0` or `mem + mem_cap = frame_mem_ptr`. -/
def ExtendMemoryPre {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ ebw : BitVec 64,
    s.locals.lookup (ofString "expand_by") = some (.val (.word ebw)) ∧
    (ebw = 0#64 ∨
      (memW s (globN s "ev" + 32) + ebw.toNat < 2 ^ 37 ∧
       (memW s (globN s "ev" + 32) + ebw.toNat) % 8 = 0 ∧
       memW s (globN s "ev" + 24) + memW s (globN s "ev" + 40) = globN s "frame_mem_ptr"))

theorem eps_extend_memory_aligned :
    EvmPreservingSpec ExtendMemoryPre
      (fun s _ post => ∀ g : String, ofString g ≠ ofString "frame_mem_ptr" → globN post g = globN s g)
      (ofString "extend_memory") := by
  refine ⟨_, _, _, lookup_extend_memory, ?_⟩
  intro F s hcode hInv ⟨ebw, heb_loc, heb_cond⟩ _ hnt
  have herr_triv : ∀ {P1 P2 : Prop},
      (∀ v, (some PanSemResultExact.error : Option (PanSemResultExact 64)) = some (.returned v) → P1) ∧
      (IsEvmErr (some PanSemResultExact.error) → P2) := by
    intro _ _; constructor
    · intro _ h; cases h
    · rintro ⟨_, h⟩; cases h
  have hhead_mem : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by simp [evmChain, evmChainFrom]
  have hFW0 := hInv.2.choose_spec.2.2.2.2.1 _ hhead_mem
  have hb_ev := (frameWF_bounds hInv.1.2 hFW0).1
  dsimp only at hb_ev
  have hev_pos : 0 < globN s "ev" := by
    obtain ⟨hin1, _⟩ := (hFW0.1 (globN s "ev", 280) (by simp)).1
    have h1 := hInv.1.2.2.2.1; have h2 := hInv.1.2.2.2.2.1
    rw [R11Shards.scratchStart_val] at h1; dsimp only at hin1; omega
  obtain ⟨evw, hevw, hevw_nat⟩ := global_word_of_pos s "ev" hev_pos
  obtain ⟨hp_w, fp_w, sp_g_w, hhp_lk, hhp_nat, hfp_lk, hfp_nat, hsp_g_lk, hsp_g_nat⟩ :=
    Wave8Contracts.M26.arenaOK_globals s hInv.1.2
  let growBranch : ProgHOL 64 :=
    .dec (ofString "ncap") .one (.panop .mul [.var .local (ofString "cap"), .const 2#64])
      (.seq
        (.ite (.cmp .lower (.var .local (ofString "ncap")) (.var .local (ofString "nlen")))
          (.assign .local (ofString "ncap") (.op .add [.var .local (ofString "nlen"), .const 1024#64]))
          .skip)
        (.seq
          (.call (some (none, none)) (ofString "frame_mem_alloc")
            [.op .sub [.var .local (ofString "ncap"), .var .local (ofString "cap")]])
          (.seq
            (.call (some (none, none)) (ofString "memzero")
              [.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]), .var .local (ofString "cap")],
               .op .sub [.var .local (ofString "ncap"), .var .local (ofString "cap")]])
            (.store (.op .add [.var .global (ofString "ev"), .const 40#64]) (.var .local (ofString "ncap"))))))
  let tailProg : ProgHOL 64 :=
    .seq
      (.call (some (none, none)) (ofString "memzero")
        [.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]), .var .local (ofString "len")],
         .var .local (ofString "expand_by")])
      (.seq
        (.store (.op .add [.var .global (ofString "ev"), .const 32#64]) (.var .local (ofString "nlen")))
        (.return (.const 0#64)))
  have hbody : sourceFnBody Guest.Software.guestFn_extend_memory =
      .seq
        (.ite (.cmp .equal (.var .local (ofString "expand_by")) (.const 0#64))
          (.return (.const 0#64))
          .skip)
        (.dec (ofString "len") .one (.load .one (.op .add [.var .global (ofString "ev"), .const 32#64]))
          (.dec (ofString "cap") .one (.load .one (.op .add [.var .global (ofString "ev"), .const 40#64]))
            (.dec (ofString "nlen") .one (.op .add [.var .local (ofString "len"), .var .local (ofString "expand_by")])
              (.seq
                (.ite (.cmp .lower (.var .local (ofString "cap")) (.var .local (ofString "nlen")))
                  growBranch
                  .skip)
                tailProg)))) := rfl
  dsimp only
  rw [hbody] at hnt ⊢
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt ⊢
  have hcmp_eb0 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .equal (.var .local (ofString "expand_by")) (.const 0#64)) =
      some (.val (.word (if ebw = 0#64 then 1 else 0))) := by
    simp [evalHOLExact, heb_loc, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  rw [hcmp_eb0] at hnt ⊢; dsimp only at hnt ⊢
  have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
  by_cases heb0 : ebw = 0#64
  · simp only [heb0, ↓reduceIte, h10] at hnt ⊢
    rw [evaluateHOLFiniteState_return]
    have hc0 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) (.const 0#64) =
        some (.val (.word 0#64)) := rfl
    rw [hc0]; dsimp only
    have hsz0 : sizeOfShapeWithContextHOL s.structs
        (shapeOfHOLExact (.val (.word 0#64))) ≤ 32 := by
      simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
    rw [if_pos hsz0]; dsimp only
    have hInv_el : EvmInv s.emptyLocalsHOLFinite := localsFree_evmInv s _ s.clock hInv
    have hc_el := evm_congr (s := s) (t := s.emptyLocalsHOLFinite) rfl rfl
    have hch_el : evmChain s.emptyLocalsHOLFinite = evmChain s := evmChain_congr rfl rfl
    exact ⟨fun _ _ => ⟨hInv_el, hch_el, le_of_eq hc_el.2.1, fun _ _ => rfl⟩,
           by rintro ⟨_, h⟩; cases h⟩
  · rcases heb_cond with rfl | ⟨hnlen_bound, hnlen_al8, hmem_end_fp⟩
    · exact absurd rfl heb0
    have heb_pos : 0 < ebw.toNat := by
      by_contra hz
      apply heb0
      apply BitVec.eq_of_toNat_eq
      have : (0#64 : BitVec 64).toNat = 0 := rfl
      omega
    simp only [heb0, ↓reduceIte, evaluateHOLFiniteState_skip] at hnt ⊢
    rw [evaluateHOLFiniteState_dec_total] at hnt ⊢; dsimp only at hnt ⊢
    rcases hload_len : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.load .one (.op .add [.var .global (ofString "ev"), .const 32#64])) with _ | vlen
    · exact herr_triv
    · simp only [hload_len] at hnt ⊢
      obtain ⟨lenw, rfl, hlenw_eq⟩ := evalAt_loadG_word s "ev" 32#64 vlen hload_len
      have h32_n : (32#64 : BitVec 64).toNat = 32 := rfl
      rw [h32_n] at hlenw_eq
      have hsh_len : shapeEqHOL .one (shapeOfHOLExact (.val (.word lenw))) = true := by
        simp [shapeEqHOL, shapeOfHOLExact]
      rw [if_pos hsh_len] at hnt ⊢; dsimp only at hnt ⊢
      set s1 := setVarHOLFinite (ofString "len") (.val (.word lenw)) s with hs1
      rw [evaluateHOLFiniteState_dec_total] at hnt ⊢; dsimp only at hnt ⊢
      rcases hload_cap : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
          (.load .one (.op .add [.var .global (ofString "ev"), .const 40#64])) with _ | vcap
      · exact herr_triv
      · simp only [hload_cap] at hnt ⊢
        obtain ⟨capw, rfl, hcapw_eq⟩ := evalAt_loadG_word s1 "ev" 40#64 vcap hload_cap
        have h40_n : (40#64 : BitVec 64).toNat = 40 := rfl
        have hs1_gm : memW s1 (globN s1 "ev" + 40) = memW s (globN s "ev" + 40) := rfl
        rw [h40_n, hs1_gm] at hcapw_eq
        have hsh_cap : shapeEqHOL .one (shapeOfHOLExact (.val (.word capw))) = true := by
          simp [shapeEqHOL, shapeOfHOLExact]
        rw [if_pos hsh_cap] at hnt ⊢; dsimp only at hnt ⊢
        set s2 := setVarHOLFinite (ofString "cap") (.val (.word capw)) s1 with hs2
        have hs2_len : s2.locals.lookup (ofString "len") = some (.val (.word lenw)) := by
          simp [hs2, hs1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
            show ofString "cap" ≠ ofString "len" by decide]
        have hs2_cap : s2.locals.lookup (ofString "cap") = some (.val (.word capw)) := by
          simp [hs2, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have hs2_eb : s2.locals.lookup (ofString "expand_by") = some (.val (.word ebw)) := by
          simp [hs2, hs1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, heb_loc,
            show ofString "cap" ≠ ofString "expand_by" by decide,
            show ofString "len" ≠ ofString "expand_by" by decide]
        rw [evaluateHOLFiniteState_dec_total] at hnt ⊢; dsimp only at hnt ⊢
        have hnlen_ev : @evalHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a))
            (.op .add [.var .local (ofString "len"), .var .local (ofString "expand_by")]) =
            some (.val (.word (lenw + ebw))) := by
          simp [evalHOLExact, evalListHOLExact, hs2_len, hs2_eb, wordOpHOL, wordOp, valueIsWord, valueWord]
        rw [hnlen_ev] at hnt ⊢; dsimp only at hnt ⊢
        set nlenw := lenw + ebw
        have hnlenw_nat : nlenw.toNat = lenw.toNat + ebw.toNat := by
          rw [BitVec.toNat_add, hlenw_eq, Nat.mod_eq_of_lt (by omega)]
        have hsh_nlen : shapeEqHOL .one (shapeOfHOLExact (.val (.word nlenw))) = true := by
          simp [shapeEqHOL, shapeOfHOLExact]
        rw [if_pos hsh_nlen] at hnt ⊢; dsimp only at hnt ⊢
        set s3 := setVarHOLFinite (ofString "nlen") (.val (.word nlenw)) s2 with hs3
        have hs3_nlen : s3.locals.lookup (ofString "nlen") = some (.val (.word nlenw)) := by
          simp [hs3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have hs3_len : s3.locals.lookup (ofString "len") = some (.val (.word lenw)) := by
          simp [hs3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs2_len,
            show ofString "nlen" ≠ ofString "len" by decide]
        have hs3_cap : s3.locals.lookup (ofString "cap") = some (.val (.word capw)) := by
          simp [hs3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs2_cap,
            show ofString "nlen" ≠ ofString "cap" by decide]
        have hs3_eb : s3.locals.lookup (ofString "expand_by") = some (.val (.word ebw)) := by
          simp [hs3, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs2_eb,
            show ofString "nlen" ≠ ofString "expand_by" by decide]
        -- Bounds on old memory buffer `(memW s (ev + 24), memW s (ev + 40))` from `FrameWF`:
        have hmem_in : Inside (memW s (globN s "ev" + 24), memW s (globN s "ev" + 40)) scratchStart (globN s "frame_mem_ptr") :=
          hFW0.2.1
        have hmem_wok := hFW0.2.2.1
        have hmem24_8 : memW s (globN s "ev" + 24) % 8 = 0 := hmem_wok.1
        have hmem40_8 : memW s (globN s "ev" + 40) % 8 = 0 := hmem_wok.2.1
        have hfp_le_se : globN s "frame_mem_ptr" ≤ scratchEnd :=
          le_trans hInv.1.2.2.2.2.1 hInv.1.2.2.2.2.2.1
        have hse_val := R11Shards.scratchEnd_val
        have hss_val := R11Shards.scratchStart_val
        have hcap_lt : capw.toNat < 2 ^ 30 := by
          dsimp only [Inside] at hmem_in; omega
        have hlen_le_cap0 : lenw.toNat ≤ capw.toNat := by
          rw [hlenw_eq, hcapw_eq]; exact hFW0.2.2.2.2.2.2.1
        -- `run_tail` from any intermediate state `m` after the optional grow branch:
        have run_tail : ∀ (m : PanSemStateFiniteExact 64 F) (freshIvl : Ivl),
            ArenaReady m →
            globN s "frame_mem_ptr" ≤ globN m "frame_mem_ptr" →
            (∀ g : String, ofString g ≠ ofString "frame_mem_ptr" → m.globals.lookup (ofString g) = s.globals.lookup (ofString g)) →
            FrameMemByteEff s m [freshIvl, (globN s "ev", 280), (memW s (globN s "ev" + 24), memW s (globN s "ev" + 40))] →
            (freshIvl = (0, 0) ∨
              (freshIvl.1 % 8 = 0 ∧ freshIvl.2 % 8 = 0 ∧
                Inside freshIvl (globN s "frame_mem_ptr") (globN m "frame_mem_ptr"))) →
            (∀ off, off + 8 ≤ 280 → off % 8 = 0 → off ≠ 32 → off ≠ 40 →
              memW m (globN s "ev" + off) = memW s (globN s "ev" + off)) →
            ((freshIvl.2 = 0 ∧ memW m (globN s "ev" + 40) = memW s (globN s "ev" + 40)) ∨
              (freshIvl.2 ≠ 0 ∧
                memW s (globN s "ev" + 24) + memW s (globN s "ev" + 40) = freshIvl.1 ∧
                memW m (globN s "ev" + 40) = memW s (globN s "ev" + 40) + freshIvl.2)) →
            nlenw.toNat ≤ memW m (globN s "ev" + 40) →
            m.locals.lookup (ofString "len") = some (.val (.word lenw)) →
            m.locals.lookup (ofString "nlen") = some (.val (.word nlenw)) →
            m.locals.lookup (ofString "expand_by") = some (.val (.word ebw)) →
            (evaluateHOLFiniteState m tailProg).1 ≠ some .timeOut →
            let out := evaluateHOLFiniteState m tailProg
            let post := { out.2 with
              locals := ((out.2.locals.resVarEq (ofString "nlen", s2.locals.lookup (ofString "nlen"))).resVarEq
                (ofString "cap", s1.locals.lookup (ofString "cap"))).resVarEq
                (ofString "len", s.locals.lookup (ofString "len")) }
            (∀ v, out.1 = some (.returned v) →
              EvmInv post ∧ evmChain post = evmChain s ∧ evmR post ≤ evmR s ∧
              (∀ g : String, ofString g ≠ ofString "frame_mem_ptr" → globN post g = globN s g)) ∧
            (IsEvmErr out.1 →
              EvmInv post ∧ evmChain post = evmChain s ∧ evmR post ≤ evmR s) := by
          intro m freshIvl hAm hfm_m hm_glob_other heff_m hfresh_m he0_m hnew_m hnlen_le_mcap hm_len hm_nlen hm_eb hnt_t
          dsimp only [tailProg] at hnt_t ⊢
          have hm_ev : m.globals.lookup (ofString "ev") = some (.val (.word evw)) := by
            rw [hm_glob_other "ev" (by decide)]; exact hevw
          have hm_code : m.code = originalRuntimeCode := heff_m.code.trans hcode
          have hm_ma : m.memaddrs = ordinaryDomain := hAm.1.memaddrs
          have hm_dom24 : m.memaddrs (evw + 24#64) := by
            rw [hm_ma, ← hInv.1.1.memaddrs]
            have hev24_eq : evw + 24#64 = BitVec.ofNat 64 (globN s "ev" + 24) := by
              apply BitVec.eq_of_toNat_eq
              have : (24#64 : BitVec 64).toNat = 24 := rfl
              rw [BitVec.toNat_add, hevw_nat, this, BitVec.toNat_ofNat]
            rw [hev24_eq]
            exact ((hFW0.1 (globN s "ev", 280) (by simp)).2.2.2 3 (by omega)).choose_spec.1
          rcases hm_m24 : m.memory (evw + 24#64) with ⟨memPtrW⟩
          have hmemPtrW_nat : memPtrW.toNat = memW s (globN s "ev" + 24) := by
            have hev24_eq : evw + 24#64 = BitVec.ofNat 64 (globN s "ev" + 24) := by
              apply BitVec.eq_of_toNat_eq
              have : (24#64 : BitVec 64).toNat = 24 := rfl
              rw [BitVec.toNat_add, hevw_nat, this, BitVec.toNat_ofNat]
            have hm24_eq := he0_m 24 (by omega) (by omega) (by omega) (by omega)
            have hm24_lhs : memW m (globN s "ev" + 24) = memPtrW.toNat := by
              unfold memW; rw [← hev24_eq, hm_m24]
            rw [← hm24_lhs, hm24_eq]
          let mzDstExp : ExpHOL 64 :=
            .op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]), .var .local (ofString "len")]
          have hev_mz_dst : @evalHOLExact 64 F _ m.toExact (fun a => Classical.propDecidable (m.memaddrs a)) mzDstExp =
              some (.val (.word (memPtrW + lenw))) := by
            simp [mzDstExp, evalHOLExact, evalListHOLExact, hm_ev, hm_len, wordOpHOL, wordOp,
              valueIsWord, valueWord, memLoadHOLExact, hm_dom24, hm_m24]
          have hev_mz_n : @evalHOLExact 64 F _ m.toExact (fun a => Classical.propDecidable (m.memaddrs a))
              (.var .local (ofString "expand_by")) = some (.val (.word ebw)) := hm_eb
          have hmcap_bound : memW s (globN s "ev" + 24) + memW m (globN s "ev" + 40) ≤ scratchEnd := by
            rcases hnew_m with ⟨_, h40_eq⟩ | ⟨hnz, hfr1, h40_eq⟩
            · rw [h40_eq]; dsimp only [Inside] at hmem_in; omega
            · rcases hfresh_m with rfl | ⟨_, _, _, hfin2⟩
              · exact absurd rfl hnz
              · have hm_fp_se : globN m "frame_mem_ptr" ≤ scratchEnd :=
                  le_trans hAm.2.2.2.2.1 hAm.2.2.2.2.2.1
                omega
          have hdst_nat : (memPtrW + lenw).toNat = memW s (globN s "ev" + 24) + lenw.toNat := by
            rw [BitVec.toNat_add, hmemPtrW_nat, Nat.mod_eq_of_lt (by omega)]
          let combinedMem : Ivl := (memW s (globN s "ev" + 24), memW m (globN s "ev" + 40))
          let mzTailCall : ProgHOL 64 := .call (some (none, none)) (ofString "memzero") [mzDstExp, .var .local (ofString "expand_by")]
          rw [evaluateHOLFiniteState_seq_line780] at hnt_t ⊢
          have hnt_mz : (evaluateHOLFiniteState m mzTailCall).1 ≠ some .timeOut := by
            intro hto
            rcases hmz_to : evaluateHOLFiniteState m
                (.call (some (none, none)) (ofString "memzero") [mzDstExp, .var .local (ofString "expand_by")]) with ⟨rmz_to, smz_to⟩
            have hto' : rmz_to = some .timeOut := by
              dsimp only [mzTailCall] at hto; rw [hmz_to] at hto; exact hto
            subst hto'
            have hmz_to_raw : evaluateHOLFiniteState m
                (.call (some (none, none)) (ofString "memzero")
                  [.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]), .var .local (ofString "len")],
                   .var .local (ofString "expand_by")]) = (some .timeOut, smz_to) := hmz_to
            simp only [hmz_to_raw] at hnt_t
            exact hnt_t rfl
          have hmz := eval_call_memzero_bre m mzDstExp (.var .local (ofString "expand_by"))
            (memPtrW + lenw) ebw [combinedMem] hm_code hm_ma hev_mz_dst hev_mz_n
            (fun _ => ⟨combinedMem, by simp, by rw [hdst_nat]; dsimp only [combinedMem]; omega,
              by rw [hdst_nat]; dsimp only [combinedMem]; omega⟩) hnt_mz
          dsimp only at hmz
          rcases hmz_run : evaluateHOLFiniteState m mzTailCall with ⟨rmz, m1⟩
          rw [hmz_run] at hmz
          have hmz_run_raw : evaluateHOLFiniteState m
              (.call (some (none, none)) (ofString "memzero")
                [.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]), .var .local (ofString "len")],
                 .var .local (ofString "expand_by")]) = (rmz, m1) := hmz_run
          simp only [hmz_run_raw] at hnt_t ⊢
          cases rmz with
          | some rmz0 =>
            dsimp only at hnt_t ⊢
            have hnr := hmz.2 (by simp)
            refine ⟨fun v hv => absurd (Or.inl ⟨v, hv⟩) hnr, ?_⟩
            rintro ⟨ev, hv⟩
            injection hv with hv'; subst hv'
            exact absurd (Or.inr ⟨ofString "EvmErr", ev, rfl, by decide⟩) hnr
          | none =>
            dsimp only at hnt_t ⊢
            obtain ⟨heff_mz_comb, hm1_loc⟩ := hmz.1 rfl
            -- Convert `ByteRegionEffect m m1 [combinedMem]` to `FrameMemByteEff m m1 [freshIvl, (e0, 280), oldMem]`!
            have heff_mz : FrameMemByteEff m m1
                [freshIvl, (globN s "ev", 280), (memW s (globN s "ev" + 24), memW s (globN s "ev" + 40))] := by
              refine ⟨heff_mz_comb.code, heff_mz_comb.memaddrs, heff_mz_comb.shMemaddrs,
                heff_mz_comb.baseAddr, heff_mz_comb.be, fun _ _ => by rw [heff_mz_comb.globals],
                heff_mz_comb.out_dom, ?_, ?_⟩
              · intro a ha
                apply heff_mz_comb.cell_frame a
                intro i hi hch
                simp at hi; subst hi
                obtain ⟨hc1, hc2⟩ := hch
                dsimp only [combinedMem] at hc1 hc2
                rcases hnew_m with ⟨_, h40_eq⟩ | ⟨hnz, hfr1, h40_eq⟩
                · rw [h40_eq] at hc2
                  exact ha (memW s (globN s "ev" + 24), memW s (globN s "ev" + 40)) (by simp) ⟨hc1, hc2⟩
                · by_cases hsplit : a.toNat < memW s (globN s "ev" + 24) + memW s (globN s "ev" + 40)
                  · exact ha (memW s (globN s "ev" + 24), memW s (globN s "ev" + 40)) (by simp) ⟨hc1, hsplit⟩
                  · exact ha freshIvl (by simp) ⟨by omega, by omega⟩
              · intro b hb hno
                apply heff_mz_comb.byte_frame b hb
                intro i hi hin
                simp at hi; subst hi
                obtain ⟨hb1, hb2⟩ := hin
                dsimp only [combinedMem] at hb1 hb2
                rcases hnew_m with ⟨_, h40_eq⟩ | ⟨hnz, hfr1, h40_eq⟩
                · rw [h40_eq] at hb2
                  exact hno (memW s (globN s "ev" + 24), memW s (globN s "ev" + 40)) (by simp) ⟨hb1, hb2⟩
                · by_cases hsplit : b < memW s (globN s "ev" + 24) + memW s (globN s "ev" + 40)
                  · exact hno (memW s (globN s "ev" + 24), memW s (globN s "ev" + 40)) (by simp) ⟨hb1, hsplit⟩
                  · exact hno freshIvl (by simp) ⟨by omega, by omega⟩
            have hm1_e0_eq : ∀ off, off + 8 ≤ 280 → off % 8 = 0 →
                memW m1 (globN s "ev" + off) = memW m (globN s "ev" + off) := by
              intro off hoff hoff8
              unfold memW
              rw [heff_mz_comb.cell_frame (BitVec.ofNat 64 (globN s "ev" + off))]
              intro x hx
              simp at hx; subst hx
              have htn : (BitVec.ofNat 64 (globN s "ev" + off)).toNat = globN s "ev" + off :=
                Nat.mod_eq_of_lt (by omega)
              rw [htn]
              have he0_8 : (globN s "ev") % 8 = 0 := (hFW0.1 (globN s "ev", 280) (by simp)).2.1
              have ha8 : (globN s "ev" + off) % 8 = 0 := by omega
              rcases hnew_m with ⟨_, h40_eq⟩ | ⟨hnz, hfr1, h40_eq⟩
              · dsimp only [combinedMem]; rw [h40_eq]
                have hpw_fo := hInv.2.choose_spec.2.2.2.2.2.2.2.1
                have hch_s : ∃ tl, evmChain s = (globN s "ev", globN s "cur_cont") :: tl := ⟨_, rfl⟩
                obtain ⟨tl_s, hch_s_eq⟩ := hch_s
                rw [hch_s_eq, List.map_cons, List.flatten_cons, List.pairwise_append] at hpw_fo
                have hd_mem : Disj (globN s "ev", 280) (memW s (globN s "ev" + 24), memW s (globN s "ev" + 40)) := by
                  have hp0 := hpw_fo.1; unfold frameObjects at hp0
                  exact (List.pairwise_cons.1 hp0).1 _ (by simp)
                exact not_cellHits_of_disj_aligned (i := (globN s "ev", 280)) ha8 hmem24_8
                  (Nat.le_add_right _ off) (Nat.add_le_add_left hoff _) hd_mem
              · rcases hfresh_m with rfl | ⟨_, _, _, hfin2⟩
                · exact absurd rfl hnz
                · obtain ⟨he0_scr, _⟩ := (hFW0.1 (globN s "ev", 280) (by simp)).1
                  have hfp_le_scr : globN m "frame_mem_ptr" ≤ globN s "scratch_ptr" := by
                    have hle_m := hAm.2.2.2.2.1
                    have hsp_eq := R16Shards.OpHandlers.globN_eq_of_lookup_eq (hm_glob_other "scratch_ptr" (by decide))
                    omega
                  exact not_cellHits_of_disj_aligned (i := (globN s "ev", 280)) ha8 hmem24_8
                    (Nat.le_add_right _ off) (Nat.add_le_add_left hoff _)
                    (Or.inr (Or.inr (Or.inr (by dsimp only [combinedMem, Inside] at he0_scr hfin2 ⊢; omega))))
            rw [evaluateHOLFiniteState_seq_line780] at hnt_t ⊢
            rcases hst32 : evaluateHOLFiniteState m1
                (.store (.op .add [.var .global (ofString "ev"), .const 32#64]) (.var .local (ofString "nlen"))) with ⟨rst32, m2⟩
            simp only [hst32] at hnt_t ⊢
            cases rst32 with
            | some res32 =>
              have herr := store_some_eq_error' hst32; subst herr; dsimp only; exact herr_triv
            | none =>
              dsimp only at hnt_t ⊢
              have hm1_ev : m1.globals.lookup (ofString "ev") = some (.val (.word evw)) := by
                rw [heff_mz_comb.globals]; exact hm_ev
              have hm1_nlen : m1.locals.lookup (ofString "nlen") = some (.val (.word nlenw)) := by
                rw [hm1_loc]; exact hm_nlen
              obtain ⟨w_nl', hw_nl_ev, hm2_eq⟩ := R14Shards.OpHandlersA.store_global_off_word (t := m1) (post := m2)
                (gname := "ev") (gbase := globN s "ev") (off := 32) hm1_ev hevw_nat (by omega)
                (fun v hv => by
                  change m1.locals.lookup (ofString "nlen") = some v at hv
                  rw [hm1_nlen] at hv; injection hv with hv'; exact ⟨nlenw, hv'.symm⟩) hst32
              have hw_nl_val : nlenw = w_nl' := by
                change m1.locals.lookup (ofString "nlen") = some (.val (.word w_nl')) at hw_nl_ev
                rw [hm1_nlen] at hw_nl_ev
                injection hw_nl_ev with h1; injection h1 with h2; injection h2 with h3
              subst w_nl'
              have heff_st32 := (ByteRegionEffect.of_store_word (Rl := [(globN s "ev", 280)])
                (heff_mz_comb.memaddrs.trans hm_ma) hst32
                (fun v hv => by
                  change m1.locals.lookup (ofString "nlen") = some v at hv
                  rw [hm1_nlen] at hv; injection hv with hv'; exact ⟨nlenw, hv'.symm⟩)
                (fun addr hdst _ => by
                  simp [evalHOLExact, evalListHOLExact, hm1_ev, wordOpHOL, wordOp, valueIsWord, valueWord] at hdst
                  have h32_eq : (evw + 32#64).toNat = globN s "ev" + 32 := by
                    have : (32#64 : BitVec 64).toNat = 32 := rfl
                    rw [BitVec.toNat_add, hevw_nat, this, Nat.mod_eq_of_lt (by omega)]
                  exact ⟨(globN s "ev", 280), by simp, by rw [← hdst, h32_eq]; dsimp only; omega,
                    by rw [← hdst, h32_eq]; dsimp only; omega⟩)).1
              have heff_st32_fm : FrameMemByteEff m1 m2
                  [freshIvl, (globN s "ev", 280), (memW s (globN s "ev" + 24), memW s (globN s "ev" + 40))] :=
                (FrameMemByteEff.of_bre heff_st32).mono (fun x hx => by
                  simp at hx; subst hx; exact ⟨(globN s "ev", 280), by simp, le_refl _, le_refl _⟩)
              rw [evaluateHOLFiniteState_return]
              have hc0_m2 : @evalHOLExact 64 F _ m2.toExact (fun a => Classical.propDecidable (m2.memaddrs a)) (.const (0 : BitVec 64)) =
                  some (.val (.word 0)) := rfl
              have hc0_m2' : @evalHOLExact 64 F _ m2.toExact (fun a => Classical.propDecidable (m2.memaddrs a)) (.const 0#64) =
                  some (.val (.word 0#64)) := rfl
              simp only [hc0_m2, hc0_m2']
              have hsz0 : sizeOfShapeWithContextHOL m2.structs
                  (shapeOfHOLExact (.val (.word (0 : BitVec 64)))) ≤ 32 := by
                simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
              have hsz0' : sizeOfShapeWithContextHOL m2.structs
                  (shapeOfHOLExact (.val (.word 0#64))) ≤ 32 := by
                simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
              simp only [hsz0, hsz0', ↓reduceIte]
              let post := { m2.emptyLocalsHOLFinite with
                locals := ((m2.emptyLocalsHOLFinite.locals.resVarEq (ofString "nlen", s2.locals.lookup (ofString "nlen"))).resVarEq
                  (ofString "cap", s1.locals.lookup (ofString "cap"))).resVarEq
                  (ofString "len", s.locals.lookup (ofString "len")) }
              have heff_total : FrameMemByteEff s post
                  [freshIvl, (globN s "ev", 280), (memW s (globN s "ev" + 24), memW s (globN s "ev" + 40))] :=
                ((heff_m.trans heff_mz).trans heff_st32_fm).with_locals_clock post.locals m2.clock
              have hm1_glob_m : m1.globals = m.globals := heff_mz_comb.globals
              have hm1_code_m : m1.code = m.code := heff_mz_comb.code
              have hm1_ma_m : m1.memaddrs = m.memaddrs := heff_mz_comb.memaddrs
              have hm1_sh_m : m1.shMemaddrs = m.shMemaddrs := heff_mz_comb.shMemaddrs
              have hm1_ba_m : m1.baseAddr = m.baseAddr := heff_mz_comb.baseAddr
              have hpost_glob_m : post.globals = m.globals := by
                simp [post, emptyLocalsHOLFinite, hm2_eq, hm1_glob_m]
              have hApost : ArenaReady post :=
                ⟨guestInv_congr (s := m) (by simp [post, emptyLocalsHOLFinite, hm2_eq, hm1_code_m])
                  (by simp [post, emptyLocalsHOLFinite, hm2_eq, hm1_ma_m])
                  (by simp [post, emptyLocalsHOLFinite, hm2_eq, hm1_sh_m])
                  (by simp [post, emptyLocalsHOLFinite, hm2_eq, hm1_ba_m]) hAm.1,
                 arenaOK_congr hpost_glob_m hAm.2⟩
              have hfm_post : globN s "frame_mem_ptr" ≤ globN post "frame_mem_ptr" := by
                unfold globN; rw [hpost_glob_m]; exact hfm_m
              have hfresh_post : freshIvl = (0, 0) ∨
                  (freshIvl.1 % 8 = 0 ∧ freshIvl.2 % 8 = 0 ∧
                    Inside freshIvl (globN s "frame_mem_ptr") (globN post "frame_mem_ptr")) := by
                unfold globN; rw [hpost_glob_m]; exact hfresh_m
              have hm2_memW_ne32 : ∀ off, off + 8 ≤ 280 → off % 8 = 0 → off ≠ 32 →
                  memW post (globN s "ev" + off) = memW m (globN s "ev" + off) := by
                intro off hoff hoff8 hne32
                change memW m2 (globN s "ev" + off) = memW m (globN s "ev" + off)
                rw [hm2_eq, R14Shards.OpHandlersA.memW_updW_ne m1 (globN s "ev" + 32) (globN s "ev" + off) _ (by omega) (by omega) (by omega),
                    hm1_e0_eq off hoff hoff8]
              have hm2_memW_32 : memW post (globN s "ev" + 32) = nlenw.toNat := by
                change memW m2 (globN s "ev" + 32) = nlenw.toNat
                rw [hm2_eq, R14Shards.OpHandlersA.memW_updW_same m1 (globN s "ev" + 32) nlenw]
              have he0_post : ∀ off, off + 8 ≤ 280 → off % 8 = 0 → off ≠ 32 → off ≠ 40 →
                  memW post (globN s "ev" + off) = memW s (globN s "ev" + off) := by
                intro off hoff hoff8 h32 h40
                rw [hm2_memW_ne32 off hoff hoff8 h32, he0_m off hoff hoff8 h32 h40]
              have hnew_post :
                  (freshIvl.2 = 0 ∧ memW post (globN s "ev" + 40) = memW s (globN s "ev" + 40)) ∨
                  (freshIvl.2 ≠ 0 ∧
                    memW s (globN s "ev" + 24) + memW s (globN s "ev" + 40) = freshIvl.1 ∧
                    memW post (globN s "ev" + 40) = memW s (globN s "ev" + 40) + freshIvl.2) := by
                rw [hm2_memW_ne32 40 (by omega) (by omega) (by omega)]
                exact hnew_m
              have hlen_le_cap_post : memW post (globN s "ev" + 32) ≤ memW post (globN s "ev" + 40) := by
                rw [hm2_memW_32, hm2_memW_ne32 40 (by omega) (by omega) (by omega)]
                exact hnlen_le_mcap
              obtain ⟨hInv_p, hch_p, hR_p⟩ := evmInv_of_head_mem_extend hInv hApost hfm_post
                heff_total hfresh_post he0_post hnew_post hlen_le_cap_post
              constructor
              · intro _ _
                refine ⟨hInv_p, hch_p, le_of_eq hR_p, fun g hg => ?_⟩
                unfold globN; rw [hpost_glob_m, hm_glob_other g hg]
              · rintro ⟨_, h⟩; cases h
        -- Now evaluate `if cap < nlen then growBranch else skip` before `tailProg`:
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt ⊢
        have hcmp_grow : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
            (.cmp .lower (.var .local (ofString "cap")) (.var .local (ofString "nlen"))) =
            some (.val (.word (if capw < nlenw then 1 else 0))) := by
          simp [evalHOLExact, hs3_cap, hs3_nlen, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
        rw [hcmp_grow] at hnt ⊢; dsimp only at hnt ⊢
        by_cases hgrow : capw < nlenw
        · have hcap_lt_nlen : capw.toNat < nlenw.toNat := BitVec.lt_def.1 hgrow
          simp only [hgrow, ↓reduceIte, h10] at hnt ⊢
          dsimp only [growBranch] at hnt ⊢
          rw [evaluateHOLFiniteState_dec_total] at hnt ⊢; dsimp only at hnt ⊢
          have hmul2 : @evalHOLExact 64 F _ s3.toExact (fun a => Classical.propDecidable (s3.memaddrs a))
              (.panop .mul [.var .local (ofString "cap"), .const 2#64]) =
              some (.val (.word (capw * 2#64))) := by
            simp [evalHOLExact, evalListHOLExact, hs3_cap, panOpHOL, valueIsWord, valueWord]
          rw [hmul2] at hnt ⊢; dsimp only at hnt ⊢
          have hsh_ncap : shapeEqHOL .one (shapeOfHOLExact (.val (.word (capw * 2#64)))) = true := by
            simp [shapeEqHOL, shapeOfHOLExact]
          rw [if_pos hsh_ncap] at hnt ⊢; dsimp only at hnt ⊢
          set s4 := setVarHOLFinite (ofString "ncap") (.val (.word (capw * 2#64))) s3 with hs4
          have hncap0_nat : (capw * 2#64).toNat = 2 * capw.toNat := by
            have : (2#64 : BitVec 64).toNat = 2 := rfl
            rw [BitVec.toNat_mul, this, Nat.mod_eq_of_lt (by omega)]; omega
          have hite_ncap : ∃ (s5 : PanSemStateFiniteExact 64 F) (ncapw : BitVec 64),
              evaluateHOLFiniteState s4
                (.ite (.cmp .lower (.var .local (ofString "ncap")) (.var .local (ofString "nlen")))
                  (.assign .local (ofString "ncap") (.op .add [.var .local (ofString "nlen"), .const 1024#64]))
                  .skip) = (none, s5) ∧
              s5 = { s with locals := s5.locals, clock := s.clock } ∧
              s5.locals.lookup (ofString "ncap") = some (.val (.word ncapw)) ∧
              s5.locals.lookup (ofString "cap") = some (.val (.word capw)) ∧
              s5.locals.lookup (ofString "len") = some (.val (.word lenw)) ∧
              s5.locals.lookup (ofString "nlen") = some (.val (.word nlenw)) ∧
              s5.locals.lookup (ofString "expand_by") = some (.val (.word ebw)) ∧
              nlenw.toNat ≤ ncapw.toNat ∧ capw.toNat < ncapw.toNat ∧
              ncapw.toNat < 2 ^ 38 ∧ ncapw.toNat % 8 = 0 := by
            have hnlenw_al8 : nlenw.toNat % 8 = 0 := by
              rw [hnlenw_nat, hlenw_eq]; exact hnlen_al8
            have hcapw_al8 : capw.toNat % 8 = 0 := by
              rw [hcapw_eq]; exact hmem40_8
            have hs4_ncap : s4.locals.lookup (ofString "ncap") = some (.val (.word (capw * 2#64))) := by
              simp [hs4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
            have hs4_nlen : s4.locals.lookup (ofString "nlen") = some (.val (.word nlenw)) := by
              simp [hs4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_nlen,
                show ofString "ncap" ≠ ofString "nlen" by decide]
            rw [evaluateHOLFiniteState_ite]
            have hcmp_nc : @evalHOLExact 64 F _ s4.toExact (fun a => Classical.propDecidable (s4.memaddrs a))
                (.cmp .lower (.var .local (ofString "ncap")) (.var .local (ofString "nlen"))) =
                some (.val (.word (if capw * 2#64 < nlenw then 1 else 0))) := by
              simp [evalHOLExact, hs4_ncap, hs4_nlen, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
            rw [hcmp_nc]; dsimp only
            by_cases hlt_nl : capw * 2#64 < nlenw
            · simp only [hlt_nl, ↓reduceIte, h10, evaluateHOLFiniteState_assign]
              have hev_add1024 : @evalHOLExact 64 F _ s4.toExact (fun a => Classical.propDecidable (s4.memaddrs a))
                  (.op .add [.var .local (ofString "nlen"), .const 1024#64]) =
                  some (.val (.word (nlenw + 1024#64))) := by
                simp [evalHOLExact, evalListHOLExact, hs4_nlen, wordOpHOL, wordOp, valueIsWord, valueWord]
              have hval_nc : s4.isValidValueHOLFinite .local (ofString "ncap") (.val (.word (nlenw + 1024#64))) = true := by
                simp [isValidValueHOLFinite, lookupKvarHOLFinite, hs4_ncap, shapeOfHOLExact, shapeEqHOL]
              rw [hev_add1024]; dsimp only; rw [if_pos hval_nc]
              let s5 := setKvarHOLFinite .local (ofString "ncap") (.val (.word (nlenw + 1024#64))) s4
              have h1024_n : (1024#64 : BitVec 64).toNat = 1024 := rfl
              have hnl1024_nat : (nlenw + 1024#64).toNat = nlenw.toNat + 1024 := by
                rw [BitVec.toNat_add, h1024_n, Nat.mod_eq_of_lt (by omega)]
              refine ⟨s5, nlenw + 1024#64, rfl, by cases s; rfl, ?_, ?_, ?_, ?_, ?_, by omega, by omega, by omega, by omega⟩
              · simp [s5, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
              · simp [s5, hs4, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_cap,
                  show ofString "ncap" ≠ ofString "cap" by decide]
              · simp [s5, hs4, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_len,
                  show ofString "ncap" ≠ ofString "len" by decide]
              · simp [s5, hs4, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_nlen,
                  show ofString "ncap" ≠ ofString "nlen" by decide]
              · simp [s5, hs4, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_eb,
                  show ofString "ncap" ≠ ofString "expand_by" by decide]
            · simp only [hlt_nl, ↓reduceIte, evaluateHOLFiniteState_skip]
              have hge_nl : nlenw.toNat ≤ (capw * 2#64).toNat := by
                rw [BitVec.lt_def] at hlt_nl; omega
              refine ⟨s4, capw * 2#64, rfl, by cases s; rfl, hs4_ncap, ?_, ?_, hs4_nlen, ?_, hge_nl, by omega, by omega, by omega⟩
              · simp [hs4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_cap,
                  show ofString "ncap" ≠ ofString "cap" by decide]
              · simp [hs4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_len,
                  show ofString "ncap" ≠ ofString "len" by decide]
              · simp [hs4, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hs3_eb,
                  show ofString "ncap" ≠ ofString "expand_by" by decide]
          obtain ⟨s5, ncapw, hs5_run, hs5_eq, hs5_ncap, hs5_cap, hs5_len, hs5_nlen, hs5_eb,
            hnlen_le_ncap, hcap_lt_ncap, hncap_lt, hncap_al8⟩ := hite_ncap
          rw [evaluateHOLFiniteState_seq_line780, hs5_run] at hnt ⊢; dsimp only at hnt ⊢
          set diffw := ncapw - capw
          have hdiff_nat : diffw.toNat = ncapw.toNat - capw.toNat :=
            BitVec.toNat_sub_of_le (BitVec.le_def.2 (Nat.le_of_lt hcap_lt_ncap))
          -- Evaluate `.call (some (none, none)) "frame_mem_alloc" [ncap - cap]` followed by `memzero` and `store`:
          rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_call] at hnt ⊢
          have hs5_code : s5.code = originalRuntimeCode := by rw [hs5_eq]; exact hcode
          have hargs_fma : evalListHOLFinite s5 (h := fun a => Classical.propDecidable (s5.memaddrs a))
              [.op .sub [.var .local (ofString "ncap"), .var .local (ofString "cap")]] =
              some [.val (.word diffw)] := by
            simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hs5_ncap, hs5_cap,
              wordOpHOL, wordOp, valueIsWord, valueWord, diffw]
          have hlk_fma := pan_one_word_lookup s5.code.lookup (ofString "frame_mem_alloc") (ofString "n")
            (sourceFnBody Guest.Software.guestFn_frame_mem_alloc) diffw
            (by rw [hs5_code]; exact lookup_frame_mem_alloc)
          rw [hargs_fma] at hnt ⊢; dsimp only at hnt ⊢
          rw [hlk_fma] at hnt ⊢; dsimp only at hnt ⊢
          by_cases hs5_clk0 : s5.clock = 0
          · rw [if_pos hs5_clk0] at hnt; simp at hnt
          · rw [if_neg hs5_clk0] at hnt ⊢
            let fmaCallee := HolFiniteMapExact.empty.update (ofString "n", ValueHOL.val (.word diffw))
            let fmaEntry := callEntryStateHOLFinite s5 fmaCallee
            have hfma_code : fmaEntry.code = originalRuntimeCode := hs5_code
            have hfma_no_evmErr := frame_mem_alloc_body_no_evmErr fmaEntry hfma_code
            rcases hfma_run : evaluateHOLFiniteState fmaEntry
                (sourceFnBody Guest.Software.guestFn_frame_mem_alloc) with ⟨rfma, fmaPost⟩
            rw [hfma_run] at hfma_no_evmErr
            have hfma_run_raw : evaluateHOLFiniteState
                (callEntryStateHOLFinite s5 (HolFiniteMapExact.empty.update (ofString "n", ValueHOL.val (.word diffw))))
                (sourceFnBody Guest.Software.guestFn_frame_mem_alloc) = (rfma, fmaPost) := hfma_run
            simp only [hfma_run_raw] at hnt ⊢
            cases rfma with
            | none => exact herr_triv
            | some rfma0 =>
              cases rfma0 with
              | timeOut => simp at hnt
              | exception eid ev =>
                dsimp only at hnt ⊢
                by_cases heid : eid = ofString "EvmErr"
                · subst heid; exact absurd ⟨ev, rfl⟩ hfma_no_evmErr
                · constructor
                  · intro _ h; cases h
                  · rintro ⟨_, h⟩; injection h with h'; injection h' with h1 _; exact (heid h1).elim
              | «break» => exact herr_triv
              | «continue» => exact herr_triv
              | finalFfi _ =>
                constructor
                · intro _ h; cases h
                · rintro ⟨_, h⟩; cases h
              | error => exact herr_triv
              | returned vfma =>
                have hfma_fp_lk : fmaEntry.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word fp_w)) := by
                  change s5.globals.lookup _ = _; rw [hs5_eq]; exact hfp_lk
                have hfma_sp_lk : fmaEntry.globals.lookup (ofString "scratch_ptr") = some (.val (.word sp_g_w)) := by
                  change s5.globals.lookup _ = _; rw [hs5_eq]; exact hsp_g_lk
                have hfma_n_lk : fmaEntry.locals.lookup (ofString "n") = some (.val (.word diffw)) := by
                  simp [fmaEntry, fmaCallee, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                obtain ⟨rfl, hcmp1_fma, hcmp2_fma, hfmaPost_eq_raw⟩ :=
                  frame_mem_alloc_body_run fmaEntry fp_w sp_g_w diffw
                    hfma_code hfma_fp_lk hfma_sp_lk hfma_n_lk vfma (by rw [hfma_run])
                have hfmaPost_eq : fmaPost = { fmaEntry with
                    globals := fmaEntry.globals.update (ofString "frame_mem_ptr",
                      .val (.word ((fp_w + (diffw + 7)) &&& ((0 : BitVec 64) - 8)))),
                    locals := fmaPost.locals,
                    clock := fmaPost.clock } := by
                  rw [hfma_run] at hfmaPost_eq_raw; exact hfmaPost_eq_raw
                dsimp only [fmaEntry] at hfmaPost_eq
                set qw : BitVec 64 := (fp_w + (diffw + 7)) &&& ((0 : BitVec 64) - 8)
                have hsh_p : shapeEqHOL (shapeOfHOLExact (.val (.word fp_w) : ValueHOL 64)) .one = true := by
                  simp [shapeEqHOL, shapeOfHOLExact]
                dsimp only at hnt ⊢
                simp only [hsh_p, ↓reduceIte] at hnt ⊢
                have hfp_le_sp_g : fp_w.toNat ≤ sp_g_w.toNat := by
                  have := hInv.1.2.2.2.2.1; omega
                have hsp_g_le_se : sp_g_w.toNat ≤ scratchEnd := by
                  have := hInv.1.2.2.2.2.2.1; omega
                have hfp_al8 : fp_w.toNat % 8 = 0 := by
                  have h8 : globN s "frame_mem_ptr" % 8 = 0 := hInv.1.2.2.2.2.2.2.2.1
                  rw [hfp_nat]; exact h8
                obtain ⟨hq_nat, hq_le_sp, hq_al8, hfp_le_q⟩ :=
                  frame_mem_alloc_arith fp_w sp_g_w diffw hfp_le_sp_g hsp_g_le_se hfp_al8 hcmp1_fma hcmp2_fma
                have hqw_nat : qw.toNat = fp_w.toNat + diffw.toNat := by
                  have hdiff_al8' : diffw.toNat % 8 = 0 := by
                    have hcapw_al8 : capw.toNat % 8 = 0 := by rw [hcapw_eq]; exact hmem40_8
                    omega
                  have halign_eq : (diffw.toNat + 7) / 8 * 8 = diffw.toNat := by omega
                  change qw.toNat = _ at hq_nat
                  omega
                have hqw_al8 : qw.toNat % 8 = 0 := hq_al8
                have hqw_le_sp : qw.toNat ≤ sp_g_w.toNat := hq_le_sp
                have hdiff_al8 : diffw.toNat % 8 = 0 := by
                  have hcapw_al8 : capw.toNat % 8 = 0 := by rw [hcapw_eq]; exact hmem40_8
                  omega
                have hdiff_pos : 0 < diffw.toNat := by omega
                set s6 : PanSemStateFiniteExact 64 F := { fmaPost with locals := s5.locals } with hs6_def
                have hs6_glob : s6.globals = s.globals.update (ofString "frame_mem_ptr", .val (.word qw)) := by
                  change fmaPost.globals = _
                  rw [hfmaPost_eq]; dsimp only [callEntryStateHOLFinite]; rw [hs5_eq]
                have hs6_code : s6.code = originalRuntimeCode := by
                  change fmaPost.code = _; rw [hfmaPost_eq]; dsimp only [callEntryStateHOLFinite]; exact hs5_code
                have hs6_ma : s6.memaddrs = ordinaryDomain := by
                  change fmaPost.memaddrs = _; rw [hfmaPost_eq]; dsimp only [callEntryStateHOLFinite]
                  rw [hs5_eq]; exact hInv.1.1.memaddrs
                have hs6_mem : s6.memory = s.memory := by
                  change fmaPost.memory = _; rw [hfmaPost_eq]; dsimp only [callEntryStateHOLFinite]; rw [hs5_eq]
                have hs6_ev : s6.globals.lookup (ofString "ev") = some (.val (.word evw)) := by
                  rw [hs6_glob]
                  simp [HolFiniteMapExact.lookup_update, FUPDATE,
                    show ofString "frame_mem_ptr" ≠ ofString "ev" by decide, hevw]
                have hs6_dom24 : s6.memaddrs (evw + 24#64) := by
                  rw [hs6_ma, ← hInv.1.1.memaddrs]
                  have hev24_eq : evw + 24#64 = BitVec.ofNat 64 (globN s "ev" + 24) := by
                    apply BitVec.eq_of_toNat_eq
                    have : (24#64 : BitVec 64).toNat = 24 := rfl
                    rw [BitVec.toNat_add, hevw_nat, this, BitVec.toNat_ofNat]
                  rw [hev24_eq]
                  exact ((hFW0.1 (globN s "ev", 280) (by simp)).2.2.2 3 (by omega)).choose_spec.1
                rcases hs_m24 : s.memory (evw + 24#64) with ⟨memPtrW⟩
                have hs6_m24 : s6.memory (evw + 24#64) = .word memPtrW := by rw [hs6_mem, hs_m24]
                have hmemPtrW_nat : memPtrW.toNat = memW s (globN s "ev" + 24) := by
                  have hev24_eq : evw + 24#64 = BitVec.ofNat 64 (globN s "ev" + 24) := by
                    apply BitVec.eq_of_toNat_eq
                    have : (24#64 : BitVec 64).toNat = 24 := rfl
                    rw [BitVec.toNat_add, hevw_nat, this, BitVec.toNat_ofNat]
                  unfold memW; rw [← hev24_eq, hs_m24]
                let freshIvl : Ivl := (globN s "frame_mem_ptr", diffw.toNat)
                let mzGrowDst : ExpHOL 64 :=
                  .op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]), .var .local (ofString "cap")]
                let mzGrowN : ExpHOL 64 :=
                  .op .sub [.var .local (ofString "ncap"), .var .local (ofString "cap")]
                have hev_mzg_dst : @evalHOLExact 64 F _ s6.toExact (fun a => Classical.propDecidable (s6.memaddrs a)) mzGrowDst =
                    some (.val (.word (memPtrW + capw))) := by
                  have hs6_cap : s6.locals.lookup (ofString "cap") = some (.val (.word capw)) := hs5_cap
                  simp [mzGrowDst, evalHOLExact, evalListHOLExact, hs6_ev, hs6_cap, wordOpHOL, wordOp,
                    valueIsWord, valueWord, memLoadHOLExact, hs6_dom24, hs6_m24]
                have hev_mzg_n : @evalHOLExact 64 F _ s6.toExact (fun a => Classical.propDecidable (s6.memaddrs a)) mzGrowN =
                    some (.val (.word diffw)) := by
                  have hs6_ncap : s6.locals.lookup (ofString "ncap") = some (.val (.word ncapw)) := hs5_ncap
                  have hs6_cap : s6.locals.lookup (ofString "cap") = some (.val (.word capw)) := hs5_cap
                  simp [mzGrowN, evalHOLExact, evalListHOLExact, hs6_ncap, hs6_cap, wordOpHOL, wordOp,
                    valueIsWord, valueWord, diffw]
                have hmzg_dst_nat : (memPtrW + capw).toNat = globN s "frame_mem_ptr" := by
                  rw [BitVec.toNat_add, hmemPtrW_nat, hcapw_eq, hmem_end_fp, Nat.mod_eq_of_lt (by omega)]
                let mzGrowCall : ProgHOL 64 := .call (some (none, none)) (ofString "memzero") [mzGrowDst, mzGrowN]
                rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
                have hnt_mzg : (evaluateHOLFiniteState s6 mzGrowCall).1 ≠ some .timeOut := by
                  intro hto
                  rcases hmzg_to : evaluateHOLFiniteState s6
                      (.call (some (none, none)) (ofString "memzero") [mzGrowDst, mzGrowN]) with ⟨rmzg_to, smzg_to⟩
                  have hto' : rmzg_to = some .timeOut := by
                    dsimp only [mzGrowCall] at hto; rw [hmzg_to] at hto; exact hto
                  subst hto'
                  have hmzg_to_raw : evaluateHOLFiniteState s6
                      (.call (some (none, none)) (ofString "memzero")
                        [.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]), .var .local (ofString "cap")],
                         .op .sub [.var .local (ofString "ncap"), .var .local (ofString "cap")]]) = (some .timeOut, smzg_to) := hmzg_to
                  simp only [hmzg_to_raw] at hnt
                  exact hnt rfl
                have hmzg := eval_call_memzero_bre s6 mzGrowDst mzGrowN
                  (memPtrW + capw) diffw [freshIvl] hs6_code hs6_ma hev_mzg_dst hev_mzg_n
                  (fun _ => ⟨freshIvl, by simp, by rw [hmzg_dst_nat]; dsimp only [freshIvl]; omega⟩) hnt_mzg
                dsimp only at hmzg
                rcases hmzg_run : evaluateHOLFiniteState s6 mzGrowCall with ⟨rmzg, s7⟩
                rw [hmzg_run] at hmzg
                have hmzg_run_raw : evaluateHOLFiniteState s6
                    (.call (some (none, none)) (ofString "memzero")
                      [.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 24#64]), .var .local (ofString "cap")],
                       .op .sub [.var .local (ofString "ncap"), .var .local (ofString "cap")]]) = (rmzg, s7) := hmzg_run
                simp only [hmzg_run_raw] at hnt ⊢
                cases rmzg with
                | some rmzg0 =>
                  dsimp only at hnt ⊢
                  have hnr := hmzg.2 (by simp)
                  refine ⟨fun v hv => absurd (Or.inl ⟨v, hv⟩) hnr, ?_⟩
                  rintro ⟨ev, hv⟩
                  injection hv with hv'; subst hv'
                  exact absurd (Or.inr ⟨ofString "EvmErr", ev, rfl, by decide⟩) hnr
                | none =>
                  dsimp only at hnt ⊢
                  obtain ⟨heff_mzg, hs7_loc⟩ := hmzg.1 rfl
                  rcases hst40 : evaluateHOLFiniteState s7
                      (.store (.op .add [.var .global (ofString "ev"), .const 40#64]) (.var .local (ofString "ncap"))) with ⟨rst40, s8⟩
                  simp only [hst40] at hnt ⊢
                  cases rst40 with
                  | some res40 =>
                    have herr := store_some_eq_error' hst40; subst herr; dsimp only; exact herr_triv
                  | none =>
                    dsimp only at hnt ⊢
                    have hs7_ev : s7.globals.lookup (ofString "ev") = some (.val (.word evw)) := by
                      rw [heff_mzg.globals]; exact hs6_ev
                    have hs7_ncap : s7.locals.lookup (ofString "ncap") = some (.val (.word ncapw)) := by
                      rw [hs7_loc]; exact hs5_ncap
                    obtain ⟨w_ncap', hw_ncap_ev, hs8_eq⟩ := R14Shards.OpHandlersA.store_global_off_word (t := s7) (post := s8)
                      (gname := "ev") (gbase := globN s "ev") (off := 40) hs7_ev hevw_nat (by omega)
                      (fun v hv => by
                        change s7.locals.lookup (ofString "ncap") = some v at hv
                        rw [hs7_ncap] at hv; injection hv with hv'; exact ⟨ncapw, hv'.symm⟩) hst40
                    have hw_ncap_val : ncapw = w_ncap' := by
                      change s7.locals.lookup (ofString "ncap") = some (.val (.word w_ncap')) at hw_ncap_ev
                      rw [hs7_ncap] at hw_ncap_ev
                      injection hw_ncap_ev with h1; injection h1 with h2; injection h2 with h3
                    subst w_ncap'
                    have heff_st40 := (ByteRegionEffect.of_store_word (Rl := [(globN s "ev", 280)])
                      (heff_mzg.memaddrs.trans hs6_ma) hst40
                      (fun v hv => by
                        change s7.locals.lookup (ofString "ncap") = some v at hv
                        rw [hs7_ncap] at hv; injection hv with hv'; exact ⟨ncapw, hv'.symm⟩)
                      (fun addr hdst _ => by
                        simp [evalHOLExact, evalListHOLExact, hs7_ev, wordOpHOL, wordOp, valueIsWord, valueWord] at hdst
                        have h40_eq : (evw + 40#64).toNat = globN s "ev" + 40 := by
                          have : (40#64 : BitVec 64).toNat = 40 := rfl
                          rw [BitVec.toNat_add, hevw_nat, this, Nat.mod_eq_of_lt (by omega)]
                        exact ⟨(globN s "ev", 280), by simp, by rw [← hdst, h40_eq]; dsimp only; omega,
                          by rw [← hdst, h40_eq]; dsimp only; omega⟩)).1
                    let m : PanSemStateFiniteExact 64 F :=
                      { s8 with locals := s8.locals.resVarEq (ofString "ncap", s3.locals.lookup (ofString "ncap")) }
                    change (let out := evaluateHOLFiniteState m tailProg
                      let post := { out.2 with
                        locals := ((out.2.locals.resVarEq (ofString "nlen", s2.locals.lookup (ofString "nlen"))).resVarEq
                          (ofString "cap", s1.locals.lookup (ofString "cap"))).resVarEq
                          (ofString "len", s.locals.lookup (ofString "len")) }
                      (∀ v, out.1 = some (.returned v) →
                        EvmInv post ∧ evmChain post = evmChain s ∧ evmR post ≤ evmR s ∧
                        (∀ g : String, ofString g ≠ ofString "frame_mem_ptr" → globN post g = globN s g)) ∧
                      (IsEvmErr out.1 →
                        EvmInv post ∧ evmChain post = evmChain s ∧ evmR post ≤ evmR s))
                    have hm_glob : m.globals = s.globals.update (ofString "frame_mem_ptr", .val (.word qw)) := by
                      dsimp only [m]; rw [hs8_eq]; dsimp only; rw [heff_mzg.globals, hs6_glob]
                    have hm_fp_glob : globN m "frame_mem_ptr" = qw.toNat := by
                      unfold globN; rw [hm_glob]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
                    have hm_other_glob : ∀ g : String, ofString g ≠ ofString "frame_mem_ptr" →
                        m.globals.lookup (ofString g) = s.globals.lookup (ofString g) := by
                      intro g hg; rw [hm_glob]
                      simp [HolFiniteMapExact.lookup_update, FUPDATE, hg, Ne.symm hg]
                    have hm_G : GuestInv m := by
                      have hcode_m : m.code = s.code := by
                        dsimp only [m]; rw [hs8_eq]; dsimp only; rw [heff_mzg.code, hs6_code, hcode]
                      have hma_m : m.memaddrs = s.memaddrs := by
                        dsimp only [m]; rw [hs8_eq]; dsimp only; rw [heff_mzg.memaddrs, hs6_ma, hInv.1.1.memaddrs]
                      have hsh_m : m.shMemaddrs = s.shMemaddrs := by
                        dsimp only [m]; rw [hs8_eq]; dsimp only; rw [heff_mzg.shMemaddrs]
                        change fmaPost.shMemaddrs = _; rw [hfmaPost_eq]; dsimp only [callEntryStateHOLFinite]; rw [hs5_eq]
                      have hba_m : m.baseAddr = s.baseAddr := by
                        dsimp only [m]; rw [hs8_eq]; dsimp only; rw [heff_mzg.baseAddr]
                        change fmaPost.baseAddr = _; rw [hfmaPost_eq]; dsimp only [callEntryStateHOLFinite]; rw [hs5_eq]
                      exact guestInv_congr hcode_m hma_m hsh_m hba_m hInv.1.1
                    have hfm_m : globN s "frame_mem_ptr" ≤ globN m "frame_mem_ptr" := by
                      rw [hm_fp_glob, hqw_nat, hfp_nat]; omega
                    have hAm : ArenaReady m := by
                      refine ⟨hm_G, ?_⟩
                      unfold ArenaOK
                      have hhp_m : globN m "heap_ptr" = globN s "heap_ptr" :=
                        R16Shards.OpHandlers.globN_eq_of_lookup_eq (hm_other_glob "heap_ptr" (by decide))
                      have hsp_m : globN m "scratch_ptr" = globN s "scratch_ptr" :=
                        R16Shards.OpHandlers.globN_eq_of_lookup_eq (hm_other_glob "scratch_ptr" (by decide))
                      rw [hhp_m, hm_fp_glob, hsp_m]
                      have hA := hInv.1.2
                      have hss_le_fp : scratchStart ≤ globN s "frame_mem_ptr" := hA.2.2.1
                      exact ⟨hA.1, hA.2.1, by rw [hqw_nat, hfp_nat]; omega, by rw [← hsp_g_nat]; exact hqw_le_sp,
                        hA.2.2.2.2.1, hA.2.2.2.2.2.1, hqw_al8, hA.2.2.2.2.2.2.2.1,
                        globalsWord_update (ofString "frame_mem_ptr") qw hm_glob hA.2.2.2.2.2.2.2.2⟩
                    have heff_s_s6 : FrameMemByteEff s s6 [freshIvl, (globN s "ev", 280), (memW s (globN s "ev" + 24), memW s (globN s "ev" + 40))] :=
                      ⟨hs6_code.trans hcode.symm,
                       hs6_ma.trans hInv.1.1.memaddrs.symm,
                       by change fmaPost.shMemaddrs = _; rw [hfmaPost_eq]; dsimp only [callEntryStateHOLFinite]; rw [hs5_eq],
                       by change fmaPost.baseAddr = _; rw [hfmaPost_eq]; dsimp only [callEntryStateHOLFinite]; rw [hs5_eq],
                       by change fmaPost.be = _; rw [hfmaPost_eq]; dsimp only [callEntryStateHOLFinite]; rw [hs5_eq],
                       fun g hg => by
                         change fmaPost.globals.lookup (ofString g) = _; rw [hfmaPost_eq]
                         dsimp only [callEntryStateHOLFinite]; rw [hs5_eq]
                         simp [HolFiniteMapExact.lookup_update, FUPDATE, hg, Ne.symm hg],
                       fun a _ => by rw [hs6_mem],
                       fun a _ => by rw [hs6_mem],
                       fun b _ _ => by
                         unfold memB; rw [hs6_mem]
                         have hbe6 : s6.be = s.be := by
                           change fmaPost.be = _; rw [hfmaPost_eq]; dsimp only [callEntryStateHOLFinite]; rw [hs5_eq]
                         rw [hbe6]⟩
                    have heff_m : FrameMemByteEff s m
                        [freshIvl, (globN s "ev", 280), (memW s (globN s "ev" + 24), memW s (globN s "ev" + 40))] := by
                      have h1 := (FrameMemByteEff.of_bre heff_mzg).mono
                        (R2 := [freshIvl, (globN s "ev", 280), (memW s (globN s "ev" + 24), memW s (globN s "ev" + 40))])
                        (fun x hx => by simp at hx; subst hx; exact ⟨freshIvl, by simp, le_refl _, le_refl _⟩)
                      have h2 := (FrameMemByteEff.of_bre heff_st40).mono
                        (R2 := [freshIvl, (globN s "ev", 280), (memW s (globN s "ev" + 24), memW s (globN s "ev" + 40))])
                        (fun x hx => by simp at hx; subst hx; exact ⟨(globN s "ev", 280), by simp, le_refl _, le_refl _⟩)
                      exact ((heff_s_s6.trans h1).trans h2).with_locals_clock m.locals s8.clock
                    have hs7_e0_eq : ∀ off, off + 8 ≤ 280 → off % 8 = 0 →
                        memW s7 (globN s "ev" + off) = memW s (globN s "ev" + off) := by
                      intro off hoff hoff8
                      unfold memW
                      rw [heff_mzg.cell_frame (BitVec.ofNat 64 (globN s "ev" + off)), hs6_mem]
                      intro x hx; simp at hx; subst hx
                      have htn : (BitVec.ofNat 64 (globN s "ev" + off)).toNat = globN s "ev" + off :=
                        Nat.mod_eq_of_lt (by omega)
                      rw [htn]
                      have he0_8 : (globN s "ev") % 8 = 0 := (hFW0.1 (globN s "ev", 280) (by simp)).2.1
                      have ha8 : (globN s "ev" + off) % 8 = 0 := by omega
                      have hfp_s_8 : globN s "frame_mem_ptr" % 8 = 0 := hInv.1.2.2.2.2.2.2.2.1
                      obtain ⟨he0_scr, _⟩ := (hFW0.1 (globN s "ev", 280) (by simp)).1
                      exact not_cellHits_of_disj_aligned (i := (globN s "ev", 280)) ha8 hfp_s_8
                        (Nat.le_add_right _ off) (Nat.add_le_add_left hoff _)
                        (Or.inr (Or.inr (Or.inr (by dsimp only [freshIvl] at he0_scr ⊢; omega))))
                    have hm_e0_other : ∀ off, off + 8 ≤ 280 → off % 8 = 0 → off ≠ 32 → off ≠ 40 →
                        memW m (globN s "ev" + off) = memW s (globN s "ev" + off) := by
                      intro off hoff hoff8 _ hne40
                      change memW s8 (globN s "ev" + off) = memW s (globN s "ev" + off)
                      rw [hs8_eq, R14Shards.OpHandlersA.memW_updW_ne s7 (globN s "ev" + 40) (globN s "ev" + off) _ (by omega) (by omega) (by omega),
                          hs7_e0_eq off hoff hoff8]
                    have hm_e0_40 : memW m (globN s "ev" + 40) = ncapw.toNat := by
                      change memW s8 (globN s "ev" + 40) = ncapw.toNat
                      rw [hs8_eq, R14Shards.OpHandlersA.memW_updW_same s7 (globN s "ev" + 40) ncapw]
                    have hfresh_m : freshIvl = (0, 0) ∨
                        (freshIvl.1 % 8 = 0 ∧ freshIvl.2 % 8 = 0 ∧
                          Inside freshIvl (globN s "frame_mem_ptr") (globN m "frame_mem_ptr")) := by
                      refine Or.inr ⟨hInv.1.2.2.2.2.2.2.2.1, hdiff_al8, ?_⟩
                      rw [hm_fp_glob, hqw_nat, hfp_nat]; dsimp only [freshIvl, Inside]; omega
                    have hnew_m :
                        (freshIvl.2 = 0 ∧ memW m (globN s "ev" + 40) = memW s (globN s "ev" + 40)) ∨
                        (freshIvl.2 ≠ 0 ∧
                          memW s (globN s "ev" + 24) + memW s (globN s "ev" + 40) = freshIvl.1 ∧
                          memW m (globN s "ev" + 40) = memW s (globN s "ev" + 40) + freshIvl.2) := by
                      refine Or.inr ⟨by dsimp only [freshIvl]; omega, hmem_end_fp, ?_⟩
                      rw [hm_e0_40]; dsimp only [freshIvl]; omega
                    have hm_loc_s5 : ∀ k, k ≠ ofString "ncap" → m.locals.lookup k = s5.locals.lookup k := by
                      intro k hk
                      have hres_ne : ∀ (mp : HolFiniteMapExact MlS (ValueHOL 64)) (key q : MlS) (old : Option (ValueHOL 64)),
                          key ≠ q → (mp.resVarEq (key, old)).lookup q = mp.lookup q := by
                        intro mp key q old hne
                        unfold HolFiniteMapExact.resVarEq
                        cases old with
                        | none => simp [HolFiniteMapExact.eraseEq, FDOMSUB_HOL, hne.symm]
                        | some v => simp [HolFiniteMapExact.updateEq, FUPDATE_HOL, hne.symm]
                      have hs8_l : s8.locals = s5.locals := by rw [hs8_eq]; exact hs7_loc
                      dsimp only [m]
                      rw [hres_ne _ _ _ _ hk.symm, hs8_l]
                    have hnt_m : (evaluateHOLFiniteState m tailProg).1 ≠ some .timeOut := by
                      dsimp only [m]
                      exact hnt
                    exact run_tail m freshIvl hAm hfm_m hm_other_glob heff_m hfresh_m hm_e0_other hnew_m
                      (by rw [hm_e0_40]; exact hnlen_le_ncap)
                      (by rw [hm_loc_s5 (ofString "len") (by decide)]; exact hs5_len)
                      (by rw [hm_loc_s5 (ofString "nlen") (by decide)]; exact hs5_nlen)
                      (by rw [hm_loc_s5 (ofString "expand_by") (by decide)]; exact hs5_eb)
                      hnt_m
        · have hnlen_le_cap : nlenw.toNat ≤ capw.toNat := by
            rw [BitVec.lt_def] at hgrow; omega
          simp only [hgrow, ↓reduceIte, evaluateHOLFiniteState_skip] at hnt ⊢
          exact run_tail s3 (0, 0)
            ⟨guestInv_congr (s := s) rfl rfl rfl rfl hInv.1.1, hInv.1.2⟩
            (le_refl _)
            (fun _ _ => rfl)
            ((FrameMemByteEff.refl s _).with_locals_clock s3.locals s.clock)
            (Or.inl rfl)
            (fun _ _ _ _ _ => rfl)
            (Or.inl ⟨rfl, rfl⟩)
            (by change nlenw.toNat ≤ memW s (globN s "ev" + 40); rw [← hcapw_eq]; exact hnlen_le_cap)
            hs3_len hs3_nlen hs3_eb hnt


end InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB
