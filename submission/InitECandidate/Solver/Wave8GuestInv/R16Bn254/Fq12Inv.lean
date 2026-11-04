import InitECandidate.Solver.Wave8GuestInv.R16ArithPort.BitFqSmallLeaves
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.FqPolyDivisionStationary
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Fq12InvBuffers
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqPolyOuterProgress
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqPolyCofactorBound
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.DecOnInit

/-! Complete bounded termination proof `fb_fq12_inv` on `GuestInv`.
Combines:
1. `Fq12InvBuffers` (`alloc(416)`, `heap_mark`, `memzero`, `memcpy`, 6-buffer disjointness & canonical cofactors),
2. `FqPolyDivisionStationary` (`polyDivLoop_stationary_bounded` + `polyDivPreparedLoop_gen_none`),
3. `FqPolyOuterProgress` + `FqPolyCofactorBound` (strict outer rank drop `polyOuterRank <` across `polyCofactorRun polyCofactorFinish`),
4. Post-loop normalization loop (`while_up_unsigned_const_on`).
Zero `LeafStatements.lean` dependency, standard Lean kernel foundations only. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.R16Bn254

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Encoders.Asm
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.GuestUniformClockBound
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanTerminatingCombinators
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
open InitECandidate.Solver.Wave8GuestInv.P13.Callees (fb_heap_mark fb_heap_release fb_memcpy fb_memzero)
open InitECandidate.Solver.Wave8GuestInv.R16ArithPort (fb_fq_inv)

/-! ### 1. Exact `decCall_on_returned` combinator & monotonic bound adapters -/

/-- `decCall` combinator exposing the exact callee return execution to `hresume`. -/
theorem TerminatingProgBoundedOn.decCall_on_returned
    {P Pk : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {fname : MlS} {B Bc : Nat}
    (hf : TerminatingFunBoundedOn GuestInv fname B)
    (hPG : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → GuestInv s)
    (name : MlS) (shape : ShapeHOL) (arguments : List (ExpHOL 64))
    {continuation : ProgHOL 64} (hcont : TerminatingProgBoundedOn Pk continuation Bc)
    (hresume : ∀ {F : Type} (state bpost : PanSemStateFiniteExact 64 F)
      (values : List (ValueHOL 64)) (body : ProgHOL 64)
      (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret' : ShapeHOL) (value : ValueHOL 64),
      state.code = originalRuntimeCode → P state →
      evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
        some values →
      lookupCodeHOLFinite state.code.lookup fname values = some (body, callee, ret') →
      evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body =
        (some (.returned value), bpost) →
      Pk (setVarHOLFinite name value { bpost with locals := state.locals })) :
    TerminatingProgBoundedOn P (.decCall name shape fname arguments continuation)
      (B + Bc + 1) := by
  obtain ⟨params, body0, ret0, hlook, hbody⟩ := hf
  have hentry : CallEntryOn P GuestInv fname arguments :=
    fun s _ _ callee _ _ hPs _ _ => guestInv_callEntry s callee (hPG s hPs)
  intro F state hcode hP hnt
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt ⊢
  rcases hargs : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments with
    _ | values
  · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
  · simp only [hargs] at hnt ⊢
    rcases hl : lookupCodeHOLFinite state.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · exact ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
    · simp only [hl] at hnt ⊢
      obtain ⟨hbb, hrunBound⟩ := callee_body_bound hlook hbody hentry state hcode hP values body'
        callee ret' hargs hl
      subst hbb
      by_cases hz : state.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt ⊢
        have hmeta := (evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state callee)
          body').1
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body' with
          ⟨res, post⟩
        simp only [hrun] at hnt hmeta ⊢
        change post.code = state.code at hmeta
        have bodyClock (hsafe : res ≠ some .timeOut) :
            state.clock - 1 ≤ post.clock + B ∧ post.clock ≤ state.clock - 1 := by
          have hb := hrunBound (by rw [hrun]; exact hsafe)
          rw [hrun] at hb
          exact hb
        cases res with
        | none =>
          obtain ⟨hs, hk⟩ := bodyClock (by simp)
          exact ⟨by (try dsimp only); omega, by (try dsimp only); omega⟩
        | some r =>
          cases r with
          | returned value =>
            obtain ⟨hs, hk⟩ := bodyClock (by simp)
            by_cases hsh : (shapeEqHOL (shapeOfHOLExact value) shape &&
                shapeEqHOL (shapeOfHOLExact value) ret') = true
            · simp only [hsh, ↓reduceIte] at hnt ⊢
              set resumed := setVarHOLFinite name value { post with locals := state.locals }
              have hresCode : resumed.code = originalRuntimeCode := hmeta.trans hcode
              have hresPk : Pk resumed :=
                hresume state post values body' callee ret' value hcode hP hargs hl hrun
              obtain ⟨hsc, hkc⟩ := hcont resumed hresCode hresPk hnt
              change post.clock ≤ (evaluateHOLFiniteState resumed continuation).2.clock + Bc at hsc
              change (evaluateHOLFiniteState resumed continuation).2.clock ≤ post.clock at hkc
              exact ⟨by omega, by omega⟩
            · simp only [hsh, Bool.false_eq_true, ↓reduceIte]
              exact ⟨by omega, by omega⟩
          | timeOut => simp at hnt
          | «break» =>
            obtain ⟨hs, hk⟩ := bodyClock (by simp)
            exact ⟨by (try dsimp only); omega, by (try dsimp only); omega⟩
          | «continue» =>
            obtain ⟨hs, hk⟩ := bodyClock (by simp)
            exact ⟨by (try dsimp only); omega, by (try dsimp only); omega⟩
          | error =>
            obtain ⟨hs, hk⟩ := bodyClock (by simp)
            exact ⟨by simp [emptyLocalsHOLFinite]; omega, by simp [emptyLocalsHOLFinite]; omega⟩
          | exception _ _ =>
            obtain ⟨hs, hk⟩ := bodyClock (by simp)
            exact ⟨by simp [emptyLocalsHOLFinite]; omega, by simp [emptyLocalsHOLFinite]; omega⟩
          | finalFfi _ =>
            obtain ⟨hs, hk⟩ := bodyClock (by simp)
            exact ⟨by simp [emptyLocalsHOLFinite]; omega, by simp [emptyLocalsHOLFinite]; omega⟩

private theorem bound_mono {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {p : ProgHOL 64} {B1 B2 : Nat} (hle : B1 ≤ B2) (h : TerminatingProgBoundedOn P p B1) :
    TerminatingProgBoundedOn P p B2 := by
  intro F s hc hp hnt
  obtain ⟨h1, h2⟩ := h s hc hp hnt
  exact ⟨by omega, h2⟩

private theorem bound_zero_add {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {p : ProgHOL 64} {B : Nat} (h : TerminatingProgBoundedOn P p (0 + B)) :
    TerminatingProgBoundedOn P p B :=
  bound_mono (by omega) h

private theorem bound_add_zero {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {p : ProgHOL 64} {B : Nat} (h : TerminatingProgBoundedOn P p (B + 0)) :
    TerminatingProgBoundedOn P p B :=
  bound_mono (by omega) h

private theorem bound_imp {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {p : ProgHOL 64} {B : Nat}
    (himp : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → Q s)
    (h : TerminatingProgBoundedOn Q p B) :
    TerminatingProgBoundedOn P p B :=
  fun s hc hp => h s hc (himp s hp)

private theorem straight_on {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (p : ProgHOL 64) (hp : extStraightLine p = true) :
    TerminatingProgBoundedOn P p 0 :=
  fun s hc _ => TerminatingProgBounded.straight p hp s hc

private theorem seq_straight_on {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {first second : ProgHOL 64} {B : Nat}
    (h1 : extStraightLine first = true)
    (hp : ∀ {F : Type} (state mid : PanSemStateFiniteExact 64 F),
      state.code = originalRuntimeCode → P state →
      evaluateHOLFiniteState state first = (none, mid) → Q mid)
    (h2 : TerminatingProgBoundedOn Q second B) :
    TerminatingProgBoundedOn P (.seq first second) B :=
  bound_zero_add (@TerminatingProgBoundedOn.seq_on_none P Q first second 0 B (straight_on first h1) hp h2)

/-! ### 2. Six-buffer invariant for the outer polynomial GCD loop -/

def BufOk (b : BitVec 64) : Prop :=
  b.toNat % 8 = 0 ∧ sourceBase ≤ b.toNat ∧ b.toNat + 416 ≤ heapEnd

def SixDistinct {α : Type} (b0 b1 b2 b3 b4 b5 : α) : Prop :=
  b0 ≠ b1 ∧ b0 ≠ b2 ∧ b0 ≠ b3 ∧ b0 ≠ b4 ∧ b0 ≠ b5 ∧
  b1 ≠ b2 ∧ b1 ≠ b3 ∧ b1 ≠ b4 ∧ b1 ≠ b5 ∧
  b2 ≠ b3 ∧ b2 ≠ b4 ∧ b2 ≠ b5 ∧
  b3 ≠ b4 ∧ b3 ≠ b5 ∧
  b4 ≠ b5

/-- Outer-loop state invariant: `GuestInv` plus 6 aligned, in-domain, pairwise-disjoint 416-byte
buffers `r0, r1, s0, s1, q, tmp` with canonical cofactors at `s0` and `s1`. -/
structure Fq12OuterInv {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop where
  guest : GuestInv s
  buffers : ∃ (r0 r1 s0 s1 q tmp : BitVec 64) (S0 S1 : Nat → Limbs256),
    s.locals.lookup (ofString "r0") = some (.val (.word r0)) ∧
    s.locals.lookup (ofString "r1") = some (.val (.word r1)) ∧
    s.locals.lookup (ofString "s0") = some (.val (.word s0)) ∧
    s.locals.lookup (ofString "s1") = some (.val (.word s1)) ∧
    s.locals.lookup (ofString "q") = some (.val (.word q)) ∧
    s.locals.lookup (ofString "tmp") = some (.val (.word tmp)) ∧
    BufOk r0 ∧ BufOk r1 ∧ BufOk s0 ∧ BufOk s1 ∧ BufOk q ∧ BufOk tmp ∧
    (∀ x y, x ∈ [r0, r1, s0, s1, q, tmp] → y ∈ [r0, r1, s0, s1, q, tmp] → x ≠ y →
      PolynomialDisjoint x y) ∧
    SixDistinct r0 r1 s0 s1 q tmp ∧
    CanonicalPolynomial S0 ∧ CanonicalPolynomial S1 ∧
    MemoryPolynomial s.memory s0 S0 ∧ MemoryPolynomial s.memory s1 S1

private theorem fq12OuterInv_decClock {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : Fq12OuterInv s) : Fq12OuterInv (decClockHOLFinite s) :=
  ⟨guestInv_congr (s := s) rfl rfl rfl rfl h.guest, h.buffers⟩

private theorem extentFrame_preserves_polynomial {F : Type}
    {s0 s : PanSemStateFiniteExact 64 F} {dst b : BitVec 64} {n : BitVec 64}
    {P : Nat → Limbs256}
    (hef : ExtentFrame s0 s dst n)
    (hal_dst : dst.toNat % 8 = 0)
    (hal_b : b.toNat % 8 = 0)
    (hb : b.toNat + 416 ≤ 2 ^ 64)
    (hdisj : dst.toNat + n.toNat ≤ b.toNat ∨ b.toNat + 416 ≤ dst.toNat)
    (hm : MemoryPolynomial s0.memory b P) :
    MemoryPolynomial s.memory b P := by
  intro i hi
  have hcell : ∀ off : Nat, off < 32 → off % 8 = 0 →
      s.memory (coefficientAddress b i + BitVec.ofNat 64 off) =
        s0.memory (coefficientAddress b i + BitVec.ofNat 64 off) := by
    intro off hoff hm8
    by_contra hne
    obtain ⟨_, hlo, hhi⟩ := hef.2 _ hne
    have hnat : (coefficientAddress b i + BitVec.ofNat 64 off).toNat = b.toNat + 32 * i + off := by
      simp only [coefficientAddress, BitVec.add_assoc, ← BitVec.ofNat_add]
      rw [BitVec.toNat_add_of_lt]
      · simp only [BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt (by omega)]; omega
      · simp only [BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt (by omega)]; omega
    rw [hnat] at hlo hhi
    rcases hdisj with hd | hd <;> omega
  rcases hm i hi with ⟨m0, m1, m2, m3⟩
  have hc0 : s.memory (coefficientAddress b i) = s0.memory (coefficientAddress b i) := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hcell 0 (by decide) (by decide)
  exact ⟨hc0.trans m0,
    (hcell 8 (by decide) (by decide)).trans m1,
    (hcell 16 (by decide) (by decide)).trans m2,
    (hcell 24 (by decide) (by decide)).trans m3⟩

private theorem nonoverlap_of_polynomialDisjoint (a b : BitVec 64)
    (hal_a : a.toNat % 8 = 0) (hal_b : b.toNat % 8 = 0)
    (_hw_a : a.toNat + 416 ≤ 2 ^ 64) (_hw_b : b.toNat + 416 ≤ 2 ^ 64)
    (hd : PolynomialDisjoint a b) :
    a.toNat + 416 ≤ b.toNat ∨ b.toNat + 416 ≤ a.toNat := by
  by_contra hnot
  have hnot' : b.toNat < a.toNat + 416 ∧ a.toNat < b.toNat + 416 := by omega
  let m := max a.toNat b.toNat
  have hm_al : m % 8 = 0 := by
    dsimp [m]; by_cases h : a.toNat ≤ b.toNat <;> simp [Nat.max_def, h, hal_a, hal_b]
  let ja := (m - a.toNat) / 32
  let ua := (m - a.toNat) % 32
  let jb := (m - b.toNat) / 32
  let ub := (m - b.toNat) % 32
  have hja : ja < 13 := by dsimp [ja, m]; omega
  have hjb : jb < 13 := by dsimp [jb, m]; omega
  have hua : ua = 0 ∨ ua = 8 ∨ ua = 16 ∨ ua = 24 := by dsimp [ua, m]; omega
  have hub : ub = 0 ∨ ub = 8 ∨ ub = 16 ∨ ub = 24 := by dsimp [ub, m]; omega
  have hxa : BitVec.ofNat 64 m ∈ u256Addresses (coefficientAddress a ja) := by
    have heq : BitVec.ofNat 64 m = coefficientAddress a ja + BitVec.ofNat 64 ua := by
      apply BitVec.eq_of_toNat_eq
      simp only [coefficientAddress, BitVec.add_assoc, ← BitVec.ofNat_add]
      rw [BitVec.toNat_add_of_lt]
      · simp only [BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt (show m < 2 ^ 64 by dsimp [m]; omega),
            Nat.mod_eq_of_lt (show 32 * ja + ua < 2 ^ 64 by dsimp [ja, ua, m]; omega)]
        dsimp [ja, ua, m]; omega
      · simp only [BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt (show 32 * ja + ua < 2 ^ 64 by dsimp [ja, ua, m]; omega)]
        dsimp [ja, ua, m]; omega
    rw [heq]; simp only [u256Addresses, List.mem_cons]
    rcases hua with h | h | h | h <;> rw [h] <;> simp
  have hxb : BitVec.ofNat 64 m ∈ u256Addresses (coefficientAddress b jb) := by
    have heq : BitVec.ofNat 64 m = coefficientAddress b jb + BitVec.ofNat 64 ub := by
      apply BitVec.eq_of_toNat_eq
      simp only [coefficientAddress, BitVec.add_assoc, ← BitVec.ofNat_add]
      rw [BitVec.toNat_add_of_lt]
      · simp only [BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt (show m < 2 ^ 64 by dsimp [m]; omega),
            Nat.mod_eq_of_lt (show 32 * jb + ub < 2 ^ 64 by dsimp [jb, ub, m]; omega)]
        dsimp [jb, ub, m]; omega
      · simp only [BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt (show 32 * jb + ub < 2 ^ 64 by dsimp [jb, ub, m]; omega)]
        dsimp [jb, ub, m]; omega
    rw [heq]; simp only [u256Addresses, List.mem_cons]
    rcases hub with h | h | h | h <;> rw [h] <;> simp
  exact hd ja hja jb hjb (BitVec.ofNat 64 m) hxb hxa

private theorem twoBufferFrame_preserves (before after : BitVec 64 → HolWordLab 64)
    (a q b : BitVec 64) (B : Nat → Limbs256)
    (hf : ∀ x, PolynomialOutside a x → PolynomialOutside q x → after x = before x)
    (hda : PolynomialDisjoint a b) (hdq : PolynomialDisjoint q b)
    (hm : MemoryPolynomial before b B) : MemoryPolynomial after b B := by
  intro k hk
  have he : ∀ x ∈ u256Addresses (coefficientAddress b k), after x = before x := by
    intro x hx
    exact hf x (fun j hj => hda j hj k hk x hx) (fun j hj => hdq j hj k hk x hx)
  rcases hm k hk with ⟨h0, h1, h2, h3⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals rw [he _ (by simp [u256Addresses])]
  all_goals assumption

private theorem canonical_zero_poly : CanonicalPolynomial (fun _ => fqZeroLimbs) := by
  intro _ _
  dsimp only
  have hpos : 0 < fqModulus.toNat := Nat.lt_trans (by decide) fqModulus_gt_one
  have hz : fqZeroLimbs.toNat = 0 := by decide
  omega

private def fqMontOne : Limbs256 :=
  ⟨15230403791020821917, 754611498739239741, 7381016538464732716, 1011752739694698287⟩

private theorem fqMontOne_lt : fqMontOne.toNat < fqModulus.toNat := by decide

private theorem canonical_montOne_poly :
    CanonicalPolynomial (fun i => if i = 0 then fqMontOne else fqZeroLimbs) := by
  intro i hi
  by_cases h0 : i = 0
  · subst h0; simp only [↓reduceIte]; exact fqMontOne_lt
  · simp only [h0, ↓reduceIte]; exact canonical_zero_poly i hi

/-! ### 3. Store helper for the prefix initialization -/

private theorem store_rstruct4_domain_and_frame {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (addrExp : ExpHOL 64)
    (w0 w1 w2 w3 : BitVec 64) (addr : BitVec 64)
    (hG : GuestInv s)
    (haddr : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) addrExp =
      some (.val (.word addr)))
    (hr : evaluateHOLFiniteState s
      (.store addrExp (.rstruct [.const w0, .const w1, .const w2, .const w3])) = (none, post)) :
    addr.toNat % 8 = 0 ∧ sourceBase ≤ addr.toNat ∧
    post.locals = s.locals ∧ post.globals = s.globals ∧
    post.memory = writeU256 s.memory addr ⟨w0, w1, w2, w3⟩ := by
  have hv : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.rstruct [.const w0, .const w1, .const w2, .const w3]) =
      some (Limbs256.toValue ⟨w0, w1, w2, w3⟩) := by
    simp [evalHOLExact, evalListHOLExact, Limbs256.toValue]
  have hr0 := hr
  rw [evaluateHOLFiniteState_store, haddr, hv] at hr0
  dsimp only at hr0
  have hd : DomainU256 s.memaddrs addr := by
    unfold DomainU256
    simp only [limbs256_flatten, panMemStoresHOL, panMemStoreHOL, panBytesInWord, BitVec.add_assoc] at hr0
    by_cases h0 : s.memaddrs addr
    · simp only [h0, ↓reduceIte] at hr0
      by_cases h1 : s.memaddrs (addr + 8#64)
      · simp only [h1, ↓reduceIte] at hr0
        by_cases h2 : s.memaddrs (addr + 8#64 + 8#64)
        · simp only [h2, ↓reduceIte] at hr0
          by_cases h3 : s.memaddrs (addr + 8#64 + 8#64 + 8#64)
          · have h16 : (8#64 : BitVec 64) + 8#64 = 16 := rfl
            have h24 : (8#64 : BitVec 64) + (8#64 + 8#64) = 24 := rfl
            exact ⟨h0, h1, by rw [BitVec.add_assoc, h16] at h2; exact h2,
              by rw [BitVec.add_assoc, BitVec.add_assoc, h24] at h3; exact h3⟩
          · simp [h3] at hr0
        · simp [h2] at hr0
      · simp [h1] at hr0
    · simp [h0] at hr0
  have hord0 : ordinaryDomain addr := by rw [← hG.memaddrs]; exact hd.1
  obtain ⟨hal, hlo, _⟩ := (ordinaryDomain_iff_local addr).mp hord0
  have hst := eval_store_u256 s addrExp (.rstruct [.const w0, .const w1, .const w2, .const w3])
    addr ⟨w0, w1, w2, w3⟩ haddr hv hd
  have hpost_eq : post = { s with memory := writeU256 s.memory addr ⟨w0, w1, w2, w3⟩ } :=
    (Prod.mk.inj (hr.symm.trans hst)).2
  subst hpost_eq
  exact ⟨hal, hlo, rfl, rfl, rfl⟩

/-! ### 4. Source sub-programs of `guestFn_fq12_inv` -/

def fq12InvBody : ProgHOL 64 := arithSourceBody Guest.Software.guestFn_fq12_inv

def fq12InvAfterAllocs : ProgHOL 64 :=
  polyDivSourceAt fq12InvBody [false, false, false, false, false, false, false]

def fq12InvMainSeq : ProgHOL 64 :=
  polyDivSourceAt fq12InvAfterAllocs [true, true, true, true, true, true, true, true, true]

def fq12OuterLoop : ProgHOL 64 := polyDivSourceAt fq12InvMainSeq [false]

def fq12OuterBody : ProgHOL 64 := polyDivSourceAt fq12OuterLoop [false]

def fq12PostLoop : ProgHOL 64 := polyDivSourceAt fq12InvMainSeq [true]

/-! ### 5. `alloc(416)` lookup helper & initialization prefix -/

private theorem lookup_alloc_local :
    originalRuntimeCode.lookup (ofString "alloc") =
      some ([(ofString "n", .one)], sourceFnBody Guest.Software.guestFn_alloc, .one) :=
  lookup_of_guestAst_getElem 7 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_alloc) rfl

private theorem alloc416_lookup_callee {F : Type} (s bpost : PanSemStateFiniteExact 64 F)
    (values : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret' : ShapeHOL) (value : ValueHOL 64)
    (hc : s.code = originalRuntimeCode)
    (hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [.const 416] =
      some values)
    (hl : PanSemStateFiniteExact.lookupCodeHOLFinite s.code.lookup (ofString "alloc") values = some (body, callee, ret'))
    (hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
      (some (.returned value), bpost)) :
    ∃ p q : BitVec 64,
      value = .val (.word p) ∧
      s.globals.lookup (ofString "heap_ptr") = some (.val (.word p)) ∧
      bpost.globals.lookup (ofString "heap_ptr") = some (.val (.word q)) ∧
      bpost.memory = s.memory ∧
      q.toNat ≤ heapLimit ∧
      (p.toNat + 423 < 2 ^ 64 →
        p.toNat + 416 ≤ q.toNat ∧ q.toNat % 8 = 0) := by
  have hv : values = [.val (.word 416)] := by
    simpa [evalListHOLFinite, evalListHOLExact, evalHOLExact] using hargs.symm
  subst hv
  have hraw : lookupCodeHOLExact originalRuntimeCode.lookup (ofString "alloc") [.val (.word 416)] =
      some (sourceFnBody Guest.Software.guestFn_alloc,
        (fun key => if key = ofString "n" then some (.val (.word 416)) else none), .one) := by
    simp [lookupCodeHOLExact, lookup_alloc_local, shapeEqHOL, shapeOfHOLExact]
  have hlk_eq : PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "alloc") [.val (.word 416)] =
      some (sourceFnBody Guest.Software.guestFn_alloc,
        HolFiniteMapExact.empty.update (ofString "n", .val (.word 416)), .one) := by
    unfold PanSemStateFiniteExact.lookupCodeHOLFinite
    split
    · rename_i hmiss; rw [hraw] at hmiss; cases hmiss
    · rename_i eb el ers hfound
      have hinj := Option.some.inj (hfound.symm.trans hraw)
      obtain ⟨rfl, hinj2⟩ := Prod.mk.inj hinj
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hinj2
      apply congrArg (fun locals => some (sourceFnBody Guest.Software.guestFn_alloc, locals, ShapeHOL.one))
      apply HolFiniteMapExact.ext
      funext key
      by_cases hk : key = ofString "n"
      · subst key; simp [HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty]
      · simp [hk, Ne.symm hk, HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty, FEMPTY]
  rw [hc] at hl
  change PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup _ _ = _ at hl
  rw [hlk_eq] at hl
  obtain ⟨rfl, hinj2⟩ := Prod.mk.inj (Option.some.inj hl)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hinj2
  obtain ⟨p, q, hret, hp_g, hq_g, hmem, _, hq_le, hprops⟩ :=
    alloc416_callee_returned (callEntryStateHOLFinite s (HolFiniteMapExact.empty.update (ofString "n", .val (.word 416))))
      bpost value hc
      (by simp [callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, HolFiniteMapExact.empty])
      hrun
  exact ⟨p, q, hret, hp_g, hq_g, hmem, hq_le, fun hf => ⟨(hprops hf).1, (hprops hf).2.2⟩⟩

/-- State after the 6 `alloc(416)` declarations, recording the allocated pointer chain. -/
def AfterAllocsInv {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  GuestInv s ∧
  ∃ r0 r1 s0 s1 q tmp q5 : BitVec 64,
    s.locals.lookup (ofString "r0") = some (.val (.word r0)) ∧
    s.locals.lookup (ofString "r1") = some (.val (.word r1)) ∧
    s.locals.lookup (ofString "s0") = some (.val (.word s0)) ∧
    s.locals.lookup (ofString "s1") = some (.val (.word s1)) ∧
    s.locals.lookup (ofString "q") = some (.val (.word q)) ∧
    s.locals.lookup (ofString "tmp") = some (.val (.word tmp)) ∧
    (r0.toNat + 423 < 2 ^ 64 → r0.toNat + 416 ≤ r1.toNat ∧ r1.toNat % 8 = 0) ∧
    r1.toNat ≤ heapLimit ∧
    r1.toNat + 416 ≤ s0.toNat ∧ s0.toNat % 8 = 0 ∧
    s0.toNat + 416 ≤ s1.toNat ∧ s1.toNat % 8 = 0 ∧
    s1.toNat + 416 ≤ q.toNat ∧ q.toNat % 8 = 0 ∧
    q.toNat + 416 ≤ tmp.toNat ∧ tmp.toNat % 8 = 0 ∧
    tmp.toNat + 416 ≤ q5.toNat ∧ q5.toNat ≤ heapLimit

private theorem fq12AfterAllocs_eq :
    fq12InvAfterAllocs =
      .seq (.call (some (none, none)) (ofString "memzero") [.var .local (ofString "r0"), .const 416])
      (.seq (.store (.var .local (ofString "r0"))
          (.rstruct [.const 5544790254283102953, .const 13698472384431417117,
            .const 4628036095437277618, .const 2762764518496934255]))
      (.seq (.store (.op .add [.var .local (ofString "r0"), .const 192])
          (.rstruct [.const 10102850021236865696, .const 15026249742141879542,
            .const 2169086236411634456, .const 2710440286313254821]))
      (.seq (.store (.op .add [.var .local (ofString "r0"), .const 384])
          (.rstruct [.const 15230403791020821917, .const 754611498739239741,
            .const 7381016538464732716, .const 1011752739694698287]))
      (.seq (.call (some (none, none)) (ofString "memzero") [.var .local (ofString "r1"), .const 416])
      (.seq (.call (some (none, none)) (ofString "memcpy")
          [.var .local (ofString "r1"), .var .local (ofString "a"), .const 384])
      (.seq (.call (some (none, none)) (ofString "memzero") [.var .local (ofString "s0"), .const 416])
      (.seq (.call (some (none, none)) (ofString "memzero") [.var .local (ofString "s1"), .const 416])
      (.seq (.store (.var .local (ofString "s1"))
          (.rstruct [.const 15230403791020821917, .const 754611498739239741,
            .const 7381016538464732716, .const 1011752739694698287]))
        fq12InvMainSeq)))))))) := rfl

private theorem pairwise_disjoint_of_chain (r0 r1 s0 s1 q tmp : BitVec 64)
    (h01 : r0.toNat + 416 ≤ r1.toNat) (h12 : r1.toNat + 416 ≤ s0.toNat)
    (h23 : s0.toNat + 416 ≤ s1.toNat) (h34 : s1.toNat + 416 ≤ q.toNat)
    (h45 : q.toNat + 416 ≤ tmp.toNat) (h5e : tmp.toNat + 416 ≤ heapEnd) :
    (∀ x y, x ∈ [r0, r1, s0, s1, q, tmp] → y ∈ [r0, r1, s0, s1, q, tmp] → x ≠ y →
      PolynomialDisjoint x y) ∧
    SixDistinct r0 r1 s0 s1 q tmp := by
  have hhe64 : heapEnd < 2 ^ 64 := by decide
  have hne : ∀ a b : BitVec 64, a.toNat < b.toNat → a ≠ b := by
    intro a b hlt h; subst h; omega
  have hdist : SixDistinct r0 r1 s0 s1 q tmp :=
    ⟨hne _ _ (by omega), hne _ _ (by omega), hne _ _ (by omega), hne _ _ (by omega), hne _ _ (by omega),
     hne _ _ (by omega), hne _ _ (by omega), hne _ _ (by omega), hne _ _ (by omega),
     hne _ _ (by omega), hne _ _ (by omega), hne _ _ (by omega),
     hne _ _ (by omega), hne _ _ (by omega),
     hne _ _ (by omega)⟩
  refine ⟨?_, hdist⟩
  intro x y hx hy hxy
  have hxw : x.toNat + 416 ≤ 2 ^ 64 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  have hyw : y.toNat + 416 ≤ 2 ^ 64 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  apply polynomialDisjoint_of_nonoverlap x y hxw hyw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact absurd rfl hxy | omega

/-! ### 6. Outer loop body progress & bound -/

def polyOuterBodyCost : Nat :=
  (K.«fq_poly_deg» + 1) + (K.«fq_poly_deg» + 1) + (K.«memzero» + 1) + (K.«fq_inv» + 1) +
  (14 + 1) * ((K.«fq_mul» + 1) + (K.«fq_poly_submul» + 1) + (K.«fq_poly_deg» + 1) + 1) +
  (K.«memcpy» + 1) +
  (13 + 1) * ((K.«u256_is_zero» + 1) + Nat.max (K.«fq_poly_submul» + 1) 0 + 1)

private theorem fq12OuterBody_eq :
    fq12OuterBody =
      .decCall (ofString "d1") .one (ofString "fq_poly_deg") [.var .local (ofString "r1"), .const 13]
        (.seq
          (.ite (.cmp .notLess (.const 0) (.var .local (ofString "d1"))) .break .skip)
          (.decCall (ofString "d0") .one (ofString "fq_poly_deg") [.var .local (ofString "r0"), .const 13]
            (.seq
              (.call (some (none, none)) (ofString "memzero") [.var .local (ofString "q"), .const 416])
              (polyDivPrepare
                (.seq polyDivLoop
                  (.seq
                    (.call (some (none, none)) (ofString "memcpy")
                      [.var .local (ofString "tmp"), .var .local (ofString "s0"), .const 416])
                    (polyCofactorRun polyCofactorFinish))))))) := rfl

private theorem signed_less_zero_eq (right : BitVec 64) :
    holAsmSignedLess 0 right = (0 : BitVec 64).slt right := by
  have bl : (0 : BitVec 64).toNat < 2 ^ 64 := (0 : BitVec 64).isLt
  have br := right.isLt
  simp only [holAsmSignedLess, BitVec.slt_eq_decide, BitVec.toInt_eq_msb_cond,
    BitVec.msb_eq_decide]
  repeat (any_goals first | split)
  all_goals simp_all only [decide_eq_true_eq]
  all_goals apply Bool.eq_iff_iff.mpr
  all_goals simp_all [decide_eq_true_eq]
  all_goals omega

private theorem d1_pos_of_guard_fallthrough (d1w : BitVec 64)
    (B : Nat → Limbs256) (hdeg : PolynomialDegreeValue B (.val (.word d1w)))
    (hnge : wordCmpHOL .notLess 0 d1w = false) :
    ∃ d1 : Nat, 0 < d1 ∧ d1 < 13 ∧ d1w = BitVec.ofNat 64 d1 := by
  have hslt : (0 : BitVec 64).slt d1w = true := by
    have h1 : holAsmSignedLess 0 d1w = true := by
      unfold wordCmpHOL at hnge
      cases h : holAsmSignedLess 0 d1w <;> simp_all
    exact signed_less_zero_eq d1w ▸ h1
  have hlt : (0 : Int) < d1w.toInt := by
    simpa using BitVec.slt_iff_toInt_lt.mp hslt
  obtain ⟨d1, hd1, heq, _, _⟩ := polynomialDegreeValue_nonnegative B d1w hdeg (by omega)
  have hi := degreeIndex_toInt d1 hd1
  exact ⟨d1, by rw [heq, hi] at hlt; omega, hd1, heq⟩

private theorem perm_mem_six {α : Type} {x a b c d e f : α} :
    x ∈ [b, a, d, f, e, c] ↔ x ∈ [a, b, c, d, e, f] := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem perm_sixDistinct {α : Type} {r0 r1 s0 s1 q tmp : α}
    (h : SixDistinct r0 r1 s0 s1 q tmp) :
    SixDistinct r1 r0 s1 tmp q s0 := by
  rcases h with ⟨h01, h02, h03, h04, h05, h12, h13, h14, h15, h23, h24, h25, h34, h35, h45⟩
  exact ⟨h01.symm, h13, h15, h14, h12,
         h03, h05, h04, h02,
         h35, h34, h23.symm,
         h45.symm, h25.symm,
         h24.symm⟩

/-- Normal execution of `fq12OuterBody` from `Fq12OuterInv` preserves `Fq12OuterInv` AND strictly
decreases `polyOuterRank`. -/
theorem fq12OuterBody_none_progress {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (hc : s.code = originalRuntimeCode) (hinv : Fq12OuterInv s)
    (hr : evaluateHOLFiniteState s fq12OuterBody = (none, post)) :
    Fq12OuterInv post ∧ polyOuterRank post < polyOuterRank s := by
  have hG_post : GuestInv post := by
    have := guestInv_evaluate s fq12OuterBody hinv.guest
    rw [hr] at this; exact this
  rw [fq12OuterBody_eq] at hr
  obtain ⟨r0, r1, s0, s1, q, tmp, S0, S1,
    hr0, hr1, hs0, hs1, hq, htmp,
    hb_r0, hb_r1, hb_s0, hb_s1, hb_q, hb_tmp,
    hdisj, hdist, hS0, hS1, hmS0, hmS1⟩ := hinv.buffers
  have hG := hinv.guest
  obtain ⟨hdR0, hwR0, hmR0⟩ := domainPolynomial_of_interval s r0 hG hb_r0.1 hb_r0.2.1 hb_r0.2.2
  obtain ⟨hdR1, hwR1, hmR1⟩ := domainPolynomial_of_interval s r1 hG hb_r1.1 hb_r1.2.1 hb_r1.2.2
  obtain ⟨hdS0, hwS0, _⟩ := domainPolynomial_of_interval s s0 hG hb_s0.1 hb_s0.2.1 hb_s0.2.2
  obtain ⟨hdS1, hwS1, _⟩ := domainPolynomial_of_interval s s1 hG hb_s1.1 hb_s1.2.1 hb_s1.2.2
  obtain ⟨hdQ, hwQ, _⟩ := domainPolynomial_of_interval s q hG hb_q.1 hb_q.2.1 hb_q.2.2
  obtain ⟨hdTmp, hwTmp, _⟩ := domainPolynomial_of_interval s tmp hG hb_tmp.1 hb_tmp.2.1 hb_tmp.2.2
  -- 1. decCall d1 = fq_poly_deg(r1, 13)
  have hargs_d1 : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "r1"), .const 13] = some [.val (.word r1), .val (.word 13)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hr1]
  obtain ⟨vals1, body1, callee1, rs1, val1, bpost1, s_d1, inner1,
    he1, hlk1, _, hrun1, _, hloc_d1, hc_d1, hseq1, hpost_loc1, hres1, hpost_eq1⟩ :=
    arith_decCall_none_state hr
  have hv1 : vals1 = [.val (.word r1), .val (.word 13)] := Option.some.inj (he1.symm.trans hargs_d1)
  subst hv1
  have hdegB := fqDegree_callee_correct s bpost1 r1 (polynomialMemoryCoefficients s.memory r1)
    val1 body1 callee1 rs1 hc hb_r1.1 hwR1 hdR1 hmR1 hlk1 hrun1
  have hm_b1 : bpost1.memory = s.memory := by
    have hlk1_orig : Flapjack.PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "fq_poly_deg")
        [.val (.word r1), .val (.word 13)] = some (body1, callee1, rs1) := by
      rw [← hc]; exact hlk1
    have hp := fqDegree_function_memoryPure [.val (.word r1), .val (.word 13)] body1 callee1 rs1
      hlk1_orig (callEntryStateHOLFinite s callee1) hc
    rw [hrun1] at hp; exact hp
  have hG_b1 : GuestInv bpost1 := by
    have := guestInv_evaluate (callEntryStateHOLFinite s callee1) body1 (guestInv_callEntry s callee1 hG)
    rw [hrun1] at this; exact this
  have hG_d1 : GuestInv s_d1 := by
    rw [hres1]; exact guestInv_setVar _ _ _ (guestInv_with_locals_clock bpost1 s.locals bpost1.clock hG_b1)
  have hmem_d1 : s_d1.memory = s.memory := by
    rw [hres1]; simp only [setVarHOLFinite]; exact hm_b1
  have hd1w_ex : ∃ d1w : BitVec 64, val1 = .val (.word d1w) := by
    rcases hdegB with ⟨he, _⟩ | ⟨j, _, he, _, _⟩
    · exact ⟨0 - 1, he⟩
    · exact ⟨BitVec.ofNat 64 j, he⟩
  obtain ⟨d1w, rfl⟩ := hd1w_ex
  -- 2. ite (0 >=_s d1) break skip
  obtain ⟨s_ite, hite1, hdec0⟩ := arith_seq_none hseq1
  have hd1_lk : s_d1.locals.lookup (ofString "d1") = some (.val (.word d1w)) := by
    simp [hloc_d1, HolFiniteMapExact.lookup_update, FUPDATE]
  rw [evaluateHOLFiniteState_ite] at hite1
  have hcmp_ev : @evalHOLExact 64 F _ s_d1.toExact (fun a => Classical.propDecidable (s_d1.memaddrs a))
      (.cmp .notLess (.const 0) (.var .local (ofString "d1"))) =
      some (.val (.word (if wordCmpHOL .notLess 0 d1w then 1 else 0))) := by
    simp [evalHOLExact, hd1_lk]
  rw [hcmp_ev] at hite1
  dsimp only at hite1
  have hnge : wordCmpHOL .notLess 0 d1w = false := by
    by_cases hc0 : wordCmpHOL .notLess 0 d1w = true
    · rw [hc0] at hite1
      have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
      simp [h10, evaluateHOLFiniteState_break] at hite1
    · exact Bool.eq_false_iff.mpr hc0
  rw [hnge] at hite1
  simp only [Bool.false_eq_true, ↓reduceIte, evaluateHOLFiniteState_skip] at hite1
  have hs_ite_eq : s_d1 = s_ite := (Prod.mk.inj hite1).2
  subst hs_ite_eq
  obtain ⟨d1, hd1_pos, hd1_lt, rfl⟩ := d1_pos_of_guard_fallthrough d1w _ hdegB hnge
  -- 3. decCall d0 = fq_poly_deg(r0, 13)
  have hr0_d1 : s_d1.locals.lookup (ofString "r0") = some (.val (.word r0)) := by
    simp [hloc_d1, HolFiniteMapExact.lookup_update, FUPDATE, hr0, show ofString "d1" ≠ ofString "r0" by decide]
  have hargs_d0 : evalListHOLFinite s_d1 (h := fun a => Classical.propDecidable (s_d1.memaddrs a))
      [.var .local (ofString "r0"), .const 13] = some [.val (.word r0), .val (.word 13)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hr0_d1]
  obtain ⟨vals0, body0, callee0, rs0, val0, bpost0, s_d0, inner0,
    he0, hlk0, _, hrun0, _, hloc_d0, hc_d0, hseq0, hpost_loc0, hres0, hpost_eq0⟩ :=
    arith_decCall_none_state hdec0
  have hv0 : vals0 = [.val (.word r0), .val (.word 13)] := Option.some.inj (he0.symm.trans hargs_d0)
  subst hv0
  have hdR0_d1 : DomainPolynomial s_d1.memaddrs r0 := by rw [hG_d1.memaddrs, ← hG.memaddrs]; exact hdR0
  have hmR0_d1 : MemoryPolynomial s_d1.memory r0 (polynomialMemoryCoefficients s.memory r0) := by
    rw [hmem_d1]; exact hmR0
  have hdegA := fqDegree_callee_correct s_d1 bpost0 r0 (polynomialMemoryCoefficients s.memory r0)
    val0 body0 callee0 rs0 (hc_d1.trans hc) hb_r0.1 hwR0 hdR0_d1 hmR0_d1 hlk0 hrun0
  have hm_b0 : bpost0.memory = s_d1.memory := by
    have hlk0_orig : Flapjack.PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "fq_poly_deg")
        [.val (.word r0), .val (.word 13)] = some (body0, callee0, rs0) := by
      rw [← hc_d1.trans hc]; exact hlk0
    have hp := fqDegree_function_memoryPure [.val (.word r0), .val (.word 13)] body0 callee0 rs0
      hlk0_orig (callEntryStateHOLFinite s_d1 callee0) (hc_d1.trans hc)
    rw [hrun0] at hp; exact hp
  have hG_b0 : GuestInv bpost0 := by
    have := guestInv_evaluate (callEntryStateHOLFinite s_d1 callee0) body0 (guestInv_callEntry s_d1 callee0 hG_d1)
    rw [hrun0] at this; exact this
  have hG_d0 : GuestInv s_d0 := by
    rw [hres0]; exact guestInv_setVar _ _ _ (guestInv_with_locals_clock bpost0 s_d1.locals bpost0.clock hG_b0)
  have hmem_d0 : s_d0.memory = s.memory := by
    rw [hres0]; simp only [setVarHOLFinite]; exact hm_b0.trans hmem_d1
  have hd0w_ex : ∃ d0w : BitVec 64, val0 = .val (.word d0w) := by
    rcases hdegA with ⟨he, _⟩ | ⟨j, _, he, _, _⟩
    · exact ⟨0 - 1, he⟩
    · exact ⟨BitVec.ofNat 64 j, he⟩
  obtain ⟨d0w, rfl⟩ := hd0w_ex
  -- 4. call memzero(q, 416)
  obtain ⟨s_mz, hmz, hprep⟩ := arith_seq_none hseq0
  have hq_d0 : s_d0.locals.lookup (ofString "q") = some (.val (.word q)) := by
    simp [hloc_d0, hloc_d1, HolFiniteMapExact.lookup_update, FUPDATE, hq,
      show ofString "d0" ≠ ofString "q" by decide, show ofString "d1" ≠ ofString "q" by decide]
  obtain ⟨hef_mz, hloc_mz, _, hpoly_mz⟩ := call_memzero_none s_d0 s_mz
    (.var .local (ofString "q")) (.const 416) q 416 (hc_d0.trans (hc_d1.trans hc)) hG_d0
    (by simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hq_d0]) hmz
  have hG_mz : GuestInv s_mz := by
    have := guestInv_evaluate s_d0 (.call (some (none, none)) (ofString "memzero") [.var .local (ofString "q"), .const 416]) hG_d0
    rw [hmz] at this; exact this
  have hmQ_mz : MemoryPolynomial s_mz.memory q (fun _ => fqZeroLimbs) := hpoly_mz hb_q.1 rfl
  have hmR0_mz : MemoryPolynomial s_mz.memory r0 (polynomialMemoryCoefficients s.memory r0) :=
    extentFrame_preserves_polynomial hef_mz hb_q.1 hb_r0.1 hwR0
      (nonoverlap_of_polynomialDisjoint q r0 hb_q.1 hb_r0.1 hwQ hwR0
        (hdisj q r0 (by simp) (by simp) hdist.2.2.2.1.symm))
      (hmem_d0 ▸ hmR0)
  have hmR1_mz : MemoryPolynomial s_mz.memory r1 (polynomialMemoryCoefficients s.memory r1) :=
    extentFrame_preserves_polynomial hef_mz hb_q.1 hb_r1.1 hwR1
      (nonoverlap_of_polynomialDisjoint q r1 hb_q.1 hb_r1.1 hwQ hwR1
        (hdisj q r1 (by simp) (by simp) hdist.2.2.2.2.2.2.2.1.symm))
      (hmem_d0 ▸ hmR1)
  have hmS0_mz : MemoryPolynomial s_mz.memory s0 S0 :=
    extentFrame_preserves_polynomial hef_mz hb_q.1 hb_s0.1 hwS0
      (nonoverlap_of_polynomialDisjoint q s0 hb_q.1 hb_s0.1 hwQ hwS0
        (hdisj q s0 (by simp) (by simp) hdist.2.2.2.2.2.2.2.2.2.2.1.symm))
      (hmem_d0 ▸ hmS0)
  have hmS1_mz : MemoryPolynomial s_mz.memory s1 S1 :=
    extentFrame_preserves_polynomial hef_mz hb_q.1 hb_s1.1 hwS1
      (nonoverlap_of_polynomialDisjoint q s1 hb_q.1 hb_s1.1 hwQ hwS1
        (hdisj q s1 (by simp) (by simp) hdist.2.2.2.2.2.2.2.2.2.2.2.2.1.symm))
      (hmem_d0 ▸ hmS1)
  -- 5. polyDivPrepare (.seq polyDivLoop cofProg)
  have hctx_div : PolyDivGenEntryContext r0 r1 q d1 (polynomialMemoryCoefficients s.memory r1) :=
    ⟨hd1_pos, hd1_lt, hdegB,
     hdisj r0 r1 (by simp) (by simp) hdist.1,
     hdisj r0 q (by simp) (by simp) hdist.2.2.2.1,
     hdisj q r1 (by simp) (by simp) hdist.2.2.2.2.2.2.2.1.symm,
     hb_r0.1, hwR0⟩
  have hloc_mz_keep : ∀ nm, nm ≠ ofString "d0" → nm ≠ ofString "d1" →
      s_mz.locals.lookup nm = s.locals.lookup nm := by
    intro nm hn0 hn1
    rw [hloc_mz, hloc_d0, hloc_d1]
    simp [HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hn0, Ne.symm hn1]
  have hinv_div : PolyDivGenEntryInvariant r0 r1 q d1 (polynomialMemoryCoefficients s.memory r1) s_mz := by
    refine ⟨(hloc_mz_keep _ (by decide) (by decide)).trans hr0,
      (hloc_mz_keep _ (by decide) (by decide)).trans hr1,
      (hloc_mz_keep _ (by decide) (by decide)).trans hq,
      ?_, ?_, ?_, ?_, hmR1_mz,
      ⟨polynomialMemoryCoefficients s.memory r0, fun _ => fqZeroLimbs, d0w,
        hmR0_mz, hmQ_mz, hdegA, ?_⟩⟩
    · rw [hloc_mz, hloc_d0, hloc_d1]
      simp [HolFiniteMapExact.lookup_update, FUPDATE, show ofString "d0" ≠ ofString "d1" by decide]
    · rw [hG_mz.memaddrs, ← hG.memaddrs]; exact hdR0
    · rw [hG_mz.memaddrs, ← hG.memaddrs]; exact hdR1
    · rw [hG_mz.memaddrs, ← hG.memaddrs]; exact hdQ
    · rw [hloc_mz, hloc_d0]; simp [HolFiniteMapExact.lookup_update, FUPDATE]
  let cofProg : ProgHOL 64 :=
    .seq (.call (some (none, none)) (ofString "memcpy")
        [.var .local (ofString "tmp"), .var .local (ofString "s0"), .const 416])
      (polyCofactorRun polyCofactorFinish)
  obtain ⟨invVal, s_afterDiv, inner_cof, hG_afterDiv, hctx_gen, hinv_afterDiv, hexit_div,
    hc_afterDiv, hkeep_afterDiv, hframe_div, hcof, hmem_inner0, hloc_inner0⟩ :=
    polyDivPreparedLoop_gen_none s_mz inner0 r0 r1 q d1 (polynomialMemoryCoefficients s.memory r1)
      cofProg hctx_div hG_mz hinv_div hprep
  obtain ⟨degAfter, hd0_afterDiv, hdegAfter_lt⟩ := hexit_div
  obtain ⟨A_div, Q_div, degAfter', hmA_div, hmQ_div, hdegA_div, hd0_afterDiv'⟩ := hinv_afterDiv.dividend
  have hdeg_eq : degAfter = degAfter' := by
    have := Option.some.inj (hd0_afterDiv.symm.trans hd0_afterDiv')
    simpa only [ValueHOL.val.injEq, HolWordLab.word.injEq] using this
  subst hdeg_eq
  have hmB_div : MemoryPolynomial s_afterDiv.memory r1 (polynomialMemoryCoefficients s.memory r1) :=
    hinv_afterDiv.divisor
  have hmS0_div : MemoryPolynomial s_afterDiv.memory s0 S0 :=
    twoBufferFrame_preserves s_mz.memory s_afterDiv.memory r0 q s0 S0 hframe_div
      (hdisj r0 s0 (by simp) (by simp) hdist.2.1)
      (hdisj q s0 (by simp) (by simp) hdist.2.2.2.2.2.2.2.2.2.2.1.symm) hmS0_mz
  have hmS1_div : MemoryPolynomial s_afterDiv.memory s1 S1 :=
    twoBufferFrame_preserves s_mz.memory s_afterDiv.memory r0 q s1 S1 hframe_div
      (hdisj r0 s1 (by simp) (by simp) hdist.2.2.1)
      (hdisj q s1 (by simp) (by simp) hdist.2.2.2.2.2.2.2.2.2.2.2.2.1.symm) hmS1_mz
  -- 6. memcpy(tmp, s0, 416) followed by polyCofactorRun polyCofactorFinish
  obtain ⟨s_mcpy, hmcpy, hcof_swap⟩ := arith_seq_none hcof
  have htmp_afterDiv : s_afterDiv.locals.lookup (ofString "tmp") = some (.val (.word tmp)) :=
    (hkeep_afterDiv _ (by simp)).trans ((hloc_mz_keep _ (by decide) (by decide)).trans htmp)
  have hs0_afterDiv : s_afterDiv.locals.lookup (ofString "s0") = some (.val (.word s0)) :=
    (hkeep_afterDiv _ (by simp)).trans ((hloc_mz_keep _ (by decide) (by decide)).trans hs0)
  obtain ⟨hef_mcpy, hloc_mcpy, _, hpoly_mcpy⟩ := call_memcpy_none s_afterDiv s_mcpy
    (.var .local (ofString "tmp")) (.var .local (ofString "s0")) (.const 416) tmp s0 416
    hG_afterDiv.code hG_afterDiv
    (by simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, htmp_afterDiv, hs0_afterDiv])
    hmcpy
  have hG_mcpy : GuestInv s_mcpy := by
    have := guestInv_evaluate s_afterDiv
      (.call (some (none, none)) (ofString "memcpy")
        [.var .local (ofString "tmp"), .var .local (ofString "s0"), .const 416]) hG_afterDiv
    rw [hmcpy] at this; exact this
  have hdTmp_div : DomainPolynomial s_afterDiv.memaddrs tmp := by
    rw [hG_afterDiv.memaddrs, ← hG.memaddrs]; exact hdTmp
  have hdS0_div : DomainPolynomial s_afterDiv.memaddrs s0 := by
    rw [hG_afterDiv.memaddrs, ← hG.memaddrs]; exact hdS0
  have hmTmp_mcpy : MemoryPolynomial s_mcpy.memory tmp S0 :=
    hpoly_mcpy S0 hb_tmp.1 hb_s0.1 rfl hdTmp_div hdS0_div hmS0_div
      (hdisj tmp s0 (by simp) (by simp) hdist.2.2.2.2.2.2.2.2.2.2.2.1.symm)
  have hmA_mcpy : MemoryPolynomial s_mcpy.memory r0 A_div :=
    extentFrame_preserves_polynomial hef_mcpy hb_tmp.1 hb_r0.1 hwR0
      (nonoverlap_of_polynomialDisjoint tmp r0 hb_tmp.1 hb_r0.1 hwTmp hwR0
        (hdisj tmp r0 (by simp) (by simp) hdist.2.2.2.2.1.symm)) hmA_div
  have hmB_mcpy : MemoryPolynomial s_mcpy.memory r1 (polynomialMemoryCoefficients s.memory r1) :=
    extentFrame_preserves_polynomial hef_mcpy hb_tmp.1 hb_r1.1 hwR1
      (nonoverlap_of_polynomialDisjoint tmp r1 hb_tmp.1 hb_r1.1 hwTmp hwR1
        (hdisj tmp r1 (by simp) (by simp) hdist.2.2.2.2.2.2.2.2.1.symm)) hmB_div
  have hmS1_mcpy : MemoryPolynomial s_mcpy.memory s1 S1 :=
    extentFrame_preserves_polynomial hef_mcpy hb_tmp.1 hb_s1.1 hwS1
      (nonoverlap_of_polynomialDisjoint tmp s1 hb_tmp.1 hb_s1.1 hwTmp hwS1
        (hdisj tmp s1 (by simp) (by simp) hdist.2.2.2.2.2.2.2.2.2.2.2.2.2.1.symm)) hmS1_div
  have hmQ_mcpy : MemoryPolynomial s_mcpy.memory q Q_div :=
    extentFrame_preserves_polynomial hef_mcpy hb_tmp.1 hb_q.1 hwQ
      (nonoverlap_of_polynomialDisjoint tmp q hb_tmp.1 hb_q.1 hwTmp hwQ
        (hdisj tmp q (by simp) (by simp) hdist.2.2.2.2.2.2.2.2.2.2.2.2.2.2.symm)) hmQ_div
  have hr0_mcpy : s_mcpy.locals.lookup (ofString "r0") = some (.val (.word r0)) := by
    rw [hloc_mcpy]; exact (hkeep_afterDiv _ (by simp)).trans ((hloc_mz_keep _ (by decide) (by decide)).trans hr0)
  have hr1_mcpy : s_mcpy.locals.lookup (ofString "r1") = some (.val (.word r1)) := by
    rw [hloc_mcpy]; exact (hkeep_afterDiv _ (by simp)).trans ((hloc_mz_keep _ (by decide) (by decide)).trans hr1)
  have hs0_mcpy : s_mcpy.locals.lookup (ofString "s0") = some (.val (.word s0)) := by
    rw [hloc_mcpy]; exact hs0_afterDiv
  have hs1_mcpy : s_mcpy.locals.lookup (ofString "s1") = some (.val (.word s1)) := by
    rw [hloc_mcpy]; exact (hkeep_afterDiv _ (by simp)).trans ((hloc_mz_keep _ (by decide) (by decide)).trans hs1)
  have htmp_mcpy : s_mcpy.locals.lookup (ofString "tmp") = some (.val (.word tmp)) := by
    rw [hloc_mcpy]; exact htmp_afterDiv
  have hq_mcpy : s_mcpy.locals.lookup (ofString "q") = some (.val (.word q)) := by
    rw [hloc_mcpy]; exact (hkeep_afterDiv _ (by simp)).trans ((hloc_mz_keep _ (by decide) (by decide)).trans hq)
  have hdTmp_mcpy : DomainPolynomial s_mcpy.memaddrs tmp := by
    rw [hG_mcpy.memaddrs, ← hG.memaddrs]; exact hdTmp
  have hdS1_mcpy : DomainPolynomial s_mcpy.memaddrs s1 := by
    rw [hG_mcpy.memaddrs, ← hG.memaddrs]; exact hdS1
  have hdQ_mcpy : DomainPolynomial s_mcpy.memaddrs q := by
    rw [hG_mcpy.memaddrs, ← hG.memaddrs]; exact hdQ
  obtain ⟨S1_new, hS1_new, hmA_cof, hmB_cof, hmS1_cof, hmTmp_cof, hmQ_cof,
    hr0_cof, hr1_cof, hs0_cof, hs1_cof, htmp_cof, hrank_lt_cof, _⟩ :=
    polyCofactorSwap_progress s_mcpy inner_cof r0 r1 s0 s1 tmp q
      A_div (polynomialMemoryCoefficients s.memory r1) S1 S0 Q_div degAfter d1
      hG_mcpy.code hr0_mcpy hr1_mcpy hs0_mcpy hs1_mcpy htmp_mcpy hq_mcpy
      hS0 hS1 hdTmp_mcpy hdS1_mcpy hdQ_mcpy
      hmA_mcpy hmB_mcpy hmS1_mcpy hmTmp_mcpy hmQ_mcpy
      (hdisj tmp r0 (by simp) (by simp) hdist.2.2.2.2.1.symm)
      (hdisj tmp r1 (by simp) (by simp) hdist.2.2.2.2.2.2.2.2.1.symm)
      (hdisj tmp s1 (by simp) (by simp) hdist.2.2.2.2.2.2.2.2.2.2.2.2.2.1.symm)
      (hdisj tmp q (by simp) (by simp) hdist.2.2.2.2.2.2.2.2.2.2.2.2.2.2.symm)
      hdegA_div hdegB hd1_lt hdegAfter_lt hcof_swap
  have hq_cof : inner_cof.locals.lookup (ofString "q") = some (.val (.word q)) := by
    have havoid : avoidsLocal (ofString "q") (polyCofactorRun polyCofactorFinish) = true := by decide
    have hfl := evaluate_avoidsLocal_flowing (ofString "q") (polyCofactorRun polyCofactorFinish) havoid s_mcpy
    rw [hcof_swap] at hfl
    exact (hfl (Or.inl rfl)).trans hq_mcpy
  have hmem_post : post.memory = inner_cof.memory := by
    rw [hpost_eq1, hpost_eq0]; exact hmem_inner0
  have hloc_post : ∀ nm, nm ≠ ofString "d1" → nm ≠ ofString "d0" → nm ≠ ofString "lead" → nm ≠ ofString "linv" →
      post.locals.lookup nm = inner_cof.locals.lookup nm := by
    intro nm hn1 hn0 hnl hni
    rw [hpost_loc1, PanRunBounded.resVarEq_lookup, if_neg hn1,
        hpost_loc0, PanRunBounded.resVarEq_lookup, if_neg hn0,
        hloc_inner0 _ hnl hni]
  have hrank_post : polyOuterRank post = polyOuterRank inner_cof := by
    have hr1_p : post.locals.lookup (ofString "r1") = inner_cof.locals.lookup (ofString "r1") :=
      hloc_post _ (by decide) (by decide) (by decide) (by decide)
    simp only [polyOuterRank, hr1_p, hmem_post]
  have hrank_mcpy : polyOuterRank s_mcpy = polyOuterRank s := by
    rw [polyOuterRank_represented s_mcpy r1 (polynomialMemoryCoefficients s.memory r1)
        (BitVec.ofNat 64 d1) hr1_mcpy hmB_mcpy hdegB,
      polyOuterRank_represented s r1 (polynomialMemoryCoefficients s.memory r1)
        (BitVec.ofNat 64 d1) hr1 hmR1 hdegB]
  refine ⟨⟨hG_post, ⟨r1, r0, s1, tmp, q, s0, S1, S1_new,
    (hloc_post _ (by decide) (by decide) (by decide) (by decide)).trans hr0_cof,
    (hloc_post _ (by decide) (by decide) (by decide) (by decide)).trans hr1_cof,
    (hloc_post _ (by decide) (by decide) (by decide) (by decide)).trans hs0_cof,
    (hloc_post _ (by decide) (by decide) (by decide) (by decide)).trans hs1_cof,
    (hloc_post _ (by decide) (by decide) (by decide) (by decide)).trans hq_cof,
    (hloc_post _ (by decide) (by decide) (by decide) (by decide)).trans htmp_cof,
    hb_r1, hb_r0, hb_s1, hb_tmp, hb_q, hb_s0,
    fun x y hx hy hxy => hdisj x y (perm_mem_six.mp hx) (perm_mem_six.mp hy) hxy,
    perm_sixDistinct hdist,
    hS1, hS1_new,
    hmem_post ▸ hmS1_cof,
    hmem_post ▸ hmTmp_cof⟩⟩, ?_⟩
  rw [hrank_post, ← hrank_mcpy]
  exact hrank_lt_cof

/-! ### 7. Boundedness of `fq12OuterBody`, `fq12OuterLoop`, `fq12PostLoop`, and `fb_fq12_inv` -/

private def polyCofactorCost : Nat :=
  (K.«memcpy» + 1) + 14 * (polyCofactorBodyCost + 1)

private theorem cofProg_bounded :
    TerminatingProgBoundedOn GuestInv
      (.seq (.call (some (none, none)) (ofString "memcpy")
          [.var .local (ofString "tmp"), .var .local (ofString "s0"), .const 416])
        (polyCofactorRun polyCofactorFinish))
      polyCofactorCost := by
  have hcof_fin : TerminatingProgBoundedOn GuestInv polyCofactorFinish 0 :=
    straight_on polyCofactorFinish rfl
  have hcof_run : TerminatingProgBoundedOn GuestInv (polyCofactorRun polyCofactorFinish)
      (14 * (polyCofactorBodyCost + 1)) := by
    unfold polyCofactorRun
    exact TerminatingProgBoundedOn.dec_on localsFree_guestInv _ _ _
      (bound_add_zero (TerminatingProgBoundedOn.seq_guestInv polyCofactorLoop_bounded hcof_fin))
  exact @TerminatingProgBoundedOn.seq_guestInv
    (.call (some (none, none)) (ofString "memcpy")
      [.var .local (ofString "tmp"), .var .local (ofString "s0"), .const 416])
    (polyCofactorRun polyCofactorFinish) (K.«memcpy» + 1) (14 * (polyCofactorBodyCost + 1))
    (TerminatingProgBoundedOn.call_guestInv fb_memcpy _ _) hcof_run

private theorem polyDivPrepare_bounded :
    TerminatingProgBoundedOn
      (fun s => GuestInv s ∧
        ∃ a b quotient : BitVec 64, ∃ d1 : Nat, ∃ B : Nat → Limbs256,
          PolyDivGenEntryContext a b quotient d1 B ∧
          PolyDivGenEntryInvariant a b quotient d1 B s)
      (polyDivPrepare
        (.seq polyDivLoop
          (.seq (.call (some (none, none)) (ofString "memcpy")
              [.var .local (ofString "tmp"), .var .local (ofString "s0"), .const 416])
            (polyCofactorRun polyCofactorFinish))))
      ((K.«fq_inv» + 1) + (14 + 1) * (polyDivisionBodyCost + 1) + polyCofactorCost) := by
  let Q1 : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
    fun s => GuestInv s ∧
      ∃ a b quotient : BitVec 64, ∃ d1 : Nat, ∃ B : Nat → Limbs256,
        PolyDivGenEntryContext a b quotient d1 B ∧
        PolyDivGenEntryInvariant a b quotient d1 B s ∧
        s.locals.lookup (ofString "lead") = some (B d1).toValue
  let Q2 : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
    fun s => GuestInv s ∧
      ∃ a b quotient : BitVec 64, ∃ d1 : Nat, ∃ B : Nat → Limbs256, ∃ inverse : Limbs256,
        PolyDivGenContext a b quotient d1 B inverse ∧
        PolyDivGenInvariant a b quotient d1 B inverse s
  have hloop_q2 : TerminatingProgBoundedOn Q2 polyDivLoop ((14 + 1) * (polyDivisionBodyCost + 1)) := by
    intro F s hc hp
    obtain ⟨hG, a, b, quotient, d1, B, inverse, hctx, hinv⟩ := hp
    exact polyDivLoop_stationary_bounded a b quotient d1 B inverse hctx s hc ⟨hG, hinv⟩
  have htail : TerminatingProgBoundedOn Q2
      (.seq polyDivLoop
        (.seq (.call (some (none, none)) (ofString "memcpy")
            [.var .local (ofString "tmp"), .var .local (ofString "s0"), .const 416])
          (polyCofactorRun polyCofactorFinish)))
      ((14 + 1) * (polyDivisionBodyCost + 1) + polyCofactorCost) := by
    refine @TerminatingProgBoundedOn.seq_on_none Q2 GuestInv polyDivLoop _
      ((14 + 1) * (polyDivisionBodyCost + 1)) polyCofactorCost hloop_q2 ?_ cofProg_bounded
    intro F s mid _ hp hr
    have := guestInv_evaluate s polyDivLoop hp.1
    rw [hr] at this
    exact this
  have hinv_call : TerminatingProgBoundedOn Q1
      (.decCall (ofString "linv") (.comb [.one, .one, .one, .one]) (ofString "fq_inv")
        [polyDivVar "lead"]
        (.seq polyDivLoop
          (.seq (.call (some (none, none)) (ofString "memcpy")
              [.var .local (ofString "tmp"), .var .local (ofString "s0"), .const 416])
            (polyCofactorRun polyCofactorFinish))))
      ((K.«fq_inv» + 1) + ((14 + 1) * (polyDivisionBodyCost + 1) + polyCofactorCost)) := by
    refine bound_mono (B1 := K.«fq_inv» + (((14 + 1) * (polyDivisionBodyCost + 1) + polyCofactorCost)) + 1) (by omega)
      (@TerminatingProgBoundedOn.decCall_on_returned Q1 Q2 (ofString "fq_inv") K.«fq_inv»
        (((14 + 1) * (polyDivisionBodyCost + 1) + polyCofactorCost)) fb_fq_inv (fun _ hp => hp.1)
        (ofString "linv") (.comb [.one, .one, .one, .one]) [polyDivVar "lead"] _ htail ?_)
    intro F state bpost values body callee ret' value hc hp hargs hlk hrun
    obtain ⟨hG, a, b, quotient, d1, B, ctx, hi, hlead⟩ := hp
    have hargs_inv : evalListHOLFinite state
        (h := fun x => Classical.propDecidable (state.memaddrs x)) [polyDivVar "lead"] =
        some [(B d1).toValue] := by
      simp [polyDivVar, evalListHOLFinite, evalListHOLExact, evalHOLExact, hlead]
    have hv : values = [(B d1).toValue] := Option.some.inj (hargs.symm.trans hargs_inv)
    subst hv
    obtain ⟨inverse, hret, hcanon, hinv⟩ := fqInverse_callee_returned (B d1) value hc
      (polynomialDegreeValue_at_index B d1 ctx.bound ctx.degree) hlk hrun
    have hlk_orig : Flapjack.PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "fq_inv")
        [(B d1).toValue] = some (body, callee, ret') := by
      rw [← hc]; exact hlk
    have hpbody : MemoryPure body :=
      fqInverse_function_memoryPure [(B d1).toValue] body callee ret' hlk_orig
    have hmem0 := hpbody (callEntryStateHOLFinite state callee) hc
    have hdomain0 := (evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state callee) body).2.1
    rw [hrun] at hmem0 hdomain0
    have hG_bpost : GuestInv bpost := by
      have := guestInv_evaluate (callEntryStateHOLFinite state callee) body
        (guestInv_callEntry state callee hG)
      rw [hrun] at this; exact this
    let resumed := setVarHOLFinite (ofString "linv") value { bpost with locals := state.locals }
    have hG_res : GuestInv resumed :=
      guestInv_setVar _ _ _ (guestInv_with_locals_clock bpost state.locals bpost.clock hG_bpost)
    have hkeep : ∀ nm, nm ≠ ofString "linv" → resumed.locals.lookup nm = state.locals.lookup nm := by
      intro nm hn
      simp [resumed, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hn]
    have hInvLoc : resumed.locals.lookup (ofString "linv") = some inverse.toValue := by
      simp [resumed, hret, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hmem : resumed.memory = state.memory := hmem0
    have hdom : resumed.memaddrs = state.memaddrs := hdomain0
    refine ⟨hG_res, a, b, quotient, d1, B, inverse,
      ⟨ctx.positive, ctx.bound, ctx.degree, hcanon, hinv,
        ctx.separateAB, ctx.separateAQ, ctx.separateQB, ctx.aligned, ctx.nonwrapping⟩,
      ⟨(hkeep _ (by decide)).trans hi.r0,
       (hkeep _ (by decide)).trans hi.r1,
       (hkeep _ (by decide)).trans hi.q,
       (hkeep _ (by decide)).trans hi.degree1,
       hInvLoc, hdom ▸ hi.domainA, hdom ▸ hi.domainB, hdom ▸ hi.domainQ,
       hmem ▸ hi.divisor, ?_⟩⟩
    obtain ⟨A, Q, degree, hmA, hmQ, hdA, hlocal⟩ := hi.dividend
    exact ⟨A, Q, degree, hmem ▸ hmA, hmem ▸ hmQ, hdA, (hkeep _ (by decide)).trans hlocal⟩
  unfold polyDivPrepare
  refine @bound_mono
    (fun s => GuestInv s ∧
      ∃ a b quotient : BitVec 64, ∃ d1 : Nat, ∃ B : Nat → Limbs256,
        PolyDivGenEntryContext a b quotient d1 B ∧
        PolyDivGenEntryInvariant a b quotient d1 B s)
    _ ((K.«fq_inv» + 1) + ((14 + 1) * (polyDivisionBodyCost + 1) + polyCofactorCost))
    ((K.«fq_inv» + 1) + (14 + 1) * (polyDivisionBodyCost + 1) + polyCofactorCost) (by omega)
    (@TerminatingProgBoundedOn.dec_on_init
      (fun s => GuestInv s ∧
        ∃ a b quotient : BitVec 64, ∃ d1 : Nat, ∃ B : Nat → Limbs256,
          PolyDivGenEntryContext a b quotient d1 B ∧
          PolyDivGenEntryInvariant a b quotient d1 B s)
      Q1 (ofString "lead") arithU256Shape
      (.load arithU256Shape polyDivLeadAddress) _ _ hinv_call ?_)
  intro F state v _ hp heval _
  obtain ⟨hG, a, b, quotient, d1, B, ctx, hi⟩ := hp
  have haddr : arithEval state polyDivLeadAddress = some (.val (.word (coefficientAddress b d1))) := by
    rw [← coefficientAddress_source]
    simp [arithEval, polyDivLeadAddress, polyDivVar, evalHOLExact, evalListHOLExact, hi.r1, hi.degree1,
      wordOpHOL, wordOp, panOpHOL, valueIsWord, valueWord]
  have hload := eval_load_u256 state polyDivLeadAddress (coefficientAddress b d1) (B d1)
    haddr (hi.domainB d1 ctx.bound) (hi.divisor d1 ctx.bound)
  have hv : v = (B d1).toValue := Option.some.inj (heval.symm.trans hload)
  subst hv
  let declared := setVarHOLFinite (ofString "lead") (B d1).toValue state
  have hkeep : ∀ nm, nm ≠ ofString "lead" → declared.locals.lookup nm = state.locals.lookup nm := by
    intro nm hn
    simp [declared, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hn]
  refine ⟨guestInv_setVar _ _ _ hG, a, b, quotient, d1, B, ctx,
    ⟨(hkeep _ (by decide)).trans hi.r0,
     (hkeep _ (by decide)).trans hi.r1,
     (hkeep _ (by decide)).trans hi.q,
     (hkeep _ (by decide)).trans hi.degree1,
     hi.domainA, hi.domainB, hi.domainQ, hi.divisor, ?_⟩,
    by simp [declared, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]⟩
  obtain ⟨A, Q, degree, hmA, hmQ, hdA, hlocal⟩ := hi.dividend
  exact ⟨A, Q, degree, hmA, hmQ, hdA, (hkeep _ (by decide)).trans hlocal⟩

private theorem fq12OuterBody_bounded :
    TerminatingProgBoundedOn Fq12OuterInv fq12OuterBody polyOuterBodyCost := by
  let P_d1 : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
    fun s => GuestInv s ∧
      ∃ (r0 r1 q : BitVec 64) (d1w : BitVec 64),
        BufOk r0 ∧ BufOk r1 ∧ BufOk q ∧
        PolynomialDisjoint r0 r1 ∧ PolynomialDisjoint r0 q ∧ PolynomialDisjoint q r1 ∧
        s.locals.lookup (ofString "r0") = some (.val (.word r0)) ∧
        s.locals.lookup (ofString "r1") = some (.val (.word r1)) ∧
        s.locals.lookup (ofString "q") = some (.val (.word q)) ∧
        s.locals.lookup (ofString "d1") = some (.val (.word d1w)) ∧
        PolynomialDegreeValue (polynomialMemoryCoefficients s.memory r1) (.val (.word d1w))
  let P_pos : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
    fun s => GuestInv s ∧
      ∃ (r0 r1 q : BitVec 64) (d1 : Nat),
        0 < d1 ∧ d1 < 13 ∧
        BufOk r0 ∧ BufOk r1 ∧ BufOk q ∧
        PolynomialDisjoint r0 r1 ∧ PolynomialDisjoint r0 q ∧ PolynomialDisjoint q r1 ∧
        s.locals.lookup (ofString "r0") = some (.val (.word r0)) ∧
        s.locals.lookup (ofString "r1") = some (.val (.word r1)) ∧
        s.locals.lookup (ofString "q") = some (.val (.word q)) ∧
        s.locals.lookup (ofString "d1") = some (.val (.word (BitVec.ofNat 64 d1))) ∧
        PolynomialDegreeValue (polynomialMemoryCoefficients s.memory r1)
          (.val (.word (BitVec.ofNat 64 d1)))
  let P_d0 : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
    fun s => GuestInv s ∧
      ∃ (r0 r1 q : BitVec 64) (d1 : Nat) (d0w : BitVec 64),
        0 < d1 ∧ d1 < 13 ∧
        BufOk r0 ∧ BufOk r1 ∧ BufOk q ∧
        PolynomialDisjoint r0 r1 ∧ PolynomialDisjoint r0 q ∧ PolynomialDisjoint q r1 ∧
        s.locals.lookup (ofString "r0") = some (.val (.word r0)) ∧
        s.locals.lookup (ofString "r1") = some (.val (.word r1)) ∧
        s.locals.lookup (ofString "q") = some (.val (.word q)) ∧
        s.locals.lookup (ofString "d1") = some (.val (.word (BitVec.ofNat 64 d1))) ∧
        s.locals.lookup (ofString "d0") = some (.val (.word d0w)) ∧
        PolynomialDegreeValue (polynomialMemoryCoefficients s.memory r1)
          (.val (.word (BitVec.ofNat 64 d1))) ∧
        PolynomialDegreeValue (polynomialMemoryCoefficients s.memory r0) (.val (.word d0w))
  have hmzero_prep : TerminatingProgBoundedOn P_d0
      (.seq (.call (some (none, none)) (ofString "memzero") [.var .local (ofString "q"), .const 416])
        (polyDivPrepare
          (.seq polyDivLoop
            (.seq (.call (some (none, none)) (ofString "memcpy")
                [.var .local (ofString "tmp"), .var .local (ofString "s0"), .const 416])
              (polyCofactorRun polyCofactorFinish)))))
      ((K.«memzero» + 1) +
        ((K.«fq_inv» + 1) + (14 + 1) * (polyDivisionBodyCost + 1) + polyCofactorCost)) := by
    refine @TerminatingProgBoundedOn.seq_on_none P_d0 _ _ _ (K.«memzero» + 1) _
      (@bound_imp P_d0 GuestInv _ _ (fun _ hp => hp.1) (TerminatingProgBoundedOn.call_guestInv fb_memzero _ _))
      ?_ polyDivPrepare_bounded
    intro F s s_mz hc hp hmz
    obtain ⟨hG, r0, r1, q, d1, d0w, hd1_pos, hd1_lt, hb_r0, hb_r1, hb_q,
      h01, h0q, hq1, hr0, hr1, hq, hd1_lk, hd0_lk, hdegB, hdegA⟩ := hp
    obtain ⟨hdR0, hwR0, hmR0⟩ := domainPolynomial_of_interval s r0 hG hb_r0.1 hb_r0.2.1 hb_r0.2.2
    obtain ⟨hdR1, hwR1, hmR1⟩ := domainPolynomial_of_interval s r1 hG hb_r1.1 hb_r1.2.1 hb_r1.2.2
    obtain ⟨hdQ, hwQ, _⟩ := domainPolynomial_of_interval s q hG hb_q.1 hb_q.2.1 hb_q.2.2
    obtain ⟨hef_mz, hloc_mz, _, hpoly_mz⟩ := call_memzero_none s s_mz
      (.var .local (ofString "q")) (.const 416) q 416 hc hG
      (by simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hq]) hmz
    have hG_mz : GuestInv s_mz := by
      have := guestInv_evaluate s
        (.call (some (none, none)) (ofString "memzero") [.var .local (ofString "q"), .const 416]) hG
      rw [hmz] at this; exact this
    have hmQ_mz : MemoryPolynomial s_mz.memory q (fun _ => fqZeroLimbs) := hpoly_mz hb_q.1 rfl
    have hmR0_mz : MemoryPolynomial s_mz.memory r0 (polynomialMemoryCoefficients s.memory r0) :=
      extentFrame_preserves_polynomial hef_mz hb_q.1 hb_r0.1 hwR0
        (nonoverlap_of_polynomialDisjoint q r0 hb_q.1 hb_r0.1 hwQ hwR0
          (polynomialDisjoint_symm r0 q h0q)) hmR0
    have hmR1_mz : MemoryPolynomial s_mz.memory r1 (polynomialMemoryCoefficients s.memory r1) :=
      extentFrame_preserves_polynomial hef_mz hb_q.1 hb_r1.1 hwR1
        (nonoverlap_of_polynomialDisjoint q r1 hb_q.1 hb_r1.1 hwQ hwR1 hq1) hmR1
    refine ⟨hG_mz, r0, r1, q, d1, polynomialMemoryCoefficients s.memory r1,
      ⟨hd1_pos, hd1_lt, hdegB, h01, h0q, hq1, hb_r0.1, hwR0⟩,
      ⟨by rw [hloc_mz]; exact hr0,
       by rw [hloc_mz]; exact hr1,
       by rw [hloc_mz]; exact hq,
       by rw [hloc_mz]; exact hd1_lk,
       by rw [hG_mz.memaddrs, ← hG.memaddrs]; exact hdR0,
       by rw [hG_mz.memaddrs, ← hG.memaddrs]; exact hdR1,
       by rw [hG_mz.memaddrs, ← hG.memaddrs]; exact hdQ,
       hmR1_mz,
       ⟨polynomialMemoryCoefficients s.memory r0, fun _ => fqZeroLimbs, d0w,
         hmR0_mz, hmQ_mz, hdegA, by rw [hloc_mz]; exact hd0_lk⟩⟩⟩
  have hd0_call : TerminatingProgBoundedOn P_pos
      (.decCall (ofString "d0") .one (ofString "fq_poly_deg") [.var .local (ofString "r0"), .const 13]
        (.seq (.call (some (none, none)) (ofString "memzero") [.var .local (ofString "q"), .const 416])
          (polyDivPrepare
            (.seq polyDivLoop
              (.seq (.call (some (none, none)) (ofString "memcpy")
                  [.var .local (ofString "tmp"), .var .local (ofString "s0"), .const 416])
                (polyCofactorRun polyCofactorFinish))))))
      ((K.«fq_poly_deg» + 1) +
        ((K.«memzero» + 1) +
          ((K.«fq_inv» + 1) + (14 + 1) * (polyDivisionBodyCost + 1) + polyCofactorCost))) := by
    refine bound_mono
      (B1 := K.«fq_poly_deg» +
        ((K.«memzero» + 1) +
          ((K.«fq_inv» + 1) + (14 + 1) * (polyDivisionBodyCost + 1) + polyCofactorCost)) + 1) (by omega)
      (@TerminatingProgBoundedOn.decCall_on_returned P_pos P_d0 (ofString "fq_poly_deg") K.«fq_poly_deg»
        ((K.«memzero» + 1) + ((K.«fq_inv» + 1) + (14 + 1) * (polyDivisionBodyCost + 1) + polyCofactorCost))
        fb_fq_poly_deg (fun _ hp => hp.1)
        (ofString "d0") .one [.var .local (ofString "r0"), .const 13] _ hmzero_prep ?_)
    intro F s bpost values body callee ret' value hc hp hargs hlk hrun
    obtain ⟨hG, r0, r1, q, d1, hd1_pos, hd1_lt, hb_r0, hb_r1, hb_q,
      h01, h0q, hq1, hr0, hr1, hq, hd1_lk, hdegB⟩ := hp
    have hargs_d0 : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
        [.var .local (ofString "r0"), .const 13] = some [.val (.word r0), .val (.word 13)] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hr0]
    have hv : values = [.val (.word r0), .val (.word 13)] := Option.some.inj (hargs.symm.trans hargs_d0)
    subst hv
    obtain ⟨hdR0, hwR0, hmR0⟩ := domainPolynomial_of_interval s r0 hG hb_r0.1 hb_r0.2.1 hb_r0.2.2
    have hdegA := fqDegree_callee_correct s bpost r0 (polynomialMemoryCoefficients s.memory r0)
      value body callee ret' hc hb_r0.1 hwR0 hdR0 hmR0 hlk hrun
    have hm_b0 : bpost.memory = s.memory := by
      have hlk_orig : Flapjack.PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "fq_poly_deg")
          [.val (.word r0), .val (.word 13)] = some (body, callee, ret') := by
        rw [← hc]; exact hlk
      have hpure := fqDegree_function_memoryPure [.val (.word r0), .val (.word 13)] body callee ret'
        hlk_orig (callEntryStateHOLFinite s callee) hc
      rw [hrun] at hpure; exact hpure
    have hG_b0 : GuestInv bpost := by
      have := guestInv_evaluate (callEntryStateHOLFinite s callee) body (guestInv_callEntry s callee hG)
      rw [hrun] at this; exact this
    have hd0w_ex : ∃ d0w : BitVec 64, value = .val (.word d0w) := by
      rcases hdegA with ⟨he, _⟩ | ⟨j, _, he, _, _⟩
      · exact ⟨0 - 1, he⟩
      · exact ⟨BitVec.ofNat 64 j, he⟩
    obtain ⟨d0w, rfl⟩ := hd0w_ex
    let resumed := setVarHOLFinite (ofString "d0") (.val (.word d0w)) { bpost with locals := s.locals }
    have hG_res : GuestInv resumed :=
      guestInv_setVar _ _ _ (guestInv_with_locals_clock bpost s.locals bpost.clock hG_b0)
    have hkeep : ∀ nm, nm ≠ ofString "d0" → resumed.locals.lookup nm = s.locals.lookup nm := by
      intro nm hn
      simp [resumed, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hn]
    have hmem_res : resumed.memory = s.memory := hm_b0
    exact ⟨hG_res, r0, r1, q, d1, d0w, hd1_pos, hd1_lt, hb_r0, hb_r1, hb_q, h01, h0q, hq1,
      (hkeep _ (by decide)).trans hr0,
      (hkeep _ (by decide)).trans hr1,
      (hkeep _ (by decide)).trans hq,
      (hkeep _ (by decide)).trans hd1_lk,
      by simp [resumed, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE],
      hmem_res ▸ hdegB, hmem_res ▸ hdegA⟩
  have hite_seq : TerminatingProgBoundedOn P_d1
      (.seq (.ite (.cmp .notLess (.const 0) (.var .local (ofString "d1"))) .break .skip)
        (.decCall (ofString "d0") .one (ofString "fq_poly_deg") [.var .local (ofString "r0"), .const 13]
          (.seq (.call (some (none, none)) (ofString "memzero") [.var .local (ofString "q"), .const 416])
            (polyDivPrepare
              (.seq polyDivLoop
                (.seq (.call (some (none, none)) (ofString "memcpy")
                    [.var .local (ofString "tmp"), .var .local (ofString "s0"), .const 416])
                  (polyCofactorRun polyCofactorFinish)))))))
      ((K.«fq_poly_deg» + 1) +
        ((K.«memzero» + 1) +
          ((K.«fq_inv» + 1) + (14 + 1) * (polyDivisionBodyCost + 1) + polyCofactorCost))) := by
    refine @seq_straight_on P_d1 P_pos _ _ _ rfl ?_ hd0_call
    intro F s mid _ hp hite
    obtain ⟨hG, r0, r1, q, d1w, hb_r0, hb_r1, hb_q, h01, h0q, hq1, hr0, hr1, hq, hd1_lk, hdegB⟩ := hp
    rw [evaluateHOLFiniteState_ite] at hite
    have hcmp_ev : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
        (.cmp .notLess (.const 0) (.var .local (ofString "d1"))) =
        some (.val (.word (if wordCmpHOL .notLess 0 d1w then 1 else 0))) := by
      simp [evalHOLExact, hd1_lk]
    rw [hcmp_ev] at hite
    dsimp only at hite
    have hnge : wordCmpHOL .notLess 0 d1w = false := by
      by_cases hc0 : wordCmpHOL .notLess 0 d1w = true
      · rw [hc0] at hite
        have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
        simp [h10, evaluateHOLFiniteState_break] at hite
      · exact Bool.eq_false_iff.mpr hc0
    rw [hnge] at hite
    simp only [Bool.false_eq_true, ↓reduceIte, evaluateHOLFiniteState_skip] at hite
    have hs_eq : s = mid := (Prod.mk.inj hite).2
    subst hs_eq
    obtain ⟨d1, hd1_pos, hd1_lt, rfl⟩ := d1_pos_of_guard_fallthrough d1w _ hdegB hnge
    exact ⟨hG, r0, r1, q, d1, hd1_pos, hd1_lt, hb_r0, hb_r1, hb_q, h01, h0q, hq1,
      hr0, hr1, hq, hd1_lk, hdegB⟩
  rw [fq12OuterBody_eq]
  have hcost_eq :
      K.«fq_poly_deg» +
        ((K.«fq_poly_deg» + 1) +
          ((K.«memzero» + 1) +
            ((K.«fq_inv» + 1) + (14 + 1) * (polyDivisionBodyCost + 1) + polyCofactorCost))) + 1 ≤
      polyOuterBodyCost := by
    simp only [polyOuterBodyCost, polyDivisionBodyCost, polyCofactorCost, polyCofactorBodyCost]
    have hmax : max (K.«fq_poly_submul» + 1) 0 = Nat.max (K.«fq_poly_submul» + 1) 0 := rfl
    rw [hmax]
    omega
  refine @bound_mono Fq12OuterInv _ _ polyOuterBodyCost hcost_eq
    (@TerminatingProgBoundedOn.decCall_on_returned Fq12OuterInv P_d1 (ofString "fq_poly_deg") K.«fq_poly_deg»
      ((K.«fq_poly_deg» + 1) + ((K.«memzero» + 1) + ((K.«fq_inv» + 1) + (14 + 1) * (polyDivisionBodyCost + 1) + polyCofactorCost)))
      fb_fq_poly_deg (fun _ h => h.guest)
      (ofString "d1") .one [.var .local (ofString "r1"), .const 13] _ hite_seq ?_)
  intro F s bpost values body callee ret' value hc hinv hargs hlk hrun
  obtain ⟨r0, r1, s0, s1, q, tmp, S0, S1,
    hr0, hr1, hs0, hs1, hq, htmp,
    hb_r0, hb_r1, _, _, hb_q, _,
    hdisj, hdist, _, _, _, _⟩ := hinv.buffers
  have hG := hinv.guest
  have hargs_d1 : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "r1"), .const 13] = some [.val (.word r1), .val (.word 13)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hr1]
  have hv : values = [.val (.word r1), .val (.word 13)] := Option.some.inj (hargs.symm.trans hargs_d1)
  subst hv
  obtain ⟨hdR1, hwR1, hmR1⟩ := domainPolynomial_of_interval s r1 hG hb_r1.1 hb_r1.2.1 hb_r1.2.2
  have hdegB := fqDegree_callee_correct s bpost r1 (polynomialMemoryCoefficients s.memory r1)
    value body callee ret' hc hb_r1.1 hwR1 hdR1 hmR1 hlk hrun
  have hm_b1 : bpost.memory = s.memory := by
    have hlk_orig : Flapjack.PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "fq_poly_deg")
        [.val (.word r1), .val (.word 13)] = some (body, callee, ret') := by
      rw [← hc]; exact hlk
    have hpure := fqDegree_function_memoryPure [.val (.word r1), .val (.word 13)] body callee ret'
      hlk_orig (callEntryStateHOLFinite s callee) hc
    rw [hrun] at hpure; exact hpure
  have hG_b1 : GuestInv bpost := by
    have := guestInv_evaluate (callEntryStateHOLFinite s callee) body (guestInv_callEntry s callee hG)
    rw [hrun] at this; exact this
  have hd1w_ex : ∃ d1w : BitVec 64, value = .val (.word d1w) := by
    rcases hdegB with ⟨he, _⟩ | ⟨j, _, he, _, _⟩
    · exact ⟨0 - 1, he⟩
    · exact ⟨BitVec.ofNat 64 j, he⟩
  obtain ⟨d1w, rfl⟩ := hd1w_ex
  let resumed := setVarHOLFinite (ofString "d1") (.val (.word d1w)) { bpost with locals := s.locals }
  have hG_res : GuestInv resumed :=
    guestInv_setVar _ _ _ (guestInv_with_locals_clock bpost s.locals bpost.clock hG_b1)
  have hkeep : ∀ nm, nm ≠ ofString "d1" → resumed.locals.lookup nm = s.locals.lookup nm := by
    intro nm hn
    simp [resumed, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hn]
  have hmem_res : resumed.memory = s.memory := hm_b1
  exact ⟨hG_res, r0, r1, q, d1w, hb_r0, hb_r1, hb_q,
    hdisj r0 r1 (by simp) (by simp) hdist.1,
    hdisj r0 q (by simp) (by simp) hdist.2.2.2.1,
    hdisj q r1 (by simp) (by simp) hdist.2.2.2.2.2.2.2.1.symm,
    (hkeep _ (by decide)).trans hr0,
    (hkeep _ (by decide)).trans hr1,
    (hkeep _ (by decide)).trans hq,
    by simp [resumed, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE],
    hmem_res ▸ hdegB⟩

private theorem fq12OuterLoop_bounded :
    TerminatingProgBoundedOn Fq12OuterInv fq12OuterLoop ((14 + 1) * (polyOuterBodyCost + 1)) := by
  have hl_eq : fq12OuterLoop = .while (.const 1) fq12OuterBody := rfl
  rw [hl_eq]
  refine @TerminatingProgBoundedOn.while_rank Fq12OuterInv (.const 1) fq12OuterBody
    polyOuterBodyCost 14 polyOuterRank
    (fun _ h => fq12OuterInv_decClock h)
    fq12OuterBody_bounded
    (fun s _ _ _ => Nat.le_trans (polyOuterRank_bound s) (by decide))
    ?_
  intro F s hc hinv _ hflow
  have hn : (evaluateHOLFiniteState (decClockHOLFinite s) fq12OuterBody).1 = none :=
    hflow.resolve_right (evaluate_noTopContinue fq12OuterBody (by decide) (decClockHOLFinite s))
  have hr : evaluateHOLFiniteState (decClockHOLFinite s) fq12OuterBody =
      (none, (evaluateHOLFiniteState (decClockHOLFinite s) fq12OuterBody).2) := Prod.ext hn rfl
  have hprog := fq12OuterBody_none_progress (decClockHOLFinite s)
    (evaluateHOLFiniteState (decClockHOLFinite s) fq12OuterBody).2
    hc (fq12OuterInv_decClock hinv) hr
  exact hprog

private def fq12PostLoopCost : Nat :=
  (K.«fq_poly_deg» + 1) + Nat.max ((K.«memzero» + 1) + (K.«heap_release» + 1)) 0 +
  (K.«fq_inv» + 1) + (12 + 1) * ((K.«fq_mul» + 1) + 1) + (K.«heap_release» + 1)

private theorem fq12PostLoop_eq :
    fq12PostLoop =
      .decCall (ofString "dz") .one (ofString "fq_poly_deg")
        [.var .local (ofString "r1"), .const 13]
        (.seq
          (.ite (.cmp .less (.var .local (ofString "dz")) (.const 0))
            (.seq (.call (some (none, none)) (ofString "memzero")
                [.var .local (ofString "d"), .const 384])
              (.seq (.call (some (none, none)) (ofString "heap_release")
                  [.var .local (ofString "mark")])
                (.return (.const 0))))
            .skip)
          (.dec (ofString "c") (.comb [.one, .one, .one, .one])
            (.load (.comb [.one, .one, .one, .one]) (.var .local (ofString "r1")))
            (.decCall (ofString "cinv") (.comb [.one, .one, .one, .one]) (ofString "fq_inv")
              [.var .local (ofString "c")]
              (.dec (ofString "i") .one (.const 0)
                (.seq
                  (.while (.cmp .lower (.var .local (ofString "i")) (.const 12))
                    (.dec (ofString "si") (.comb [.one, .one, .one, .one])
                      (.load (.comb [.one, .one, .one, .one])
                        (.op .add [.var .local (ofString "s1"),
                          .panop .mul [.var .local (ofString "i"), .const 32]]))
                      (.decCall (ofString "ri") (.comb [.one, .one, .one, .one]) (ofString "fq_mul")
                        [.var .local (ofString "si"), .var .local (ofString "cinv")]
                        (.seq
                          (.store (.op .add [.var .local (ofString "d"),
                              .panop .mul [.var .local (ofString "i"), .const 32]])
                            (.var .local (ofString "ri")))
                          (.assign .local (ofString "i")
                            (.op .add [.var .local (ofString "i"), .const 1]))))))
                  (.seq
                    (.call (some (none, none)) (ofString "heap_release")
                      [.var .local (ofString "mark")])
                    (.return (.const 0)))))))) := rfl

private theorem fq12PostLoop_bounded :
    TerminatingProgBoundedOn GuestInv fq12PostLoop fq12PostLoopCost := by
  rw [fq12PostLoop_eq]
  have hnorm_body :
      TerminatingProgBoundedOn GuestInv
        (.dec (ofString "si") (.comb [.one, .one, .one, .one])
          (.load (.comb [.one, .one, .one, .one])
            (.op .add [.var .local (ofString "s1"),
              .panop .mul [.var .local (ofString "i"), .const 32]]))
          (.decCall (ofString "ri") (.comb [.one, .one, .one, .one]) (ofString "fq_mul")
            [.var .local (ofString "si"), .var .local (ofString "cinv")]
            (.seq
              (.store (.op .add [.var .local (ofString "d"),
                  .panop .mul [.var .local (ofString "i"), .const 32]])
                (.var .local (ofString "ri")))
              (.assign .local (ofString "i")
                (.op .add [.var .local (ofString "i"), .const 1])))))
        (K.«fq_mul» + 1) := by
    refine TerminatingProgBoundedOn.dec_on localsFree_guestInv _ _ _ ?_
    exact bound_mono (B1 := K.«fq_mul» + 0 + 1) (by omega)
      (TerminatingProgBoundedOn.decCall_guestInv
        (TerminatingFunBoundedOn.of_unconditional ub_fq_mul) _ _ _
        (straight_on _ rfl))
  have hnorm_counter :
      CounterAdd (ofString "i") 1
        (.dec (ofString "si") (.comb [.one, .one, .one, .one])
          (.load (.comb [.one, .one, .one, .one])
            (.op .add [.var .local (ofString "s1"),
              .panop .mul [.var .local (ofString "i"), .const 32]]))
          (.decCall (ofString "ri") (.comb [.one, .one, .one, .one]) (ofString "fq_mul")
            [.var .local (ofString "si"), .var .local (ofString "cinv")]
            (.seq
              (.store (.op .add [.var .local (ofString "d"),
                  .panop .mul [.var .local (ofString "i"), .const 32]])
                (.var .local (ofString "ri")))
              (.assign .local (ofString "i")
                (.op .add [.var .local (ofString "i"), .const 1]))))) :=
    CounterAdd.dec (ofString "i") 1 (ofString "si") _ _ (by decide)
      (CounterAdd.decCall (ofString "i") 1 (ofString "ri") _ _ _ (by decide)
        (CounterAdd.seq (ofString "i") 1 _ (by decide) (by decide)
          (CounterAdd.assign (ofString "i") 1)))
  have hnorm_loop :
      TerminatingProgBoundedOn GuestInv
        (.while (.cmp .lower (.var .local (ofString "i")) (.const 12))
          (.dec (ofString "si") (.comb [.one, .one, .one, .one])
            (.load (.comb [.one, .one, .one, .one])
              (.op .add [.var .local (ofString "s1"),
                .panop .mul [.var .local (ofString "i"), .const 32]]))
            (.decCall (ofString "ri") (.comb [.one, .one, .one, .one]) (ofString "fq_mul")
              [.var .local (ofString "si"), .var .local (ofString "cinv")]
              (.seq
                (.store (.op .add [.var .local (ofString "d"),
                    .panop .mul [.var .local (ofString "i"), .const 32]])
                  (.var .local (ofString "ri")))
                (.assign .local (ofString "i")
                  (.op .add [.var .local (ofString "i"), .const 1]))))))
        ((12 + 1) * ((K.«fq_mul» + 1) + 1)) :=
    while_up_unsigned_const_on (ofString "i") 12 hnorm_body hnorm_counter
  have hrel_ret :
      TerminatingProgBoundedOn GuestInv
        (.seq (.call (some (none, none)) (ofString "heap_release") [.var .local (ofString "mark")])
          (.return (.const 0)))
        (K.«heap_release» + 1) :=
    bound_add_zero
      (TerminatingProgBoundedOn.seq_guestInv
        (TerminatingProgBoundedOn.call_guestInv fb_heap_release _ _)
        (straight_on _ rfl))
  have hzero_br :
      TerminatingProgBoundedOn GuestInv
        (.seq (.call (some (none, none)) (ofString "memzero") [.var .local (ofString "d"), .const 384])
          (.seq (.call (some (none, none)) (ofString "heap_release") [.var .local (ofString "mark")])
            (.return (.const 0))))
        ((K.«memzero» + 1) + (K.«heap_release» + 1)) :=
    TerminatingProgBoundedOn.seq_guestInv
      (TerminatingProgBoundedOn.call_guestInv fb_memzero _ _) hrel_ret
  have hite_br :
      TerminatingProgBoundedOn GuestInv
        (.ite (.cmp .less (.var .local (ofString "dz")) (.const 0))
          (.seq (.call (some (none, none)) (ofString "memzero") [.var .local (ofString "d"), .const 384])
            (.seq (.call (some (none, none)) (ofString "heap_release") [.var .local (ofString "mark")])
              (.return (.const 0))))
          .skip)
        (Nat.max ((K.«memzero» + 1) + (K.«heap_release» + 1)) 0) :=
    TerminatingProgBoundedOn.ite_on hzero_br (straight_on _ rfl)
  have hcinv :
      TerminatingProgBoundedOn GuestInv
        (.dec (ofString "c") (.comb [.one, .one, .one, .one])
          (.load (.comb [.one, .one, .one, .one]) (.var .local (ofString "r1")))
          (.decCall (ofString "cinv") (.comb [.one, .one, .one, .one]) (ofString "fq_inv")
            [.var .local (ofString "c")]
            (.dec (ofString "i") .one (.const 0)
              (.seq
                (.while (.cmp .lower (.var .local (ofString "i")) (.const 12))
                  (.dec (ofString "si") (.comb [.one, .one, .one, .one])
                    (.load (.comb [.one, .one, .one, .one])
                      (.op .add [.var .local (ofString "s1"),
                        .panop .mul [.var .local (ofString "i"), .const 32]]))
                    (.decCall (ofString "ri") (.comb [.one, .one, .one, .one]) (ofString "fq_mul")
                      [.var .local (ofString "si"), .var .local (ofString "cinv")]
                      (.seq
                        (.store (.op .add [.var .local (ofString "d"),
                            .panop .mul [.var .local (ofString "i"), .const 32]])
                          (.var .local (ofString "ri")))
                        (.assign .local (ofString "i")
                          (.op .add [.var .local (ofString "i"), .const 1]))))))
                (.seq
                  (.call (some (none, none)) (ofString "heap_release")
                    [.var .local (ofString "mark")])
                  (.return (.const 0)))))))
        (K.«fq_inv» + ((12 + 1) * ((K.«fq_mul» + 1) + 1) + (K.«heap_release» + 1)) + 1) :=
    TerminatingProgBoundedOn.dec_on localsFree_guestInv _ _ _
      (TerminatingProgBoundedOn.decCall_guestInv fb_fq_inv _ _ _
        (TerminatingProgBoundedOn.dec_on localsFree_guestInv _ _ _
          (TerminatingProgBoundedOn.seq_guestInv hnorm_loop hrel_ret)))
  have hcost_post :
      K.«fq_poly_deg» +
        (Nat.max ((K.«memzero» + 1) + (K.«heap_release» + 1)) 0 +
          (K.«fq_inv» + ((12 + 1) * ((K.«fq_mul» + 1) + 1) + (K.«heap_release» + 1)) + 1)) + 1 ≤
      fq12PostLoopCost := by
    dsimp only [fq12PostLoopCost]
    omega
  exact @bound_mono GuestInv _ _ fq12PostLoopCost hcost_post
    (@TerminatingProgBoundedOn.decCall_guestInv (ofString "fq_poly_deg") K.«fq_poly_deg» _
      fb_fq_poly_deg (ofString "dz") .one [.var .local (ofString "r1"), .const 13] _
      (@TerminatingProgBoundedOn.seq_guestInv _ _ _ _ hite_br hcinv))

private theorem fq12MainSeq_bounded :
    TerminatingProgBoundedOn Fq12OuterInv fq12InvMainSeq
      ((14 + 1) * (polyOuterBodyCost + 1) + fq12PostLoopCost) := by
  have hm_eq : fq12InvMainSeq = .seq fq12OuterLoop fq12PostLoop := rfl
  rw [hm_eq]
  refine @TerminatingProgBoundedOn.seq_on_none Fq12OuterInv GuestInv fq12OuterLoop fq12PostLoop
    ((14 + 1) * (polyOuterBodyCost + 1)) fq12PostLoopCost fq12OuterLoop_bounded ?_ fq12PostLoop_bounded
  intro F s mid _ hinv hr
  have := guestInv_evaluate s fq12OuterLoop hinv.guest
  rw [hr] at this
  exact this

private theorem fq12AfterAllocs_bounded :
    TerminatingProgBoundedOn AfterAllocsInv fq12InvAfterAllocs
      ((K.«memzero» + 1) + (K.«memzero» + 1) + (K.«memcpy» + 1) +
       (K.«memzero» + 1) + (K.«memzero» + 1) +
       ((14 + 1) * (polyOuterBodyCost + 1) + fq12PostLoopCost)) := by
  let P_r0ok : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
    fun s => GuestInv s ∧
      ∃ r0 r1 s0 s1 q tmp : BitVec 64,
        s.locals.lookup (ofString "r0") = some (.val (.word r0)) ∧
        s.locals.lookup (ofString "r1") = some (.val (.word r1)) ∧
        s.locals.lookup (ofString "s0") = some (.val (.word s0)) ∧
        s.locals.lookup (ofString "s1") = some (.val (.word s1)) ∧
        s.locals.lookup (ofString "q") = some (.val (.word q)) ∧
        s.locals.lookup (ofString "tmp") = some (.val (.word tmp)) ∧
        BufOk r0 ∧ BufOk r1 ∧ BufOk s0 ∧ BufOk s1 ∧ BufOk q ∧ BufOk tmp ∧
        (∀ x y, x ∈ [r0, r1, s0, s1, q, tmp] → y ∈ [r0, r1, s0, s1, q, tmp] → x ≠ y →
          PolynomialDisjoint x y) ∧
        SixDistinct r0 r1 s0 s1 q tmp
  let P_s0ok : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
    fun s => GuestInv s ∧
      ∃ r0 r1 s0 s1 q tmp : BitVec 64,
        s.locals.lookup (ofString "r0") = some (.val (.word r0)) ∧
        s.locals.lookup (ofString "r1") = some (.val (.word r1)) ∧
        s.locals.lookup (ofString "s0") = some (.val (.word s0)) ∧
        s.locals.lookup (ofString "s1") = some (.val (.word s1)) ∧
        s.locals.lookup (ofString "q") = some (.val (.word q)) ∧
        s.locals.lookup (ofString "tmp") = some (.val (.word tmp)) ∧
        BufOk r0 ∧ BufOk r1 ∧ BufOk s0 ∧ BufOk s1 ∧ BufOk q ∧ BufOk tmp ∧
        (∀ x y, x ∈ [r0, r1, s0, s1, q, tmp] → y ∈ [r0, r1, s0, s1, q, tmp] → x ≠ y →
          PolynomialDisjoint x y) ∧
        SixDistinct r0 r1 s0 s1 q tmp ∧
        MemoryPolynomial s.memory s0 (fun _ => fqZeroLimbs)
  let P_s1ok : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
    fun s => GuestInv s ∧
      ∃ r0 r1 s0 s1 q tmp : BitVec 64,
        s.locals.lookup (ofString "r0") = some (.val (.word r0)) ∧
        s.locals.lookup (ofString "r1") = some (.val (.word r1)) ∧
        s.locals.lookup (ofString "s0") = some (.val (.word s0)) ∧
        s.locals.lookup (ofString "s1") = some (.val (.word s1)) ∧
        s.locals.lookup (ofString "q") = some (.val (.word q)) ∧
        s.locals.lookup (ofString "tmp") = some (.val (.word tmp)) ∧
        BufOk r0 ∧ BufOk r1 ∧ BufOk s0 ∧ BufOk s1 ∧ BufOk q ∧ BufOk tmp ∧
        (∀ x y, x ∈ [r0, r1, s0, s1, q, tmp] → y ∈ [r0, r1, s0, s1, q, tmp] → x ≠ y →
          PolynomialDisjoint x y) ∧
        SixDistinct r0 r1 s0 s1 q tmp ∧
        MemoryPolynomial s.memory s0 (fun _ => fqZeroLimbs) ∧
        MemoryPolynomial s.memory s1 (fun _ => fqZeroLimbs)
  -- Step 9: store s1 := fqMontOne
  have hst9 : TerminatingProgBoundedOn P_s1ok
      (.seq (.store (.var .local (ofString "s1"))
          (.rstruct [.const 15230403791020821917, .const 754611498739239741,
            .const 7381016538464732716, .const 1011752739694698287]))
        fq12InvMainSeq)
      ((14 + 1) * (polyOuterBodyCost + 1) + fq12PostLoopCost) := by
    refine @seq_straight_on P_s1ok Fq12OuterInv _ _ _ rfl ?_ fq12MainSeq_bounded
    intro F s mid _ hp hst
    obtain ⟨hG, r0, r1, s0, s1, q, tmp, hr0, hr1, hs0, hs1, hq, htmp,
      hb_r0, hb_r1, hb_s0, hb_s1, hb_q, hb_tmp, hdisj, hdist, hmS0, hmS1⟩ := hp
    have hG_mid : GuestInv mid := by
      have := guestInv_evaluate s
        (.store (.var .local (ofString "s1"))
          (.rstruct [.const 15230403791020821917, .const 754611498739239741,
            .const 7381016538464732716, .const 1011752739694698287])) hG
      rw [hst] at this; exact this
    obtain ⟨_, _, hloc, _, hmem⟩ := store_rstruct4_domain_and_frame s mid
      (.var .local (ofString "s1"))
      15230403791020821917 754611498739239741 7381016538464732716 1011752739694698287 s1 hG
      (by simp [evalHOLExact, hs1]) hst
    have hs1_ca0 : s1 = coefficientAddress s1 0 := by simp [coefficientAddress]
    have hmS1_new : MemoryPolynomial mid.memory s1
        (fun i => if i = 0 then fqMontOne else fqZeroLimbs) := by
      rw [hmem]
      have hmem_eq : writeU256 s.memory s1 fqMontOne =
          writeU256 s.memory (coefficientAddress s1 0) fqMontOne := by
        rw [← hs1_ca0]
      change MemoryPolynomial (writeU256 s.memory s1 fqMontOne) s1 _
      rw [hmem_eq]
      exact writeCoefficient_polynomial s.memory s1 (fun _ => fqZeroLimbs) 0 fqMontOne (by decide) hmS1
    have hmS0_new : MemoryPolynomial mid.memory s0 (fun _ => fqZeroLimbs) := by
      rw [hmem]
      have hmem_eq : writeU256 s.memory s1 fqMontOne =
          writeU256 s.memory (coefficientAddress s1 0) fqMontOne := by
        rw [← hs1_ca0]
      change MemoryPolynomial (writeU256 s.memory s1 fqMontOne) s0 _
      rw [hmem_eq]
      exact writeCoefficient_disjoint s.memory s1 s0 (fun _ => fqZeroLimbs) 0 fqMontOne (by decide)
        (hdisj s1 s0 (by simp) (by simp) hdist.2.2.2.2.2.2.2.2.2.1.symm) hmS0
    exact ⟨hG_mid, ⟨r0, r1, s0, s1, q, tmp, fun _ => fqZeroLimbs,
      fun i => if i = 0 then fqMontOne else fqZeroLimbs,
      hloc ▸ hr0, hloc ▸ hr1, hloc ▸ hs0, hloc ▸ hs1, hloc ▸ hq, hloc ▸ htmp,
      hb_r0, hb_r1, hb_s0, hb_s1, hb_q, hb_tmp, hdisj, hdist,
      canonical_zero_poly, canonical_montOne_poly, hmS0_new, hmS1_new⟩⟩
  -- Step 8: memzero(s1, 416)
  have hst8 : TerminatingProgBoundedOn P_s0ok
      (.seq (.call (some (none, none)) (ofString "memzero") [.var .local (ofString "s1"), .const 416])
        (.seq (.store (.var .local (ofString "s1"))
            (.rstruct [.const 15230403791020821917, .const 754611498739239741,
              .const 7381016538464732716, .const 1011752739694698287]))
          fq12InvMainSeq))
      ((K.«memzero» + 1) + ((14 + 1) * (polyOuterBodyCost + 1) + fq12PostLoopCost)) := by
    refine @TerminatingProgBoundedOn.seq_on_none P_s0ok P_s1ok _ _ (K.«memzero» + 1) _
      (@bound_imp P_s0ok GuestInv _ _ (fun _ hp => hp.1) (TerminatingProgBoundedOn.call_guestInv fb_memzero _ _))
      ?_ hst9
    intro F s mid hc hp hmz
    obtain ⟨hG, r0, r1, s0, s1, q, tmp, hr0, hr1, hs0, hs1, hq, htmp,
      hb_r0, hb_r1, hb_s0, hb_s1, hb_q, hb_tmp, hdisj, hdist, hmS0⟩ := hp
    have hG_mid : GuestInv mid := by
      have := guestInv_evaluate s (.call (some (none, none)) (ofString "memzero") [.var .local (ofString "s1"), .const 416]) hG
      rw [hmz] at this; exact this
    obtain ⟨_, hwS0, _⟩ := domainPolynomial_of_interval s s0 hG hb_s0.1 hb_s0.2.1 hb_s0.2.2
    obtain ⟨_, hwS1, _⟩ := domainPolynomial_of_interval s s1 hG hb_s1.1 hb_s1.2.1 hb_s1.2.2
    obtain ⟨hef, hloc, _, hpoly⟩ := call_memzero_none s mid
      (.var .local (ofString "s1")) (.const 416) s1 416 hc hG
      (by simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hs1]) hmz
    have hmS0' : MemoryPolynomial mid.memory s0 (fun _ => fqZeroLimbs) :=
      extentFrame_preserves_polynomial hef hb_s1.1 hb_s0.1 hwS0
        (nonoverlap_of_polynomialDisjoint s1 s0 hb_s1.1 hb_s0.1 hwS1 hwS0
          (hdisj s1 s0 (by simp) (by simp) hdist.2.2.2.2.2.2.2.2.2.1.symm)) hmS0
    exact ⟨hG_mid, r0, r1, s0, s1, q, tmp,
      hloc ▸ hr0, hloc ▸ hr1, hloc ▸ hs0, hloc ▸ hs1, hloc ▸ hq, hloc ▸ htmp,
      hb_r0, hb_r1, hb_s0, hb_s1, hb_q, hb_tmp, hdisj, hdist, hmS0', hpoly hb_s1.1 rfl⟩
  -- Step 7: memzero(s0, 416)
  have hst7 : TerminatingProgBoundedOn P_r0ok
      (.seq (.call (some (none, none)) (ofString "memzero") [.var .local (ofString "s0"), .const 416])
        (.seq (.call (some (none, none)) (ofString "memzero") [.var .local (ofString "s1"), .const 416])
          (.seq (.store (.var .local (ofString "s1"))
              (.rstruct [.const 15230403791020821917, .const 754611498739239741,
                .const 7381016538464732716, .const 1011752739694698287]))
            fq12InvMainSeq)))
      ((K.«memzero» + 1) + ((K.«memzero» + 1) + ((14 + 1) * (polyOuterBodyCost + 1) + fq12PostLoopCost))) := by
    refine @TerminatingProgBoundedOn.seq_on_none P_r0ok P_s0ok _ _ (K.«memzero» + 1) _
      (@bound_imp P_r0ok GuestInv _ _ (fun _ hp => hp.1) (TerminatingProgBoundedOn.call_guestInv fb_memzero _ _))
      ?_ hst8
    intro F s mid hc hp hmz
    obtain ⟨hG, r0, r1, s0, s1, q, tmp, hr0, hr1, hs0, hs1, hq, htmp,
      hb_r0, hb_r1, hb_s0, hb_s1, hb_q, hb_tmp, hdisj, hdist⟩ := hp
    have hG_mid : GuestInv mid := by
      have := guestInv_evaluate s (.call (some (none, none)) (ofString "memzero") [.var .local (ofString "s0"), .const 416]) hG
      rw [hmz] at this; exact this
    obtain ⟨_, hloc, _, hpoly⟩ := call_memzero_none s mid
      (.var .local (ofString "s0")) (.const 416) s0 416 hc hG
      (by simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hs0]) hmz
    exact ⟨hG_mid, r0, r1, s0, s1, q, tmp,
      hloc ▸ hr0, hloc ▸ hr1, hloc ▸ hs0, hloc ▸ hs1, hloc ▸ hq, hloc ▸ htmp,
      hb_r0, hb_r1, hb_s0, hb_s1, hb_q, hb_tmp, hdisj, hdist, hpoly hb_s0.1 rfl⟩
  -- Helper: any memory-mutating program that preserves locals & GuestInv preserves P_r0ok!
  have preserve_r0ok_call : ∀ (fn : MlS) (args : List (ExpHOL 64)) (B : Nat) {rest : ProgHOL 64} {Br : Nat},
      TerminatingFunBoundedOn GuestInv fn B →
      TerminatingProgBoundedOn P_r0ok rest Br →
      TerminatingProgBoundedOn P_r0ok (.seq (.call (some (none, none)) fn args) rest) ((B + 1) + Br) := by
    intro fn args B rest Br hfn hrest
    refine @TerminatingProgBoundedOn.seq_on_none P_r0ok P_r0ok _ _ (B + 1) Br
      (@bound_imp P_r0ok GuestInv _ _ (fun _ hp => hp.1) (TerminatingProgBoundedOn.call_guestInv hfn _ _))
      ?_ hrest
    intro F s mid _ hp hr
    obtain ⟨hG, r0, r1, s0, s1, q, tmp, hr0, hr1, hs0, hs1, hq, htmp, hbs⟩ := hp
    have hG_mid : GuestInv mid := by
      have := guestInv_evaluate s (.call (some (none, none)) fn args) hG
      rw [hr] at this; exact this
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hloc⟩ := arith_call_discard_none_state hr
    exact ⟨hG_mid, r0, r1, s0, s1, q, tmp,
      hloc ▸ hr0, hloc ▸ hr1, hloc ▸ hs0, hloc ▸ hs1, hloc ▸ hq, hloc ▸ htmp, hbs⟩
  have preserve_r0ok_store : ∀ (aExp vExp : ExpHOL 64) {rest : ProgHOL 64} {Br : Nat},
      extStraightLine (.store aExp vExp) = true →
      TerminatingProgBoundedOn P_r0ok rest Br →
      TerminatingProgBoundedOn P_r0ok (.seq (.store aExp vExp) rest) Br := by
    intro aExp vExp rest Br hstr hrest
    refine @seq_straight_on P_r0ok P_r0ok _ _ Br hstr ?_ hrest
    intro F s mid _ hp hr
    obtain ⟨hG, r0, r1, s0, s1, q, tmp, hr0, hr1, hs0, hs1, hq, htmp, hbs⟩ := hp
    have hG_mid : GuestInv mid := by
      have := guestInv_evaluate s (.store aExp vExp) hG
      rw [hr] at this; exact this
    have hloc : mid.locals = s.locals := by
      rw [evaluateHOLFiniteState_store] at hr
      split at hr <;> [skip; simp at hr]
      split at hr <;> [skip; simp at hr]
      split at hr <;> simp at hr
      exact (congrArg PanSemStateFiniteExact.locals hr).symm
    exact ⟨hG_mid, r0, r1, s0, s1, q, tmp,
      hloc ▸ hr0, hloc ▸ hr1, hloc ▸ hs0, hloc ▸ hs1, hloc ▸ hq, hloc ▸ htmp, hbs⟩
  have hst2_to_6 : TerminatingProgBoundedOn P_r0ok
      (.seq (.store (.op .add [.var .local (ofString "r0"), .const 192])
          (.rstruct [.const 10102850021236865696, .const 15026249742141879542,
            .const 2169086236411634456, .const 2710440286313254821]))
        (.seq (.store (.op .add [.var .local (ofString "r0"), .const 384])
            (.rstruct [.const 15230403791020821917, .const 754611498739239741,
              .const 7381016538464732716, .const 1011752739694698287]))
          (.seq (.call (some (none, none)) (ofString "memzero") [.var .local (ofString "r1"), .const 416])
            (.seq (.call (some (none, none)) (ofString "memcpy")
                [.var .local (ofString "r1"), .var .local (ofString "a"), .const 384])
              (.seq (.call (some (none, none)) (ofString "memzero") [.var .local (ofString "s0"), .const 416])
                (.seq (.call (some (none, none)) (ofString "memzero") [.var .local (ofString "s1"), .const 416])
                  (.seq (.store (.var .local (ofString "s1"))
                      (.rstruct [.const 15230403791020821917, .const 754611498739239741,
                        .const 7381016538464732716, .const 1011752739694698287]))
                    fq12InvMainSeq)))))))
      ((K.«memzero» + 1) + ((K.«memcpy» + 1) +
        ((K.«memzero» + 1) + ((K.«memzero» + 1) +
          ((14 + 1) * (polyOuterBodyCost + 1) + fq12PostLoopCost))))) :=
    preserve_r0ok_store
      (.op .add [.var .local (ofString "r0"), .const 192])
      (.rstruct [.const 10102850021236865696, .const 15026249742141879542,
        .const 2169086236411634456, .const 2710440286313254821]) rfl
      (preserve_r0ok_store
        (.op .add [.var .local (ofString "r0"), .const 384])
        (.rstruct [.const 15230403791020821917, .const 754611498739239741,
          .const 7381016538464732716, .const 1011752739694698287]) rfl
        (preserve_r0ok_call (ofString "memzero") [.var .local (ofString "r1"), .const 416] K.«memzero» fb_memzero
          (preserve_r0ok_call (ofString "memcpy")
            [.var .local (ofString "r1"), .var .local (ofString "a"), .const 384] K.«memcpy» fb_memcpy hst7)))
  -- Steps 1 + 2: memzero(r0, 416) establishes sourceBase ≤ r0 ∧ r0 + 416 ≤ heapEnd,
  -- and store(r0, ...) establishes r0 % 8 = 0!
  let P_r0dom : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
    fun s => GuestInv s ∧
      ∃ r0 r1 s0 s1 q tmp q5 : BitVec 64,
        s.locals.lookup (ofString "r0") = some (.val (.word r0)) ∧
        s.locals.lookup (ofString "r1") = some (.val (.word r1)) ∧
        s.locals.lookup (ofString "s0") = some (.val (.word s0)) ∧
        s.locals.lookup (ofString "s1") = some (.val (.word s1)) ∧
        s.locals.lookup (ofString "q") = some (.val (.word q)) ∧
        s.locals.lookup (ofString "tmp") = some (.val (.word tmp)) ∧
        sourceBase ≤ r0.toNat ∧ r0.toNat + 416 ≤ heapEnd ∧
        (r0.toNat + 423 < 2 ^ 64 → r0.toNat + 416 ≤ r1.toNat ∧ r1.toNat % 8 = 0) ∧
        r1.toNat ≤ heapLimit ∧
        r1.toNat + 416 ≤ s0.toNat ∧ s0.toNat % 8 = 0 ∧
        s0.toNat + 416 ≤ s1.toNat ∧ s1.toNat % 8 = 0 ∧
        s1.toNat + 416 ≤ q.toNat ∧ q.toNat % 8 = 0 ∧
        q.toNat + 416 ≤ tmp.toNat ∧ tmp.toNat % 8 = 0 ∧
        tmp.toNat + 416 ≤ q5.toNat ∧ q5.toNat ≤ heapLimit
  have hst2 : TerminatingProgBoundedOn P_r0dom
      (.seq (.store (.var .local (ofString "r0"))
          (.rstruct [.const 5544790254283102953, .const 13698472384431417117,
            .const 4628036095437277618, .const 2762764518496934255]))
        (.seq (.store (.op .add [.var .local (ofString "r0"), .const 192])
            (.rstruct [.const 10102850021236865696, .const 15026249742141879542,
              .const 2169086236411634456, .const 2710440286313254821]))
          (.seq (.store (.op .add [.var .local (ofString "r0"), .const 384])
              (.rstruct [.const 15230403791020821917, .const 754611498739239741,
                .const 7381016538464732716, .const 1011752739694698287]))
            (.seq (.call (some (none, none)) (ofString "memzero") [.var .local (ofString "r1"), .const 416])
              (.seq (.call (some (none, none)) (ofString "memcpy")
                  [.var .local (ofString "r1"), .var .local (ofString "a"), .const 384])
                (.seq (.call (some (none, none)) (ofString "memzero") [.var .local (ofString "s0"), .const 416])
                  (.seq (.call (some (none, none)) (ofString "memzero") [.var .local (ofString "s1"), .const 416])
                    (.seq (.store (.var .local (ofString "s1"))
                        (.rstruct [.const 15230403791020821917, .const 754611498739239741,
                          .const 7381016538464732716, .const 1011752739694698287]))
                      fq12InvMainSeq))))))))
      ((K.«memzero» + 1) + ((K.«memcpy» + 1) +
        ((K.«memzero» + 1) + ((K.«memzero» + 1) +
          ((14 + 1) * (polyOuterBodyCost + 1) + fq12PostLoopCost))))) := by
    refine @seq_straight_on P_r0dom P_r0ok _ _ _ rfl ?_ hst2_to_6
    intro F s mid _ hp hst
    obtain ⟨hG, r0, r1, s0, s1, q, tmp, q5, hr0, hr1, hs0, hs1, hq, htmp,
      hr0_lo, hr0_hi, hr01_imp, hr1_lim, h12, hal2, h23, hal3, h34, hal4, h45, hal5, h5q, hq5_lim⟩ := hp
    have hG_mid : GuestInv mid := by
      have := guestInv_evaluate s
        (.store (.var .local (ofString "r0"))
          (.rstruct [.const 5544790254283102953, .const 13698472384431417117,
            .const 4628036095437277618, .const 2762764518496934255])) hG
      rw [hst] at this; exact this
    obtain ⟨hal0, _, hloc, _, _⟩ := store_rstruct4_domain_and_frame s mid
      (.var .local (ofString "r0"))
      5544790254283102953 13698472384431417117 4628036095437277618 2762764518496934255 r0 hG
      (by simp [evalHOLExact, hr0]) hst
    have hconsts : heapEnd = 33806089704 ∧ heapLimit = 2952790016 := ⟨by decide, rfl⟩
    have hr0_423 : r0.toNat + 423 < 2 ^ 64 := by rw [hconsts.1] at hr0_hi; omega
    obtain ⟨h01, hal1⟩ := hr01_imp hr0_423
    have h5e : tmp.toNat + 416 ≤ heapEnd := by rw [hconsts.2] at hq5_lim; rw [hconsts.1]; omega
    obtain ⟨hdisj, hdist⟩ := pairwise_disjoint_of_chain r0 r1 s0 s1 q tmp h01 h12 h23 h34 h45 h5e
    exact ⟨hG_mid, r0, r1, s0, s1, q, tmp,
      hloc ▸ hr0, hloc ▸ hr1, hloc ▸ hs0, hloc ▸ hs1, hloc ▸ hq, hloc ▸ htmp,
      ⟨hal0, hr0_lo, hr0_hi⟩,
      ⟨hal1, by omega, by omega⟩,
      ⟨hal2, by omega, by omega⟩,
      ⟨hal3, by omega, by omega⟩,
      ⟨hal4, by omega, by omega⟩,
      ⟨hal5, by omega, h5e⟩,
      hdisj, hdist⟩
  rw [fq12AfterAllocs_eq]
  have hcost_after :
      (K.«memzero» + 1) +
        ((K.«memzero» + 1) + ((K.«memcpy» + 1) +
          ((K.«memzero» + 1) + ((K.«memzero» + 1) +
            ((14 + 1) * (polyOuterBodyCost + 1) + fq12PostLoopCost))))) ≤
      (K.«memzero» + 1) + (K.«memzero» + 1) + (K.«memcpy» + 1) +
        (K.«memzero» + 1) + (K.«memzero» + 1) +
        ((14 + 1) * (polyOuterBodyCost + 1) + fq12PostLoopCost) := by omega
  refine @bound_mono AfterAllocsInv _ _ _ hcost_after
    (@TerminatingProgBoundedOn.seq_on_none AfterAllocsInv P_r0dom _ _ (K.«memzero» + 1) _
      (@bound_imp AfterAllocsInv GuestInv _ _ (fun _ hp => hp.1)
        (TerminatingProgBoundedOn.call_guestInv fb_memzero none [.var .local (ofString "r0"), .const 416]))
      ?_ hst2)
  intro F s mid hc hp hmz
  obtain ⟨hG, r0, r1, s0, s1, q, tmp, q5, hr0, hr1, hs0, hs1, hq, htmp, hrest⟩ := hp
  have hG_mid : GuestInv mid := by
    have := guestInv_evaluate s (.call (some (none, none)) (ofString "memzero") [.var .local (ofString "r0"), .const 416]) hG
    rw [hmz] at this; exact this
  obtain ⟨_, hloc, hdom, _⟩ := call_memzero_none s mid
    (.var .local (ofString "r0")) (.const 416) r0 416 hc hG
    (by simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hr0]) hmz
  obtain ⟨hr0_lo, hr0_hi⟩ := hdom (by decide)
  exact ⟨hG_mid, r0, r1, s0, s1, q, tmp, q5,
    hloc ▸ hr0, hloc ▸ hr1, hloc ▸ hs0, hloc ▸ hs1, hloc ▸ hq, hloc ▸ htmp,
    hr0_lo, hr0_hi, hrest⟩

private theorem fq12Body_eq :
    fq12InvBody =
      .decCall (ofString "mark") .one (ofString "heap_mark") []
        (.decCall (ofString "r0") .one (ofString "alloc") [.const 416]
          (.decCall (ofString "r1") .one (ofString "alloc") [.const 416]
            (.decCall (ofString "s0") .one (ofString "alloc") [.const 416]
              (.decCall (ofString "s1") .one (ofString "alloc") [.const 416]
                (.decCall (ofString "q") .one (ofString "alloc") [.const 416]
                  (.decCall (ofString "tmp") .one (ofString "alloc") [.const 416]
                    fq12InvAfterAllocs)))))) := rfl

private theorem fq12Body_bounded :
    TerminatingProgBoundedOn GuestInv fq12InvBody K.«fq12_inv» := by
  let AfterAllocsCost : Nat :=
    (K.«memzero» + 1) + (K.«memzero» + 1) + (K.«memcpy» + 1) +
    (K.«memzero» + 1) + (K.«memzero» + 1) +
    ((14 + 1) * (polyOuterBodyCost + 1) + fq12PostLoopCost)
  let A1 : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
    fun s => GuestInv s ∧
      ∃ r0 q0 : BitVec 64,
        s.locals.lookup (ofString "r0") = some (.val (.word r0)) ∧
        s.globals.lookup (ofString "heap_ptr") = some (.val (.word q0)) ∧
        (r0.toNat + 423 < 2 ^ 64 → r0.toNat + 416 ≤ q0.toNat ∧ q0.toNat % 8 = 0) ∧
        q0.toNat ≤ heapLimit
  let A2 : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
    fun s => GuestInv s ∧
      ∃ r0 r1 q1 : BitVec 64,
        s.locals.lookup (ofString "r0") = some (.val (.word r0)) ∧
        s.locals.lookup (ofString "r1") = some (.val (.word r1)) ∧
        s.globals.lookup (ofString "heap_ptr") = some (.val (.word q1)) ∧
        (r0.toNat + 423 < 2 ^ 64 → r0.toNat + 416 ≤ r1.toNat ∧ r1.toNat % 8 = 0) ∧
        r1.toNat ≤ heapLimit ∧
        r1.toNat + 416 ≤ q1.toNat ∧ q1.toNat % 8 = 0 ∧ q1.toNat ≤ heapLimit
  let A3 : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
    fun s => GuestInv s ∧
      ∃ r0 r1 s0 q2 : BitVec 64,
        s.locals.lookup (ofString "r0") = some (.val (.word r0)) ∧
        s.locals.lookup (ofString "r1") = some (.val (.word r1)) ∧
        s.locals.lookup (ofString "s0") = some (.val (.word s0)) ∧
        s.globals.lookup (ofString "heap_ptr") = some (.val (.word q2)) ∧
        (r0.toNat + 423 < 2 ^ 64 → r0.toNat + 416 ≤ r1.toNat ∧ r1.toNat % 8 = 0) ∧
        r1.toNat ≤ heapLimit ∧
        r1.toNat + 416 ≤ s0.toNat ∧ s0.toNat % 8 = 0 ∧
        s0.toNat + 416 ≤ q2.toNat ∧ q2.toNat % 8 = 0 ∧ q2.toNat ≤ heapLimit
  let A4 : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
    fun s => GuestInv s ∧
      ∃ r0 r1 s0 s1 q3 : BitVec 64,
        s.locals.lookup (ofString "r0") = some (.val (.word r0)) ∧
        s.locals.lookup (ofString "r1") = some (.val (.word r1)) ∧
        s.locals.lookup (ofString "s0") = some (.val (.word s0)) ∧
        s.locals.lookup (ofString "s1") = some (.val (.word s1)) ∧
        s.globals.lookup (ofString "heap_ptr") = some (.val (.word q3)) ∧
        (r0.toNat + 423 < 2 ^ 64 → r0.toNat + 416 ≤ r1.toNat ∧ r1.toNat % 8 = 0) ∧
        r1.toNat ≤ heapLimit ∧
        r1.toNat + 416 ≤ s0.toNat ∧ s0.toNat % 8 = 0 ∧
        s0.toNat + 416 ≤ s1.toNat ∧ s1.toNat % 8 = 0 ∧
        s1.toNat + 416 ≤ q3.toNat ∧ q3.toNat % 8 = 0 ∧ q3.toNat ≤ heapLimit
  let A5 : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
    fun s => GuestInv s ∧
      ∃ r0 r1 s0 s1 q q4 : BitVec 64,
        s.locals.lookup (ofString "r0") = some (.val (.word r0)) ∧
        s.locals.lookup (ofString "r1") = some (.val (.word r1)) ∧
        s.locals.lookup (ofString "s0") = some (.val (.word s0)) ∧
        s.locals.lookup (ofString "s1") = some (.val (.word s1)) ∧
        s.locals.lookup (ofString "q") = some (.val (.word q)) ∧
        s.globals.lookup (ofString "heap_ptr") = some (.val (.word q4)) ∧
        (r0.toNat + 423 < 2 ^ 64 → r0.toNat + 416 ≤ r1.toNat ∧ r1.toNat % 8 = 0) ∧
        r1.toNat ≤ heapLimit ∧
        r1.toNat + 416 ≤ s0.toNat ∧ s0.toNat % 8 = 0 ∧
        s0.toNat + 416 ≤ s1.toNat ∧ s1.toNat % 8 = 0 ∧
        s1.toNat + 416 ≤ q.toNat ∧ q.toNat % 8 = 0 ∧
        q.toNat + 416 ≤ q4.toNat ∧ q4.toNat % 8 = 0 ∧ q4.toNat ≤ heapLimit
  have hlim423 : ∀ p : BitVec 64, p.toNat ≤ heapLimit → p.toNat + 423 < 2 ^ 64 := by
    intro p hp; have hconst : heapLimit = 2952790016 := rfl; rw [hconst] at hp; omega
  have ha6 : TerminatingProgBoundedOn A5
      (.decCall (ofString "tmp") .one (ofString "alloc") [.const 416] fq12InvAfterAllocs)
      (K.«alloc» + AfterAllocsCost + 1) := by
    refine @TerminatingProgBoundedOn.decCall_on_returned A5 AfterAllocsInv
      (ofString "alloc") K.«alloc» AfterAllocsCost fb_alloc (fun _ hp => hp.1)
      (ofString "tmp") .one [.const 416] _ fq12AfterAllocs_bounded ?_
    intro F s bpost values body callee ret' value hc hp hargs hlk hrun
    obtain ⟨hG, r0, r1, s0, s1, q, q4, hr0, hr1, hs0, hs1, hq, hhp,
      hr01, hr1_lim, h12, hal2, h23, hal3, h34, hal4, h45, hal5, hq4_lim⟩ := hp
    obtain ⟨p5, q5, rfl, hp5_g, _, _, hq5_lim, hp5_imp⟩ :=
      alloc416_lookup_callee s bpost values body callee ret' value hc hargs hlk hrun
    have hp5_eq : p5 = q4 := by
      have := Option.some.inj (hp5_g.symm.trans hhp)
      simpa only [ValueHOL.val.injEq, HolWordLab.word.injEq] using this
    subst hp5_eq
    obtain ⟨h5q, _⟩ := hp5_imp (hlim423 p5 hq4_lim)
    have hG_b : GuestInv bpost := by
      have := guestInv_evaluate (callEntryStateHOLFinite s callee) body (guestInv_callEntry s callee hG)
      rw [hrun] at this; exact this
    let resumed := setVarHOLFinite (ofString "tmp") (.val (.word p5)) { bpost with locals := s.locals }
    have hG_res : GuestInv resumed :=
      guestInv_setVar _ _ _ (guestInv_with_locals_clock bpost s.locals bpost.clock hG_b)
    have hkeep : ∀ nm, nm ≠ ofString "tmp" → resumed.locals.lookup nm = s.locals.lookup nm := by
      intro nm hn; simp [resumed, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hn]
    exact ⟨hG_res, r0, r1, s0, s1, q, p5, q5,
      (hkeep _ (by decide)).trans hr0,
      (hkeep _ (by decide)).trans hr1,
      (hkeep _ (by decide)).trans hs0,
      (hkeep _ (by decide)).trans hs1,
      (hkeep _ (by decide)).trans hq,
      by simp [resumed, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE],
      hr01, hr1_lim, h12, hal2, h23, hal3, h34, hal4, h45, hal5, h5q, hq5_lim⟩
  have ha5 : TerminatingProgBoundedOn A4
      (.decCall (ofString "q") .one (ofString "alloc") [.const 416]
        (.decCall (ofString "tmp") .one (ofString "alloc") [.const 416] fq12InvAfterAllocs))
      (K.«alloc» + (K.«alloc» + AfterAllocsCost + 1) + 1) := by
    refine @TerminatingProgBoundedOn.decCall_on_returned A4 A5
      (ofString "alloc") K.«alloc» _ fb_alloc (fun _ hp => hp.1)
      (ofString "q") .one [.const 416] _ ha6 ?_
    intro F s bpost values body callee ret' value hc hp hargs hlk hrun
    obtain ⟨hG, r0, r1, s0, s1, q3, hr0, hr1, hs0, hs1, hhp,
      hr01, hr1_lim, h12, hal2, h23, hal3, h34, hal4, hq3_lim⟩ := hp
    obtain ⟨p4, q4, rfl, hp4_g, hq4_g, _, hq4_lim, hp4_imp⟩ :=
      alloc416_lookup_callee s bpost values body callee ret' value hc hargs hlk hrun
    have hp4_eq : p4 = q3 := by
      have := Option.some.inj (hp4_g.symm.trans hhp)
      simpa only [ValueHOL.val.injEq, HolWordLab.word.injEq] using this
    subst hp4_eq
    obtain ⟨h45, hal5⟩ := hp4_imp (hlim423 p4 hq3_lim)
    have hG_b : GuestInv bpost := by
      have := guestInv_evaluate (callEntryStateHOLFinite s callee) body (guestInv_callEntry s callee hG)
      rw [hrun] at this; exact this
    let resumed := setVarHOLFinite (ofString "q") (.val (.word p4)) { bpost with locals := s.locals }
    have hG_res : GuestInv resumed :=
      guestInv_setVar _ _ _ (guestInv_with_locals_clock bpost s.locals bpost.clock hG_b)
    have hkeep : ∀ nm, nm ≠ ofString "q" → resumed.locals.lookup nm = s.locals.lookup nm := by
      intro nm hn; simp [resumed, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hn]
    exact ⟨hG_res, r0, r1, s0, s1, p4, q4,
      (hkeep _ (by decide)).trans hr0,
      (hkeep _ (by decide)).trans hr1,
      (hkeep _ (by decide)).trans hs0,
      (hkeep _ (by decide)).trans hs1,
      by simp [resumed, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE],
      hq4_g, hr01, hr1_lim, h12, hal2, h23, hal3, h34, hal4, h45, hal5, hq4_lim⟩
  have ha4 : TerminatingProgBoundedOn A3
      (.decCall (ofString "s1") .one (ofString "alloc") [.const 416]
        (.decCall (ofString "q") .one (ofString "alloc") [.const 416]
          (.decCall (ofString "tmp") .one (ofString "alloc") [.const 416] fq12InvAfterAllocs)))
      (K.«alloc» + (K.«alloc» + (K.«alloc» + AfterAllocsCost + 1) + 1) + 1) := by
    refine @TerminatingProgBoundedOn.decCall_on_returned A3 A4
      (ofString "alloc") K.«alloc» _ fb_alloc (fun _ hp => hp.1)
      (ofString "s1") .one [.const 416] _ ha5 ?_
    intro F s bpost values body callee ret' value hc hp hargs hlk hrun
    obtain ⟨hG, r0, r1, s0, q2, hr0, hr1, hs0, hhp,
      hr01, hr1_lim, h12, hal2, h23, hal3, hq2_lim⟩ := hp
    obtain ⟨p3, q3, rfl, hp3_g, hq3_g, _, hq3_lim, hp3_imp⟩ :=
      alloc416_lookup_callee s bpost values body callee ret' value hc hargs hlk hrun
    have hp3_eq : p3 = q2 := by
      have := Option.some.inj (hp3_g.symm.trans hhp)
      simpa only [ValueHOL.val.injEq, HolWordLab.word.injEq] using this
    subst hp3_eq
    obtain ⟨h34, hal4⟩ := hp3_imp (hlim423 p3 hq2_lim)
    have hG_b : GuestInv bpost := by
      have := guestInv_evaluate (callEntryStateHOLFinite s callee) body (guestInv_callEntry s callee hG)
      rw [hrun] at this; exact this
    let resumed := setVarHOLFinite (ofString "s1") (.val (.word p3)) { bpost with locals := s.locals }
    have hG_res : GuestInv resumed :=
      guestInv_setVar _ _ _ (guestInv_with_locals_clock bpost s.locals bpost.clock hG_b)
    have hkeep : ∀ nm, nm ≠ ofString "s1" → resumed.locals.lookup nm = s.locals.lookup nm := by
      intro nm hn; simp [resumed, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hn]
    exact ⟨hG_res, r0, r1, s0, p3, q3,
      (hkeep _ (by decide)).trans hr0,
      (hkeep _ (by decide)).trans hr1,
      (hkeep _ (by decide)).trans hs0,
      by simp [resumed, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE],
      hq3_g, hr01, hr1_lim, h12, hal2, h23, hal3, h34, hal4, hq3_lim⟩
  have ha3 : TerminatingProgBoundedOn A2
      (.decCall (ofString "s0") .one (ofString "alloc") [.const 416]
        (.decCall (ofString "s1") .one (ofString "alloc") [.const 416]
          (.decCall (ofString "q") .one (ofString "alloc") [.const 416]
            (.decCall (ofString "tmp") .one (ofString "alloc") [.const 416] fq12InvAfterAllocs))))
      (K.«alloc» + (K.«alloc» + (K.«alloc» + (K.«alloc» + AfterAllocsCost + 1) + 1) + 1) + 1) := by
    refine @TerminatingProgBoundedOn.decCall_on_returned A2 A3
      (ofString "alloc") K.«alloc» _ fb_alloc (fun _ hp => hp.1)
      (ofString "s0") .one [.const 416] _ ha4 ?_
    intro F s bpost values body callee ret' value hc hp hargs hlk hrun
    obtain ⟨hG, r0, r1, q1, hr0, hr1, hhp, hr01, hr1_lim, h12, hal2, hq1_lim⟩ := hp
    obtain ⟨p2, q2, rfl, hp2_g, hq2_g, _, hq2_lim, hp2_imp⟩ :=
      alloc416_lookup_callee s bpost values body callee ret' value hc hargs hlk hrun
    have hp2_eq : p2 = q1 := by
      have := Option.some.inj (hp2_g.symm.trans hhp)
      simpa only [ValueHOL.val.injEq, HolWordLab.word.injEq] using this
    subst hp2_eq
    obtain ⟨h23, hal3⟩ := hp2_imp (hlim423 p2 hq1_lim)
    have hG_b : GuestInv bpost := by
      have := guestInv_evaluate (callEntryStateHOLFinite s callee) body (guestInv_callEntry s callee hG)
      rw [hrun] at this; exact this
    let resumed := setVarHOLFinite (ofString "s0") (.val (.word p2)) { bpost with locals := s.locals }
    have hG_res : GuestInv resumed :=
      guestInv_setVar _ _ _ (guestInv_with_locals_clock bpost s.locals bpost.clock hG_b)
    have hkeep : ∀ nm, nm ≠ ofString "s0" → resumed.locals.lookup nm = s.locals.lookup nm := by
      intro nm hn; simp [resumed, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hn]
    exact ⟨hG_res, r0, r1, p2, q2,
      (hkeep _ (by decide)).trans hr0,
      (hkeep _ (by decide)).trans hr1,
      by simp [resumed, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE],
      hq2_g, hr01, hr1_lim, h12, hal2, h23, hal3, hq2_lim⟩
  have ha2 : TerminatingProgBoundedOn A1
      (.decCall (ofString "r1") .one (ofString "alloc") [.const 416]
        (.decCall (ofString "s0") .one (ofString "alloc") [.const 416]
          (.decCall (ofString "s1") .one (ofString "alloc") [.const 416]
            (.decCall (ofString "q") .one (ofString "alloc") [.const 416]
              (.decCall (ofString "tmp") .one (ofString "alloc") [.const 416] fq12InvAfterAllocs)))))
      (K.«alloc» + (K.«alloc» + (K.«alloc» + (K.«alloc» + (K.«alloc» + AfterAllocsCost + 1) + 1) + 1) + 1) + 1) := by
    refine @TerminatingProgBoundedOn.decCall_on_returned A1 A2
      (ofString "alloc") K.«alloc» _ fb_alloc (fun _ hp => hp.1)
      (ofString "r1") .one [.const 416] _ ha3 ?_
    intro F s bpost values body callee ret' value hc hp hargs hlk hrun
    obtain ⟨hG, r0, q0, hr0, hhp, hr01, hq0_lim⟩ := hp
    obtain ⟨p1, q1, rfl, hp1_g, hq1_g, _, hq1_lim, hp1_imp⟩ :=
      alloc416_lookup_callee s bpost values body callee ret' value hc hargs hlk hrun
    have hp1_eq : p1 = q0 := by
      have := Option.some.inj (hp1_g.symm.trans hhp)
      simpa only [ValueHOL.val.injEq, HolWordLab.word.injEq] using this
    subst hp1_eq
    obtain ⟨h12, hal2⟩ := hp1_imp (hlim423 p1 hq0_lim)
    have hG_b : GuestInv bpost := by
      have := guestInv_evaluate (callEntryStateHOLFinite s callee) body (guestInv_callEntry s callee hG)
      rw [hrun] at this; exact this
    let resumed := setVarHOLFinite (ofString "r1") (.val (.word p1)) { bpost with locals := s.locals }
    have hG_res : GuestInv resumed :=
      guestInv_setVar _ _ _ (guestInv_with_locals_clock bpost s.locals bpost.clock hG_b)
    have hkeep : ∀ nm, nm ≠ ofString "r1" → resumed.locals.lookup nm = s.locals.lookup nm := by
      intro nm hn; simp [resumed, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hn]
    exact ⟨hG_res, r0, p1, q1,
      (hkeep _ (by decide)).trans hr0,
      by simp [resumed, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE],
      hq1_g, hr01, hq0_lim, h12, hal2, hq1_lim⟩
  have ha1 : TerminatingProgBoundedOn GuestInv
      (.decCall (ofString "r0") .one (ofString "alloc") [.const 416]
        (.decCall (ofString "r1") .one (ofString "alloc") [.const 416]
          (.decCall (ofString "s0") .one (ofString "alloc") [.const 416]
            (.decCall (ofString "s1") .one (ofString "alloc") [.const 416]
              (.decCall (ofString "q") .one (ofString "alloc") [.const 416]
                (.decCall (ofString "tmp") .one (ofString "alloc") [.const 416] fq12InvAfterAllocs))))))
      (K.«alloc» + (K.«alloc» + (K.«alloc» + (K.«alloc» + (K.«alloc» + (K.«alloc» + AfterAllocsCost + 1) + 1) + 1) + 1) + 1) + 1) := by
    refine @TerminatingProgBoundedOn.decCall_on_returned GuestInv A1
      (ofString "alloc") K.«alloc» _ fb_alloc (fun _ hp => hp)
      (ofString "r0") .one [.const 416] _ ha2 ?_
    intro F s bpost values body callee ret' value hc hG hargs hlk hrun
    obtain ⟨r0, q0, rfl, _, hq0_g, _, hq0_lim, hr01⟩ :=
      alloc416_lookup_callee s bpost values body callee ret' value hc hargs hlk hrun
    have hG_b : GuestInv bpost := by
      have := guestInv_evaluate (callEntryStateHOLFinite s callee) body (guestInv_callEntry s callee hG)
      rw [hrun] at this; exact this
    let resumed := setVarHOLFinite (ofString "r0") (.val (.word r0)) { bpost with locals := s.locals }
    have hG_res : GuestInv resumed :=
      guestInv_setVar _ _ _ (guestInv_with_locals_clock bpost s.locals bpost.clock hG_b)
    exact ⟨hG_res, r0, q0,
      by simp [resumed, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE],
      hq0_g, hr01, hq0_lim⟩
  rw [fq12Body_eq]
  have hcost_top :
      K.«heap_mark» +
        (K.«alloc» + (K.«alloc» + (K.«alloc» + (K.«alloc» + (K.«alloc» + (K.«alloc» + AfterAllocsCost + 1) + 1) + 1) + 1) + 1) + 1) + 1 ≤
      K.«fq12_inv» := by
    dsimp only [AfterAllocsCost, fq12PostLoopCost, polyOuterBodyCost]
    unfold K.«fq12_inv»
    omega
  exact @bound_mono GuestInv _ _ K.«fq12_inv» hcost_top
    (@TerminatingProgBoundedOn.decCall_guestInv (ofString "heap_mark") K.«heap_mark» _
      fb_heap_mark (ofString "mark") .one [] _ ha1)

theorem fb_fq12_inv :
    TerminatingFunBoundedOn GuestInv (ofString "fq12_inv") K.«fq12_inv» := by
  refine ⟨_, _, _, lookup_of_guestAst_getElem 682 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_fq12_inv) rfl, ?_⟩
  exact fq12Body_bounded

end InitECandidate.Solver.Wave8GuestInv.R16Bn254
